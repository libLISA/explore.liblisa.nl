use std::collections::HashMap;
use std::io::Cursor;

use hex::FromHexError;
use itertools::Itertools;
use liblisa::Instruction;
use liblisa::arch::Scope;
use liblisa::arch::x64::{PrefixScope, X64Arch};
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa_wasm_shared::group::DataGroup;
use liblisa_wasm_shared::{EncodingResolver, EncodingWithArchitectureMap};
use log::{Level, debug, error, info};
use search::ReturnStatus;
use tokio::sync::{Mutex, RwLock};
use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::JsFuture;
use wasm_bindgen_futures::js_sys::Uint8Array;
use web_sys::{Request, RequestInit, RequestMode, Response};

use crate::encoding::WasmEncoding;
use crate::search::{FetchStatusCode, LookupResult, SearchResult, SearchResultEntry};

pub mod codegen;
pub mod encoding;
pub mod search;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console, js_name = log)]
    fn log_obj(s: &JsValue);

    #[wasm_bindgen(js_name = Blob)]
    type Blob;

    #[wasm_bindgen(method, js_class = "Blob", js_name = "arrayBuffer")]
    async fn as_array_buffer(this: &Blob) -> JsValue;
}

#[wasm_bindgen(start)]
fn run() {
    console_log::init_with_level(Level::Trace).unwrap();
    std::panic::set_hook(Box::new(console_error_panic_hook::hook));
}

// #[derive(serde::Serialize)]
// pub struct WasmEncoding {
//     instr: Vec<u8>,
// }

#[wasm_bindgen]
pub struct EncodingFetcher {
    base_url: String,
    resolver: RwLock<EncodingResolver>,
    resolver_is_loaded: RwLock<bool>,
    loaded: Mutex<HashMap<DataGroup, Vec<EncodingWithArchitectureMap<X64Arch, SynthesizedComputation>>>>,
}

#[wasm_bindgen]
pub struct ArchitectureNames {
    names: Vec<String>,
}

#[wasm_bindgen]
impl ArchitectureNames {
    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, index: usize) -> String {
        self.names[index].clone()
    }
}

#[wasm_bindgen]
impl EncodingFetcher {
    #[wasm_bindgen(constructor)]
    pub fn new(base_url: String) -> Self {
        info!("Creating EncodingFetcher with base_url={base_url:?}");
        EncodingFetcher {
            base_url,
            resolver: RwLock::new(EncodingResolver::default()),
            loaded: Mutex::new(HashMap::new()),
            resolver_is_loaded: RwLock::new(false),
        }
    }

    #[wasm_bindgen]
    pub async fn load_index(&self) -> Result<bool, JsValue> {
        if !*self.resolver_is_loaded.read().await {
            let mut w = self.resolver.write().await;
            let data = self.load("slices.index").await?;
            *self.resolver_is_loaded.write().await = true;
            *w = EncodingResolver::from_bytes(&data);
            info!("Loaded and unpacked the index!");
        }

        Ok(true)
    }

    #[wasm_bindgen]
    pub async fn architectures(&self) -> String {
        serde_json::to_string(self.resolver.read().await.architecture_names()).unwrap()
    }

    fn parse_instr(mut instr: String) -> Result<(usize, Instruction), ReturnStatus> {
        use FetchStatusCode::*;

        debug!("Fetching encoding for {instr:?}");
        let original_instr_bits = instr.len() * 4;
        if instr.len() % 2 == 1 {
            instr.push('0');
        }

        let bytes = match hex::decode(instr) {
            Ok(bytes) => bytes,
            Err(e) => {
                return Err(match e {
                    FromHexError::InvalidHexCharacter {
                        ..
                    } => ReturnStatus::from_status(InvalidHex),
                    _ => unreachable!(),
                })
            },
        };

        let instr = Instruction::new(&bytes);
        debug!("Decoded instruction: {instr:?}");
        if bytes.is_empty() || bytes.len() >= 15 {
            return Err(ReturnStatus::from_status(NotFound))
        }

        Ok((original_instr_bits, instr))
    }

    async fn load_results_matching(
        &self, instr: Instruction, original_instr_bits: usize,
    ) -> Result<Vec<EncodingWithArchitectureMap<X64Arch, SynthesizedComputation>>, ReturnStatus> {
        use FetchStatusCode::*;

        let scope = PrefixScope;
        if original_instr_bits % 8 == 0 && !scope.is_instr_in_scope(instr.bytes()) {
            return Err(ReturnStatus::from_status(OutOfScope))
        }

        if instr.byte_len() == 0 {
            return Err(ReturnStatus::from_status(InvalidHex))
        }

        debug!("Performing lookup...");
        let data_groups = self.resolver.read().await.lookup(&instr, original_instr_bits);
        if data_groups.is_empty() {
            return Err(ReturnStatus::from_status(NotFound))
        }

        let mut loaded = self.loaded.lock().await;
        let mut matching = Vec::new();
        for data_group in data_groups.iter() {
            let hash = data_group.murmur().as_hex();

            if !loaded.contains_key(data_group) {
                let data = match self.load(&format!("{}/{}.slice", &hash[..2], &hash[2..])).await {
                    Ok(data) => data,
                    Err(e) => return Err(ReturnStatus::from_js_error(NetworkError, e)),
                };

                let mut decompressed = Vec::new();
                match lzma_rs::xz_decompress(&mut Cursor::new(&data), &mut decompressed) {
                    Ok(_) => (),
                    Err(e) => {
                        error!("decompression failed: {e}");
                        return Err(ReturnStatus::from_message(
                            DataCorrupted,
                            format!("unable to decompress received slice {hash}"),
                        ))
                    },
                }

                let decoded: Vec<EncodingWithArchitectureMap<X64Arch, SynthesizedComputation>> =
                    match bincode::deserialize(&decompressed) {
                        Ok(data) => data,
                        Err(e) => {
                            error!("bincode::deserialize failed: {e}");
                            return Err(ReturnStatus::from_status(DataCorrupted))
                        },
                    };

                loaded.insert(*data_group, decoded);
            }

            let encodings = loaded.get(data_group).unwrap();
            for e in encodings.iter() {
                if e.encoding.prefix_matches(&instr, original_instr_bits) {
                    matching.push(e.clone());
                }
            }

            if matching.len() >= 100 {
                break
            }
        }

        Ok(matching)
    }

    #[wasm_bindgen]
    pub async fn search(&self, instr: String) -> SearchResult {
        let (original_instr_bits, instr) = match Self::parse_instr(instr) {
            Ok(x) => x,
            Err(e) => return e.into(),
        };
        match self.load_results_matching(instr, original_instr_bits).await {
            Ok(matching) => {
                let mut matching = matching
                    .iter()
                    .map(|e| SearchResultEntry::new(e, &instr, original_instr_bits))
                    .collect::<Vec<_>>();
                matching.sort_by_key(|e| e.matching_instr.clone());
                SearchResult::from_results(matching)
            },
            Err(e) => SearchResult::from_status(e),
        }
    }

    #[wasm_bindgen]
    pub async fn get(&self, instr: String, arch: String) -> LookupResult {
        let architecture_index = self
            .resolver
            .read()
            .await
            .architecture_names()
            .iter()
            .position(|n| n == &arch)
            .unwrap();
        let (original_instr_bits, instr) = match Self::parse_instr(instr) {
            Ok(x) => x,
            Err(e) => return e.into(),
        };
        match self.load_results_matching(instr, original_instr_bits).await {
            Ok(mut matching) => {
                matching.retain(|e| e.encoding.bits.len() <= original_instr_bits);
                if matching.is_empty() {
                    return LookupResult::from_status(ReturnStatus::from_status(FetchStatusCode::NotFound))
                }

                for item in matching.iter() {
                    debug!("Matching encoding: {item:?}");
                }

                let arch_groups = matching
                    .iter()
                    .flat_map(|e| {
                        e.architecture_maps
                            .iter()
                            .filter(|(filter, _)| filter.matches(&instr))
                            .map(|(_, m)| m)
                    })
                    .unique()
                    .map(|m| m.indices().collect::<Vec<_>>())
                    .collect::<Vec<_>>();

                let e = matching.iter().find(|e| {
                    e.architecture_maps
                        .iter()
                        .any(|(f, m)| m.get(architecture_index) && f.matches(&instr))
                });

                if let Some(e) = e {
                    LookupResult::from_encoding(WasmEncoding::new(instr, e.encoding.clone()), arch_groups)
                } else {
                    LookupResult::from_arches(arch_groups)
                }
            },
            Err(e) => LookupResult::from_status(e),
        }
    }

    async fn load(&self, path: &str) -> Result<Vec<u8>, JsValue> {
        let opts = RequestInit::new();
        opts.set_method("GET");
        opts.set_mode(RequestMode::Cors);

        let url = format!("{}{path}", self.base_url);

        info!("requesting {url:?}");

        let request = Request::new_with_str_and_init(&url, &opts)?;

        request.headers().set("Accept", "application/vnd.github.v3+json")?;

        let window = web_sys::window().unwrap();
        let resp_value = JsFuture::from(window.fetch_with_request(&request)).await?;

        // `resp_value` is a `Response` object.
        assert!(resp_value.is_instance_of::<Response>());
        let resp: Response = resp_value.dyn_into().unwrap();

        // Convert this other `Promise` into a rust `Future`.
        let blob = Blob::from(JsFuture::from(resp.blob()?).await?);
        let buf = blob.as_array_buffer().await;

        let array = Uint8Array::new(&buf);

        info!("Downloaded {} bytes", array.length());

        Ok(array.to_vec())
    }
}
