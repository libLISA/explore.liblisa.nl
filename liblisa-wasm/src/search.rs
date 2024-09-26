use itertools::Itertools;
use liblisa::Instruction;
use liblisa::arch::x64::X64Arch;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa_wasm_shared::EncodingWithArchitectureMap;
use serde::{Deserialize, Serialize};
use wasm_bindgen::prelude::*;

use crate::encoding::WasmEncoding;

#[wasm_bindgen]
#[derive(Copy, Clone, Debug, Default)]
pub enum FetchStatusCode {
    Success,
    InvalidHex,

    #[default]
    UnknownError,
    NotFound,
    NetworkError,
    DataCorrupted,
    OutOfScope,
    MissingOnArchitecture,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SearchResultEntry {
    pub match_bits: Vec<MatchBit>,
    pub matching_instr: String,
    pub architectures: Vec<usize>,
}

impl SearchResultEntry {
    pub fn new(
        encoding: &EncodingWithArchitectureMap<X64Arch, SynthesizedComputation>, instr: &Instruction, original_instr_bits: usize,
    ) -> Self {
        let mut bytes = instr
            .bytes()
            .iter()
            .chain(encoding.encoding.instr().bytes().iter().skip(instr.byte_len()))
            .take(encoding.encoding.instr().byte_len())
            .copied()
            .collect::<Vec<_>>();

        if original_instr_bits % 8 == 4 && instr.byte_len() < encoding.encoding.instr().byte_len() {
            bytes[instr.byte_len() - 1] =
                (bytes[instr.byte_len() - 1] & 0xf0) | (encoding.encoding.instr().bytes()[instr.byte_len() - 1] & 0x0f);
        }

        let matching_instr = Instruction::new(&bytes);

        SearchResultEntry {
            match_bits: encoding
                .encoding
                .bits
                .iter()
                .rev()
                .enumerate()
                .map(|(index, bit)| MatchBit {
                    bit_value: matching_instr.nth_bit_from_left(index),
                    part_index: bit.part_index(),
                    matched: index < original_instr_bits,
                })
                .collect(),
            matching_instr: matching_instr.bytes().iter().map(|b| format!("{b:02x}")).join(""),
            architectures: if let Some((_, e)) = encoding
                .architecture_maps
                .iter()
                .find(|(filter, _)| filter.matches(&matching_instr))
            {
                e.indices().collect()
            } else {
                Vec::new()
            },
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MatchBit {
    pub bit_value: u8,
    pub part_index: Option<usize>,
    pub matched: bool,
}

#[wasm_bindgen]
#[derive(Clone, Debug, Default)]
pub struct ReturnStatus {
    code: FetchStatusCode,
    message: String,
}

#[wasm_bindgen]
impl ReturnStatus {
    pub fn from_status(code: FetchStatusCode) -> Self {
        Self {
            code,
            ..Self::default()
        }
    }

    pub fn from_message(code: FetchStatusCode, message: String) -> Self {
        Self {
            code,
            message,
        }
    }

    pub fn from_js_error(code: FetchStatusCode, error: JsValue) -> Self {
        Self {
            code,
            message: error.as_string().unwrap_or_default(),
        }
    }

    pub fn code(&self) -> FetchStatusCode {
        self.code
    }

    pub fn message(&self) -> String {
        self.message.clone()
    }
}

#[wasm_bindgen]
#[derive(Clone, Debug, Default)]
pub struct SearchResult {
    status: ReturnStatus,
    results: Vec<SearchResultEntry>,
}

impl SearchResult {
    pub fn from_results(results: Vec<SearchResultEntry>) -> Self {
        Self {
            status: if results.is_empty() {
                ReturnStatus::from_status(FetchStatusCode::NotFound)
            } else {
                ReturnStatus::from_status(FetchStatusCode::Success)
            },
            results,
        }
    }

    pub fn from_status(status: ReturnStatus) -> Self {
        Self {
            status,
            ..Self::default()
        }
    }
}

#[wasm_bindgen]
impl SearchResult {
    pub fn status(&self) -> ReturnStatus {
        self.status.clone()
    }

    pub fn results(&self) -> String {
        serde_json::to_string(&self.results).unwrap()
    }
}

impl From<ReturnStatus> for SearchResult {
    fn from(status: ReturnStatus) -> Self {
        Self::from_status(status)
    }
}

#[wasm_bindgen]
#[derive(Clone, Debug)]
pub struct LookupResult {
    status: ReturnStatus,
    encoding: Option<WasmEncoding>,
    arch_groups: Vec<Vec<usize>>,
}

impl LookupResult {
    pub fn from_encoding(encoding: WasmEncoding, arch_groups: Vec<Vec<usize>>) -> Self {
        Self {
            status: ReturnStatus::from_status(FetchStatusCode::Success),
            encoding: Some(encoding),
            arch_groups,
        }
    }

    pub fn from_status(status: ReturnStatus) -> Self {
        Self {
            status,
            encoding: None,
            arch_groups: Vec::new(),
        }
    }

    pub fn from_arches(arch_groups: Vec<Vec<usize>>) -> Self {
        Self {
            status: ReturnStatus::from_status(FetchStatusCode::MissingOnArchitecture),
            encoding: None,
            arch_groups,
        }
    }
}

#[wasm_bindgen]
impl LookupResult {
    pub fn status(&self) -> ReturnStatus {
        self.status.clone()
    }

    pub fn encoding(&self) -> WasmEncoding {
        self.encoding.clone().unwrap()
    }

    pub fn architecture_groups(&self) -> String {
        serde_json::to_string(&self.arch_groups).unwrap()
    }
}

impl From<ReturnStatus> for LookupResult {
    fn from(status: ReturnStatus) -> Self {
        Self::from_status(status)
    }
}
