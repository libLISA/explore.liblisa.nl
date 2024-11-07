use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use itertools::Itertools;
use liblisa::Instruction;
use liblisa::arch::x64::X64Arch;
use liblisa::arch::{Arch, Register};
use liblisa::encoding::Encoding;
use liblisa::encoding::dataflows::{AccessKind, Dataflows, Dest, Source};
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa::semantics::default::smtgen::{StorageLocations, Z3Model};
use liblisa::state::{Addr, Location, MemoryState, Permissions, SystemState};
use liblisa::value::{Value, ValueType};
use log::debug;
use wasm_bindgen::prelude::*;

use crate::codegen::SmtStringSolver;

#[derive(Clone, Debug)]
#[wasm_bindgen]
pub struct WasmEncoding {
    encoding: Encoding<X64Arch, SynthesizedComputation>,
    instance: Dataflows<X64Arch, SynthesizedComputation>,

    // TODO: We will need this to determine the value of DontCare bits.
    #[allow(unused)]
    instr: Instruction,
}

impl WasmEncoding {
    pub fn new(instr: Instruction, encoding: Encoding<X64Arch, SynthesizedComputation>) -> Self {
        let part_values = encoding.extract_parts(&instr);
        Self {
            instr,
            instance: encoding.instantiate(&part_values).unwrap(),
            encoding,
        }
    }
}

type InputStateInfo = (SystemState<X64Arch>, Vec<Dest<X64Arch>>, HashMap<Dest<X64Arch>, String>);

#[wasm_bindgen]
impl WasmEncoding {
    pub fn byte_len(&self) -> usize {
        self.encoding.instr().byte_len()
    }

    pub fn bits(&self) -> String {
        serde_json::to_string(&self.encoding.bits).unwrap()
    }

    pub fn json(&self) -> String {
        serde_json::to_string(&self.encoding).unwrap()
    }

    pub fn part_values(&self) -> Vec<u64> {
        self.encoding.extract_parts(&self.instr)
    }

    /// Returns a string containing a JSON-array of dests
    pub fn simulation_inputs(&self) -> String {
        let mut inputs = HashMap::new();
        for df in self.instance.output_dataflows() {
            for input in df.inputs().iter() {
                if let Source::Dest(dest) = input {
                    let loc = Location::from(dest);
                    let ranges = inputs.entry(loc).or_insert_with(Vec::new);
                    let mut size = dest.size();

                    while let Some(overlapping_index) = ranges.iter().position(|r| size.overlaps(r)) {
                        let other = ranges.remove(overlapping_index);
                        size = size.union(&other);
                    }

                    ranges.push(size);
                }
            }
        }

        let mut inputs = inputs
            .into_iter()
            .flat_map(|(k, v)| {
                let dest = Dest::from(k);

                v.into_iter().map(move |size| dest.with_size(size))
            })
            .collect::<Vec<_>>();
        inputs.sort();

        serde_json::to_string(&inputs).unwrap()
    }

    fn create_input_state(&self, input_values: HashMap<String, String>) -> InputStateInfo {
        let state = SystemState::default();
        let mut areas_set = Vec::new();
        let mut parsing_errors = HashMap::new();
        let mut mem = Vec::with_capacity(self.instance.addresses.len());
        for access in self.instance.addresses.iter() {
            mem.push((
                Addr::new(0),
                match access.kind {
                    AccessKind::Input => Permissions::Read,
                    AccessKind::InputOutput => Permissions::ReadWrite,
                    AccessKind::Executable => Permissions::Execute,
                },
                vec![0; access.size.end as usize],
            ));
        }

        let mut state = state.with_new_memory(mem.len(), 1, MemoryState::from_vec(mem.clone()));

        for (dest, val) in input_values.into_iter() {
            if val.trim().is_empty() {
                continue
            }

            let dest: Dest<X64Arch> = serde_json::from_str(&dest).unwrap();
            areas_set.push(dest);
            let mut tmp_bytes = Vec::new();
            state.set_dest(&dest, &match dest.value_type() {
                ValueType::Bytes(num) => {
                    tmp_bytes.resize(num, 0);
                    let len = ((val.len() + 1) / 2).min(num);
                    match hex::decode_to_slice(&val, &mut tmp_bytes[..len]) {
                        Ok(_) => Value::Bytes(&tmp_bytes),
                        Err(e) => {
                            parsing_errors.insert(dest, format!("unable to parse hexadecimal byte sequence: {e}"));
                            continue
                        },
                    }
                },
                ValueType::Num => {
                    if let Some(val) = val.strip_prefix("0x") {
                        match u64::from_str_radix(val, 16) {
                            Ok(n) => Value::Num(n),
                            Err(e) => {
                                parsing_errors.insert(dest, format!("unable to parse hexadecimal number: {e}"));
                                continue
                            },
                        }
                    } else {
                        match val.parse::<u64>() {
                            Ok(n) => Value::Num(n),
                            Err(e) => {
                                parsing_errors.insert(dest, format!("unable to parse decimal number: {e}"));
                                continue
                            },
                        }
                    }
                },
            });
        }

        for (index, area) in self.instance.extract_memory_areas(&state.clone()).enumerate() {
            state.memory_mut().get_mut(index).set_addr(area.start_addr());
        }

        (state, areas_set, parsing_errors)
    }

    pub fn get_parsing_errors(&self, input_data: String) -> String {
        let inputs: HashMap<String, String> = serde_json::from_str(&input_data).unwrap();
        let (_, _, parsing_errors) = self.create_input_state(inputs);

        let parsing_errors = parsing_errors
            .into_iter()
            .map(|(dest, err)| (serde_json::to_string(&dest).unwrap(), err))
            .collect::<HashMap<_, _>>();

        serde_json::to_string(&parsing_errors).unwrap()
    }

    pub fn parse_simulation_values(&self, input_data: String) -> String {
        let inputs: HashMap<String, String> = serde_json::from_str(&input_data).unwrap();
        let (input_state, areas_set, _) = self.create_input_state(inputs);

        let result = self
            .instance
            .outputs
            .iter()
            .flat_map(|df| df.inputs().iter())
            .flat_map(|source| Dest::try_from(*source).ok())
            .filter(|dest| areas_set.iter().any(|x| x.overlaps(dest)))
            .map(|dest| {
                let key = serde_json::to_string(&dest).unwrap();
                let val = match input_state.get_dest(&dest) {
                    Value::Bytes(b) => format!("[{}]", hex::encode(b)),
                    Value::Num(n) => {
                        let size = dest.size().num_bytes() * 2;
                        format!("0x{n:0width$x?}", width = size)
                    },
                };

                (key, val)
            })
            .collect::<HashMap<_, _>>();

        serde_json::to_string(&result).unwrap()
    }

    pub fn simulate(&self, input_data: String) -> String {
        if !self.encoding.all_outputs_have_computations() {
            return String::from("{}");
        }

        let inputs: HashMap<String, String> = serde_json::from_str(&input_data).unwrap();
        let (mut state, areas_set, _) = self.create_input_state(inputs);

        self.instance.execute(&mut state);

        let outputs = self
            .instance
            .outputs
            .iter()
            .filter(|o| {
                o.inputs.iter().any(|source| {
                    areas_set
                        .iter()
                        .any(|d| Dest::try_from(*source).ok().map(|s| s.overlaps(d)).unwrap_or(false))
                })
            })
            .map(|o| {
                (serde_json::to_string(&o.target).unwrap(), match state.get_dest(&o.target) {
                    Value::Bytes(b) => format!("[{}]", hex::encode(b)),
                    Value::Num(n) => {
                        let size = o.target.size().num_bytes() * 2;
                        format!("0x{n:0width$x?}", width = size)
                    },
                })
            })
            .collect::<HashMap<_, _>>();

        serde_json::to_string(&outputs).unwrap()
    }

    pub fn smt_code(&self, instr: &str) -> String {
        let mut result = String::new();
        let instr = Instruction::new(&hex::decode(instr).unwrap());
        let encoding = {
            let part_values: Vec<Option<u64>> = self.encoding.extract_parts(&instr).into_iter().map(Some).collect::<Vec<_>>();
            let encoding = self.encoding.instantiate_partially(&part_values).unwrap();
            debug!("Instantiated: {encoding}");
            encoding
        };

        let mut context = SmtStringSolver::new();
        let mut storage = StorageLocations::new(&mut context);
        let model = Z3Model::of(&encoding, &mut storage, &mut context);
        let concrete = model.compute_concrete_outputs(&encoding, &mut storage, &mut context);

        for constraint in model.constraints() {
            writeln!(&mut result, "(assert {})", constraint).unwrap();
        }

        for &index in concrete.intermediate_values_needed() {
            let intermediate = &model.intermediate_outputs()[index];
            if let Some(smt) = intermediate.smt() {
                writeln!(&mut result, "(assert (= {:?} {}))", intermediate.name(), smt.clone()).unwrap();
            } else {
                return String::from("unavailable: not all outputs have been synthesized")
            }
        }

        for output in concrete.concrete_outputs().iter().sorted_by_key(|o| o.target()) {
            if let Some(smt) = output.smt() {
                writeln!(&mut result).unwrap();
                writeln!(&mut result, "<span class=\"comment\">; output {:?}</span>", output.target()).unwrap();

                let size = output.target().size();
                writeln!(
                    &mut result,
                    "(assert (= ((_ extract {} {}) {}) {smt}))",
                    size.end_byte * 8 + 7,
                    size.start_byte * 8,
                    smt_name(&Location::from(output.target()))
                )
                .unwrap();
            } else {
                return String::from("unavailable: not all outputs have been synthesized")
            }
        }

        let mut declarations = String::new();
        let mut declared = HashSet::new();
        for bv in context.bv_consts().iter().sorted_by_key(|bv| bv.name()) {
            if declared.insert(bv.name().to_string()) && result.contains(bv.name()) {
                writeln!(&mut declarations, "(declare-const {} (_ BitVec {}))", bv.name(), bv.size()).unwrap();
            }
        }

        for output in concrete.concrete_outputs().iter().sorted_by_key(|o| o.target()) {
            let loc = Location::from(output.target());
            let name = smt_name(&loc);
            if declared.insert(name.clone()) && result.contains(&name) {
                writeln!(
                    &mut declarations,
                    "(declare-const {} (_ BitVec {}))",
                    name,
                    match loc {
                        Location::Reg(r) => r.byte_size(),
                        Location::Memory(m) => encoding.dataflows.addresses[m].size.end as usize,
                    } * 8
                )
                .unwrap();
            }
        }

        for bool in context.bool_consts().iter().sorted_by_key(|bool| bool.name()) {
            if declared.insert(bool.name().to_string()) && result.contains(bool.name()) {
                writeln!(&mut declarations, "(declare-const {} Bool)", bool.name()).unwrap();
            }
        }

        format!("{declarations}{result}")
    }
}

fn smt_name<A: Arch>(reg: &Location<A>) -> String {
    match reg {
        Location::Reg(reg) => format!("out_r{reg}"),
        Location::Memory(memory_index) => format!("out_m{memory_index}"),
    }
}
