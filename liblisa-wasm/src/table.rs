use liblisa::Instruction;
use liblisa_wasm_shared::table::ComparisonTable;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct TableWrapper {
    table: ComparisonTable,
}

#[wasm_bindgen]
impl TableWrapper {
    pub(crate) fn new(table: ComparisonTable) -> Self {
        Self {
            table,
        }
    }

    #[wasm_bindgen]
    pub fn into_rows(&self) -> Vec<RowWrapper> {
        self.table
            .rows()
            .iter()
            .map(|r| {
                let mut v = Vec::new();
                for (index, ids) in r.architectures().iter().enumerate() {
                    for id in ids {
                        if id.0 >= v.len() {
                            v.resize(id.0 + 1, 0);
                        }

                        v[id.0] = index;
                    }
                }

                RowWrapper {
                    symbols: v,
                    instrs: r.instrs().to_vec(),
                }
            })
            .collect()
    }
}

#[wasm_bindgen]
pub struct RowWrapper {
    symbols: Vec<usize>,
    instrs: Vec<Instruction>,
}

#[wasm_bindgen]
impl RowWrapper {
    #[wasm_bindgen]
    pub fn symbols(&self) -> Vec<usize> {
        self.symbols.clone()
    }

    #[wasm_bindgen]
    pub fn instrs(&self) -> Vec<String> {
        self.instrs.iter().map(|i| format!("{i:X}")).collect()
    }
}
