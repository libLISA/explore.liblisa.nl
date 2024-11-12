use liblisa::Instruction;
use liblisa::compare::summary::ArchId;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct ComparisonTable {
    rows: Vec<TableRow>,
}

impl ComparisonTable {
    pub fn new(rows: Vec<TableRow>) -> Self {
        Self {
            rows,
        }
    }

    pub fn rows(&self) -> &[TableRow] {
        &self.rows
    }
}

#[derive(Serialize, Deserialize)]
pub struct TableRow {
    architectures: Vec<Vec<ArchId>>,
    instrs: Vec<Instruction>,
}

impl TableRow {
    pub fn new(architectures: Vec<Vec<ArchId>>, instrs: Vec<Instruction>) -> Self {
        Self {
            architectures,
            instrs,
        }
    }

    pub fn architectures(&self) -> &[Vec<ArchId>] {
        &self.architectures
    }

    pub fn instrs(&self) -> &[Instruction] {
        &self.instrs
    }
}
