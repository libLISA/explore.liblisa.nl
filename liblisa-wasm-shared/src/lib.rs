pub mod group;
pub mod tree;
pub mod table;

use std::io::Cursor;

use group::DataGroup;
use liblisa::Instruction;
use liblisa::arch::Arch;
use liblisa::encoding::Encoding;
use liblisa::instr::InstructionFilter;
use log::info;
use tree::MappingTree;

#[derive(bitcode::Decode, bitcode::Encode, Default)]
pub struct EqualityGroup {
    implementation_indices: Vec<Option<u8>>,
}

#[derive(bitcode::Decode, bitcode::Encode, Default)]
pub struct EncodingResolver {
    arch_names: Vec<String>,
    index: MappingTree<DataGroup>,
}

#[derive(
    Copy,
    Clone,
    Debug,
    serde::Serialize,
    serde::Deserialize,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    bitcode::Encode,
    bitcode::Decode,
)]
pub struct ArchitectureMap(u8);

impl ArchitectureMap {
    pub fn new(indices: impl IntoIterator<Item = usize>) -> Self {
        Self(indices.into_iter().fold(0u8, |acc, x| acc | (1u8 << x)))
    }

    pub fn indices(&self) -> impl Iterator<Item = usize> + '_ {
        (0..8).filter(|&n| self.get(n))
    }

    pub fn get(&self, index: usize) -> bool {
        (self.0 >> index) & 1 != 0
    }
}

#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct EncodingWithArchitectureMap<A: Arch, C> {
    pub architecture_maps: Vec<(InstructionFilter, ArchitectureMap)>,
    pub encoding: Encoding<A, C>,
}

impl EncodingResolver {
    pub fn new(arch_names: Vec<String>, index: MappingTree<DataGroup>) -> Self {
        Self {
            arch_names,
            index,
        }
    }

    pub fn lookup(&self, instr: &Instruction, max_bits: usize) -> Vec<DataGroup> {
        self.index.lookup(instr, max_bits).into_iter().copied().collect()
    }

    pub fn architecture_names(&self) -> &[String] {
        &self.arch_names
    }

    pub fn to_uncompressed_bytes(&self) -> Vec<u8> {
        let bytes = bitcode::encode(&self).unwrap();
        info!("{} bytes uncompressed", bytes.len());

        bytes
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut decompressed = Vec::new();
        lzma_rs::xz_decompress(&mut Cursor::new(bytes), &mut decompressed).unwrap();
        let result: EncodingResolver = bitcode::decode(&decompressed).unwrap();

        info!(
            "Loaded index with {} data groups for architectures {:?}",
            result.index.leaves().count(),
            result.arch_names
        );

        result
    }
}
