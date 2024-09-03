use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use clap::Parser;
use itertools::Itertools;
use liblisa::arch::x64::X64Arch;
use liblisa::compare::summary::ArchComparisonSummary;
use liblisa::encoding::indexed::EncodingId;
use liblisa::semantics::default::computation::SynthesizedComputation;
use liblisa_wasm_shared::group::DataGroup;
use liblisa_wasm_shared::tree::MappingTree;
use liblisa_wasm_shared::{ArchitectureMap, EncodingResolver, EncodingWithArchitectureMap};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

#[derive(clap::Parser)]
struct Args {
    data: PathBuf,

    #[arg(long)]
    output_dir: PathBuf,

    #[arg(long, default_value = "40")]
    entry_limit: usize,
}

pub fn main() {
    env_logger::init();
    let args = Args::parse();
    println!("Loading data...");

    let data: ArchComparisonSummary<X64Arch, SynthesizedComputation> =
        serde_json::from_reader(BufReader::new(File::open(args.data).unwrap())).unwrap();

    println!("Number of encodings: {}", data.index.len());
    println!("Building tree..");

    // How many encodings per tree leaf we are aiming for
    let tree = MappingTree::create_from_summary(&data, args.entry_limit);

    let leaves = tree.individual_leaves().unique().map(|v| v.to_vec()).collect::<Vec<_>>();

    println!("{} leaves", leaves.len());

    println!("Building encoding-to-leaf mapping");
    let mut encoding_to_leaf = vec![None; data.index.len()];
    for (leaf_index, leaf) in leaves.iter().enumerate() {
        let current_leaves = leaf
            .iter()
            .flat_map(|id| encoding_to_leaf[id.as_usize()])
            .collect::<HashSet<_>>();
        let new = current_leaves.iter().min().copied().unwrap_or(usize::MAX).min(leaf_index);

        for item in encoding_to_leaf.iter_mut().flatten() {
            if current_leaves.contains(item) {
                *item = new;
            }
        }

        for id in leaf.iter() {
            encoding_to_leaf[id.as_usize()] = Some(new);
        }
    }

    let mut leaf_index_map = HashMap::new();
    let reduced_tree = tree.map(|ids| {
        let leaf_index = encoding_to_leaf[ids[0].as_usize()].unwrap();
        assert!(ids.iter().all(|id| encoding_to_leaf[id.as_usize()].unwrap() == leaf_index));

        let num_indices = leaf_index_map.len();
        let data_group = *leaf_index_map
            .entry(leaf_index)
            .or_insert(DataGroup::from_u32(u32::try_from(num_indices).unwrap()));

        data_group
    });

    println!("Computing non-overlapping leaves");
    let non_overlapping_leaves = {
        let mut m = HashMap::new();
        for (encoding_index, leaf) in encoding_to_leaf.iter().enumerate() {
            if let Some(leaf) = leaf {
                m.entry(leaf_index_map.get(leaf).unwrap())
                    .or_insert_with(Vec::new)
                    .push(EncodingId::from_usize(encoding_index))
            }
        }

        m
    };

    println!("{} non-overlapping leaves", non_overlapping_leaves.len());

    // TODO: Check the compressed file sizes of the leaves and merge small leaves

    let encoding_index_to_architecture_maps = {
        let mut map = HashMap::new();
        for group in data.encodings.iter() {
            for encodings in group.encodings.iter() {
                let architecture_map = ArchitectureMap::new(encodings.architectures.iter().map(|arch| arch.0));
                for &id in encodings.encodings.iter() {
                    map.entry(id.as_usize())
                        .or_insert_with(Vec::new)
                        .push((group.filter.clone(), architecture_map));
                }
            }
        }

        map
    };

    let arch_names = data.architectures.iter().map(|info| info.name.clone()).collect();
    let index = EncodingResolver::new(arch_names, reduced_tree);

    // Write index
    let bytes = index.to_uncompressed_bytes();
    println!("Uncompressed tree bytes: {}", bytes.len());

    let bytes = lzma::compress(&bytes, 9 | lzma::EXTREME_PRESET).unwrap();
    println!("Compressed tree bytes: {}", bytes.len());

    std::fs::create_dir_all(&args.output_dir).unwrap();
    std::fs::write(args.output_dir.join("slices.index"), bytes).unwrap();

    println!("Writing leaf data...");
    // Write leaves
    let sizes_written = non_overlapping_leaves
        .into_par_iter()
        .map(|(leaf_index, encodings)| {
            let hash = leaf_index.murmur().as_hex();
            let path = args.output_dir.join(&hash[0..2]);
            let file = path.join(&hash[2..]).with_extension("slice");
            let data = encodings
                .iter()
                .map(|id| {
                    let encoding = data.index[id].encoding.clone();
                    let architecture_maps = encoding_index_to_architecture_maps[&id.as_usize()].clone();

                    EncodingWithArchitectureMap {
                        architecture_maps,
                        encoding,
                    }
                })
                .collect::<Vec<_>>();

            std::fs::create_dir_all(&path).unwrap();

            let bytes = bincode::serialize(&data).unwrap();
            let bytes = lzma::compress(&bytes, 9 | lzma::EXTREME_PRESET).unwrap();
            println!("Writing {} bytes to {file:?}", bytes.len());
            std::fs::write(file, &bytes).unwrap();

            bytes.len()
        })
        .collect::<Vec<_>>();

    println!(
        "Slices have sizes between {} and {} bytes",
        sizes_written.iter().min().unwrap(),
        sizes_written.iter().max().unwrap()
    );
}
