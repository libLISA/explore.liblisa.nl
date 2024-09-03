use std::collections::HashSet;
use std::hash::Hash;

use liblisa::arch::Arch;
use liblisa::compare::summary::ArchComparisonSummary;
use liblisa::encoding::indexed::EncodingId;
use liblisa::instr::{FilterBit, InstructionFilter};
use liblisa::semantics::Computation;
use liblisa::Instruction;
use log::{debug, info, trace};

#[derive(Clone, Debug, bitcode::Encode, bitcode::Decode)]
pub enum Item<T> {
    Node(u8),
    Leaf(T),
    Empty,
}

#[derive(Clone, Debug, bitcode::Encode, bitcode::Decode)]
pub struct MappingTree<T> {
    tree: Vec<Item<T>>,
}

impl<T> Default for MappingTree<T> {
    fn default() -> Self {
        Self {
            tree: Vec::new(),
        }
    }
}

impl MappingTree<Vec<EncodingId>> {
    pub fn create_from_summary<A: Arch, C: Computation>(data: &ArchComparisonSummary<A, C>, entry_limit: usize) -> Self {
        info!("Building tree...");
        let mut flattened_filters = HashSet::new();
        for group in data.encodings.iter() {
            for encodings in group.encodings.iter() {
                for id in encodings.encodings.iter() {
                    for filter in data.index[id].filters.iter() {
                        flattened_filters.insert((filter.intersect(&group.filter), *id));
                    }
                }
            }
        }

        Self::new(flattened_filters.into_iter().collect::<Vec<_>>(), entry_limit)
    }
}

impl<T: Clone + Hash + Eq> MappingTree<Vec<T>> {
    fn build_internal(entries: Vec<(InstructionFilter, T)>, entry_limit: usize) -> Vec<Item<Vec<T>>> {
        let mut output = Vec::new();
        let mut num_done = 0usize;
        let mut queue = Vec::new();
        queue.push((0, entries));

        while let Some((depth, entries)) = queue.pop() {
            if entries.is_empty() {
                trace!("depth={depth}: no entries");
                output.push(Item::Empty);
            } else {
                let num_unique = entries.iter().map(|(_, t)| t).collect::<HashSet<_>>().len();
                trace!(
                    "depth={depth}: {} entries ({num_unique} unique values; {num_done} done)",
                    entries.len()
                );
                if depth >= 32 || num_unique < entry_limit {
                    num_done += entries.len();
                    output.push(Item::Leaf(entries.into_iter().map(|(_, t)| t).collect()));
                } else {
                    let max_index = entries.iter().map(|(f, _)| f.bit_len()).min().unwrap();
                    if let Some(best_split_index) = (0..max_index)
                        .filter(|&index| {
                            let mut any0 = false;
                            let mut any1 = false;

                            for (f, _) in entries.iter() {
                                match f.nth_bit_from_left(index) {
                                    FilterBit::Is0 => any0 = true,
                                    FilterBit::Is1 => any1 = true,
                                    FilterBit::Wildcard => (),
                                }

                                if any0 && any1 {
                                    return true
                                }
                            }

                            false
                        })
                        .min_by_key(|&index| {
                            let mut num_wildcard = 0usize;
                            let mut num_0 = 0usize;
                            let mut num_1 = 0usize;
                            for (f, _) in entries.iter() {
                                match f.nth_bit_from_left(index) {
                                    FilterBit::Is0 => num_0 += 1,
                                    FilterBit::Is1 => num_1 += 1,
                                    FilterBit::Wildcard => num_wildcard += 1,
                                }
                            }

                            (num_wildcard, num_0.abs_diff(num_1))
                        })
                    {
                        trace!(
                            "depth={depth}: splitting {} entries ({} non-wildcard) on bit {best_split_index}",
                            entries.len(),
                            entries
                                .iter()
                                .filter(|(f, _)| f.nth_bit_from_left(best_split_index) != FilterBit::Wildcard)
                                .count(),
                        );
                        output.push(Item::Node(
                            best_split_index
                                .try_into()
                                .expect("No instruction should countain more than 16 bytes / 256 bits"),
                        ));
                        // 1 second (1 below top of stack)
                        queue.push((
                            depth + 1,
                            entries
                                .iter()
                                .filter(|(f, _)| f.nth_bit_from_left(best_split_index) != FilterBit::Is0)
                                .cloned()
                                .collect::<Vec<_>>(),
                        ));
                        // 0 first (top of stack)
                        queue.push((
                            depth + 1,
                            entries
                                .iter()
                                .filter(|(f, _)| f.nth_bit_from_left(best_split_index) != FilterBit::Is1)
                                .cloned()
                                .collect::<Vec<_>>(),
                        ));
                    } else {
                        num_done += entries.len();
                        output.push(Item::Leaf(entries.into_iter().map(|(_, t)| t).collect()));
                    }
                }
            }
        }

        output
    }

    pub fn new(entries: Vec<(InstructionFilter, T)>, entry_limit: usize) -> Self {
        debug!("{} entries to process", entries.len());
        let tree = Self::build_internal(entries, entry_limit);

        debug!(
            "Built tree with {} leaves",
            tree.iter().filter(|item| matches!(item, Item::Leaf(_))).count()
        );
        debug!(
            "{} distinct leaves",
            tree.iter()
                .flat_map(|item| match item {
                    Item::Leaf(t) => Some(t),
                    _ => None,
                })
                .collect::<HashSet<_>>()
                .len()
        );

        MappingTree {
            tree,
        }
    }

    pub fn map_items<U>(self, mut f: impl FnMut(T) -> U) -> MappingTree<Vec<U>> {
        MappingTree {
            tree: self
                .tree
                .into_iter()
                .map(|item| match item {
                    Item::Node(index) => Item::Node(index),
                    Item::Leaf(x) => Item::Leaf(x.into_iter().map(&mut f).collect()),
                    Item::Empty => Item::Empty,
                })
                .collect(),
        }
    }

    pub fn individual_leaves(&self) -> impl Iterator<Item = &[T]> + '_ {
        self.tree.iter().flat_map(|item| match item {
            Item::Leaf(t) => Some(t.as_slice()),
            _ => None,
        })
    }
}

struct TreeWalker<'a, T> {
    tree: &'a [Item<T>],
}

impl<T> Copy for TreeWalker<'_, T> {}

impl<T> Clone for TreeWalker<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a, T> TreeWalker<'a, T> {
    fn new(tree: &'a [Item<T>]) -> Self {
        Self {
            tree,
        }
    }

    fn current(&self) -> &'a Item<T> {
        &self.tree[0]
    }

    fn next(&mut self) {
        self.tree = &self.tree[1..];
    }

    fn enter(&mut self) {
        assert!(matches!(self.current(), Item::Node(_)));
        self.next();
    }

    fn take_left(&mut self) {
        self.enter();
    }

    fn take_right(&mut self) {
        self.enter();
        self.skip(1);
    }

    fn split(&self) -> (Self, Self) {
        let mut left = *self;
        let mut right = *self;

        left.take_left();
        right.take_right();

        (left, right)
    }

    fn skip(&mut self, mut num: usize) {
        while num > 0 {
            num -= 1;
            if let Item::Node(_) = self.current() {
                num += 2
            }

            self.next();
        }
    }

    // TODO
    #[allow(unused)]
    fn children(&self) -> impl Iterator<Item = &T> {
        let mut num = 1;
        self.tree
            .iter()
            .take_while(move |item| {
                if num > 0 {
                    num -= 1;
                    if let Item::Node(_) = item {
                        num += 2
                    }

                    true
                } else {
                    false
                }
            })
            .flat_map(|item| if let Item::Leaf(leaf) = item { Some(leaf) } else { None })
    }
}

impl<T: Clone + Hash + Eq> MappingTree<T> {
    pub fn map<U>(self, mut f: impl FnMut(T) -> U) -> MappingTree<U> {
        MappingTree {
            tree: self
                .tree
                .into_iter()
                .map(|item| match item {
                    Item::Node(index) => Item::Node(index),
                    Item::Leaf(x) => Item::Leaf(f(x)),
                    Item::Empty => Item::Empty,
                })
                .collect(),
        }
    }

    pub fn leaves(&self) -> impl Iterator<Item = &T> + '_ {
        self.tree.iter().flat_map(|item| match item {
            Item::Leaf(t) => Some(t),
            _ => None,
        })
    }

    pub fn lookup(&self, instr: &Instruction, max_bits: usize) -> Vec<&T> {
        let mut walkers = vec![TreeWalker::new(&self.tree)];
        let mut result = Vec::new();
        while let Some(mut walker) = walkers.pop() {
            loop {
                match walker.current() {
                    Item::Node(index) => {
                        if (*index as usize) < max_bits {
                            if instr.nth_bit_from_left(*index as usize) != 0 {
                                walker.take_right();
                            } else {
                                walker.take_left();
                            }
                        } else {
                            let (left, right) = walker.split();
                            walkers.extend([left, right]);
                            break
                        }
                    },
                    Item::Leaf(t) => {
                        result.push(t);
                        break
                    },
                    Item::Empty => break,
                }
            }
        }

        result
    }
}
