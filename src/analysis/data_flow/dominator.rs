/*
 * depile: translate three-address code back to C code.
 * Copyright (C) 2022  Zhichao Guan
 * Copyright (C) 2022  Ruifeng Xie
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

//! Data flow analysis for dominator relation.

use std::collections::{BTreeMap, BTreeSet};
use crate::analysis::control_flow::HasBranchingBehaviour;
use crate::analysis::data_flow::{AnalysisRes, ForwardAnalysis};
use crate::ir::Function;
use crate::ir::instr::InstrExt;

pub type BlockSet = BTreeSet<usize>;

pub type BlockMap = BTreeMap<usize, BlockSet>;
pub type ImmDomRel = BTreeMap<usize, Option<usize>>;

/// Returns nodes dominated by `block_idx`, i.e. `block_idx` dominates
/// `x` for `x` in return value.
pub fn dominate_nodes(domtree: &BlockMap, block_idx: usize) -> BlockSet {
    let mut res: BlockSet = BlockSet::new();
    for (i, doms) in domtree {
        if doms.contains(&block_idx) { res.insert(*i); }
    }
    res
}

/// Returns `true` if `x` dom `y`.
pub fn dominate(domtree: &BlockMap, x: usize, y: usize) -> bool {
    dominator(&domtree, y).contains(&x)
}

/// Returns dominators of `block_idx`, i.e. `x` dominates `block_idx`
/// for `x` in return value.
pub fn dominator(domtree: &BlockMap, block_idx: usize) -> &BlockSet {
    domtree.get(&block_idx).unwrap()
}

/// Returns nodes immediate dominated by `block_idx`, i.e. `block_idx`
/// immediate dominates `x` for `x` in return value.
pub fn imm_dominate_nodes(imm_doms: &ImmDomRel, block_idx: usize) -> BlockSet {
    let mut res: BlockSet = BlockSet::new();
    for (x, y) in imm_doms {
        // y.contains(block_idx)
        if y.map_or(false, |x| x == block_idx) { res.insert(*x); }
    }
    res
}

/// Returns immediate dominators of `block_idx`.
#[allow(unused)]
pub fn imm_dominators(imm_doms: &ImmDomRel, block_idx: usize) -> &Option<usize> {
    imm_doms.get(&block_idx).unwrap()
}

/// Returns the root of `domtree`.
#[allow(unused)]
pub fn root_of_domtree(domtree: &BlockMap) -> usize {
    for (i, doms) in domtree {
        if doms.len() == 1 { return *i; }
    }
    panic!("Root not found");
}

/// Compute dominator tree for function `func`.
pub fn compute_domtree<K: InstrExt>(func: &Function<K>) -> BlockMap
    where K::Branching: HasBranchingBehaviour,
          K::Marker: HasBranchingBehaviour,
          K::Extra: HasBranchingBehaviour {
    let res: Vec<AnalysisRes<DomAnalysis>> = DomAnalysis::run_forward(func);
    let mut domtree: BlockMap = BTreeMap::new();
    for (i, r) in res.iter().enumerate() {
        domtree.insert(i, r.out.get());
    }
    domtree
}

/// Compute immediate dominator for all blocks from `domtree`.
pub fn compute_idom(domtree: &BlockMap) -> ImmDomRel {
    let mut idoms = BTreeMap::new();
    for (i, _) in domtree { idoms.insert(*i, get_idom(*i, domtree)); }
    idoms
}

/// Compute immediate dominator for `block_idx`.
fn get_idom(block_idx: usize, domtree: &BlockMap) -> Option<usize> {
    let doms: &BlockSet = domtree.get(&block_idx).unwrap();
    for (i, ids) in domtree {
        let mut ids_ = ids.clone();
        ids_.insert(block_idx);
        if ids_.eq(doms) && !ids.contains(&block_idx) {
            return Some(*i);
        }
    }
    None
}

/// Macro to build a [`BlockMap`].
#[macro_export]
macro_rules! map_b_bs {
    ($( $key: expr => $val: expr ),*) => {
         BlockMap::from_iter([
             $( ($key, BTreeSet::from($val)), )*
         ])
    }
}

mod dominance_analysis {
    use crate::analysis::control_flow::ControlFlowExt;
    use crate::analysis::data_flow::ForwardAnalysis;
    use crate::analysis::lattice::JoinSemiLattice;
    use crate::ir::Block;
    use crate::ir::instr::InstrExt;
    use super::BlockSet;

    /// Dominator analysis.
    #[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
    pub struct DomAnalysis {
        pub bs: BlockSet,
    }

    impl DomAnalysis {
        pub fn empty() -> Self { Self { bs: BlockSet::new() } }
        pub fn complete(size: usize) -> Self { Self { bs: BlockSet::from_iter((0..size).into_iter()) } }
        pub fn get(&self) -> BlockSet { self.bs.clone() }
        pub fn insert(&mut self, x: usize) -> bool { self.bs.insert(x) }
    }

    impl<K: InstrExt> JoinSemiLattice<K> for DomAnalysis {
        fn bottom(env: &dyn ControlFlowExt<BlockKind=K>) -> Self {
            Self::complete(env.block_count())
        }

        fn join_assign(&mut self, other: Self) -> bool {
            let mut changed = false;
            for x in self.bs.clone() {
                if !other.bs.contains(&x) { changed |= self.bs.remove(&x); }
            }
            changed
        }
    }

    impl<K: InstrExt> ForwardAnalysis<K> for DomAnalysis {
        fn v_entry() -> Self { Self::empty() }

        fn transfer_function(block_idx: usize, _: &Block<K>, input: &Self, output: &mut Self) -> bool {
            let mut res = input.clone();
            res.insert(block_idx);
            <Self as JoinSemiLattice<K>>::join_assign(output, res)
            // output.join_assign::(res)
        }
    }
}

pub use dominance_analysis::DomAnalysis;

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use crate::ir::instr::basic::Blocks;
    use crate::ir::instr::stripped::Functions;
    use crate::ir::program::read_program;
    use crate::samples::{PRIME, ALL_SAMPLES};
    use super::{BlockMap, compute_domtree, compute_idom};

    #[test]
    fn test_idom() {
        let domtree: BlockMap = map_b_bs![
            0 => [0], 1 => [0, 1], 2 => [0, 1, 2], 3 => [0, 1, 3],
            4 => [0, 1, 3, 4], 5 => [0, 1, 3, 5],
            6 => [0, 1, 3, 6], 7 => [0, 1, 7]
        ];
        let idoms = BTreeMap::from_iter([
            (0, None), (1, Some(0)), (2, Some(1)), (3, Some(1)),
            (4, Some(3)), (5, Some(3)), (6, Some(3)), (7, Some(1)),
        ]);
        assert_eq!(compute_idom(&domtree), idoms)
    }

    fn get_sample_functions(src: &str) -> Functions {
        let program = read_program(src).unwrap();
        let blocks = Blocks::try_from(program.as_ref()).unwrap();
        blocks.functions().unwrap()
    }

    #[test]
    fn test_prime_dom() {
        let funcs = get_sample_functions(PRIME);
        let func = &funcs.functions[0];
        let domtree = compute_domtree(func);
        let idoms = compute_idom(&domtree);
        let idoms_ = BTreeMap::from_iter([
            (0, None), (1, Some(0)), (2, Some(1)), (3, Some(2)), (4, Some(3)),
            (5, Some(4)), (6, Some(4)), (7, Some(6)), (8, Some(4)),
            (9, Some(3)), (10, Some(9)), (11, Some(9)), (12, Some(1))
        ]);
        assert_eq!(idoms, idoms_);
    }

    #[test]
    fn test_samples_dom() {
        for s in ALL_SAMPLES {
            for func in get_sample_functions(s).functions.iter() {
                compute_idom(&compute_domtree(func));
            }
        }
    }
}
