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

use std::collections::BTreeSet;
use crate::analysis::control_flow::HasBranchingBehaviour;
use crate::analysis::data_flow::{AnalysisRes, ForwardAnalysis};
use crate::ir::Function;
use crate::ir::instr::InstrExt;

type BlockSet = BTreeSet<usize>;

/// Dominator Relation.
pub type DomRel = Box<[Box<[usize]>]>;
/// Immediate Dominator Relation.
pub type ImmDomRel = Box<[Option<usize>]>;

/// Compute dominator tree for function `func`.
pub fn get_dominators<K: InstrExt>(func: &Function<K>) -> DomRel
    where K::Branching: HasBranchingBehaviour,
          K::Marker: HasBranchingBehaviour,
          K::Extra: HasBranchingBehaviour {
    let res: Vec<AnalysisRes<DomAnalysis>> = DomAnalysis::run_forward(func);
    res.into_iter().map(|r| r.out.0.into_iter().collect()).collect()
}

/// Compute immediate dominator for all blocks from `domtree`.
pub fn get_immediate_dominators(domtree: &[Box<[usize]>]) -> ImmDomRel {
    (0..domtree.len()).map(|i| get_immediate_dominator(i, domtree)).collect()
}

/// Compute immediate dominator for `block_idx`.
fn get_immediate_dominator(block_idx: usize, domtree: &[Box<[usize]>]) -> Option<usize> {
    let doms = domtree[block_idx].as_ref();
    for (i, candidate) in domtree.iter().enumerate() {
        // candidate ∪ {block_idx} == doms
        if i == block_idx { continue; }
        if candidate.binary_search(&block_idx).is_ok() { continue; }
        if candidate.len() + 1 != doms.len() { continue; }
        if let Ok(p) = doms.binary_search(&block_idx) {
            assert_eq!(doms[p], block_idx);
            if candidate[..p] == doms[..p] && candidate[p..] == doms[p + 1..] {
                return Some(i);
            }
        }
    }
    None
}

mod dominance_analysis {
    use std::collections::BTreeSet;
    use crate::analysis::control_flow::ControlFlowExt;
    use crate::analysis::data_flow::ForwardAnalysis;
    use crate::analysis::lattice::JoinSemiLattice;
    use crate::ir::Block;
    use crate::ir::instr::InstrExt;
    use super::BlockSet;

    /// Dominator analysis.
    #[derive(Default, Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
    pub struct DomAnalysis(pub BlockSet);

    impl DomAnalysis {
        fn empty() -> Self { DomAnalysis(BlockSet::new()) }
        fn complete(size: usize) -> Self { DomAnalysis(BlockSet::from_iter(0..size)) }
        fn insert(&mut self, x: usize) -> bool { self.0.insert(x) }
    }

    impl JoinSemiLattice for DomAnalysis {
        fn bottom<K: InstrExt>(env: &dyn ControlFlowExt<BlockKind=K>) -> Self {
            Self::complete(env.block_count())
        }
        fn join_assign(&mut self, other: Self) -> bool {
            let mut new = self.0
                .intersection(&other.0)
                .copied().collect::<BTreeSet<_>>();
            std::mem::swap(&mut self.0, &mut new);
            new.len() != self.0.len()
        }
    }

    impl<K: InstrExt> ForwardAnalysis<K> for DomAnalysis {
        fn v_entry() -> Self { Self::empty() }
        fn transfer_function(block_idx: usize, _: &Block<K>, input: &Self, output: &mut Self) -> bool {
            let mut res = input.clone();
            res.insert(block_idx);
            output.join_assign(res)
        }
    }
}

pub use dominance_analysis::DomAnalysis;

#[cfg(test)]
mod tests {
    macro_rules! dom_rel {
        ($($val: expr),* $(,)?) => {{
            fn type_coerce<const N: usize>(xs: [usize; N]) -> Box<[usize]> { Box::new(xs) }
            Box::new([$(type_coerce($val)),*]) as Box<[_]>
        }}
    }

    use crate::ir::instr::basic::Blocks;
    use crate::ir::instr::stripped::Functions;
    use crate::ir::program::read_program;
    use crate::samples::{PRIME, ALL_SAMPLES};
    use super::{DomRel, get_dominators, get_immediate_dominators};

    #[test]
    fn test_idom() {
        let domtree: DomRel = dom_rel![
            [0], [0, 1], [0, 1, 2], [0, 1, 3], [0, 1, 3, 4],
            [0, 1, 3, 5], [0, 1, 3, 6], [0, 1, 7],
        ];
        assert_eq!(get_immediate_dominators(&domtree).as_ref(), [
            None, Some(0), Some(1), Some(1),
            Some(3), Some(3), Some(3), Some(1),
        ]);
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
        let domtree = get_dominators(func);
        assert_eq!(get_immediate_dominators(&domtree).as_ref(), [
            None, Some(0), Some(1), Some(2), Some(3),
            Some(4), Some(4), Some(6), Some(4),
            Some(3), Some(9), Some(9), Some(1)
        ]);
    }

    #[test]
    fn test_samples_dom() {
        for s in ALL_SAMPLES {
            for func in get_sample_functions(s).functions.iter() {
                get_immediate_dominators(&get_dominators(func));
            }
        }
    }
}
