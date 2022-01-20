/*
 * depile: translate three-address code back to C code.
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

//! Analysis and transformations related to control flows.

use std::collections::BTreeSet;
use itertools::Itertools;
use smallvec::{SmallVec, ToSmallVec};
use crate::ir::{Block, Instr};
use crate::ir::instr::{basic, InstrExt, Branching, BranchKind, Never};

/// Successor blocks.
pub type NextBlocks = SmallVec<[usize; 2]>;

/// A control flow: a series of basic blocks indexed `0..block_count()`, with a successor relation
/// given by `successor_blocks`. Some helper functions are also provided here.
pub trait ControlFlow {
    /// Index of the entry block.
    fn entry_block_idx(&self) -> usize;
    /// Get the total number of basic blocks in this control flow.
    fn block_count(&self) -> usize;
    /// Which blocks are following this one (in the control flow graph)?
    fn successor_blocks(&self, block_idx: usize) -> NextBlocks;
    /// Collect all the blocks reachable from the given block into an existing set.
    fn collect_reachable_into(&self, block_idx: usize, result: &mut BTreeSet<usize>) {
        if block_idx >= self.block_count() { return; }
        if result.insert(block_idx) {
            for n in self.successor_blocks(block_idx) {
                self.collect_reachable_into(n, result);
            }
        }
    }
    /// Calculate all the blocks reachable from the given block.
    fn collect_reachable(&self, block_idx: usize) -> Vec<usize> {
        let mut result = BTreeSet::new();
        self.collect_reachable_into(block_idx, &mut result);
        result.into_iter().collect()
    }
}

impl<'a, F: ControlFlow> ControlFlow for &'a F {
    fn entry_block_idx(&self) -> usize { F::entry_block_idx(self) }
    fn block_count(&self) -> usize { F::block_count(self) }
    fn successor_blocks(&self, block_idx: usize) -> NextBlocks {
        F::successor_blocks(self, block_idx)
    }
    fn collect_reachable_into(&self, block_idx: usize, result: &mut BTreeSet<usize>) {
        F::collect_reachable_into(self, block_idx, result)
    }
    fn collect_reachable(&self, block_idx: usize) -> Vec<usize> {
        F::collect_reachable(self, block_idx)
    }
}

/// More control flow related API.
pub trait ControlFlowExt: ControlFlow {
    /// The kind of the blocks in this control flow.
    type BlockKind: InstrExt;
    /// Get the block content for a given index.
    fn get_block(&self, block_idx: usize) -> &Block<Self::BlockKind>;
    /// Get the block content for the entry block, equivalent to
    /// [`get_block`](ControlFlowExt::get_block) on [`ControlFlow::entry_block_idx`].
    fn entry_block(&self) -> &Block<Self::BlockKind> {
        self.get_block(self.entry_block_idx())
    }
}

impl<'a, F: ControlFlowExt> ControlFlowExt for &'a F {
    type BlockKind = F::BlockKind;
    fn get_block(&self, block_idx: usize) -> &Block<Self::BlockKind> {
        F::get_block(self, block_idx)
    }
}

/// Reverse the control flow, and get a dual version.
pub struct Dual<F> {
    /// The original control flow.
    pub base_flow: F,
    /// The predecessor relation on the original flow, and thus the successor relation on the new.
    pub predecessors: Vec<Vec<usize>>,
}

impl<F: ControlFlow> From<F> for Dual<F> {
    fn from(base: F) -> Dual<F> {
        let n: usize = base.block_count();
        let mut predecessors = vec![BTreeSet::new(); n + 1];
        for block_idx in 0..n {
            let successors = base.successor_blocks(block_idx);
            if successors.is_empty() { predecessors[n].insert(block_idx); }
            for successor in successors {
                predecessors[successor].insert(block_idx);
            }
        }
        let predecessors = predecessors.into_iter()
            .map(|set| set.into_iter().collect_vec())
            .collect_vec();
        Dual { base_flow: base, predecessors }
    }
}

impl<F: ControlFlow> ControlFlow for Dual<F> {
    fn entry_block_idx(&self) -> usize { self.predecessors.len() - 1 }
    fn block_count(&self) -> usize { self.base_flow.block_count() }
    fn successor_blocks(&self, block_idx: usize) -> NextBlocks {
        self.predecessors[block_idx].to_smallvec()
    }
}

impl<F: ControlFlowExt> ControlFlowExt for Dual<F> {
    type BlockKind = F::BlockKind;
    fn get_block(&self, block_idx: usize) -> &Block<Self::BlockKind> {
        F::get_block(&self.base_flow, block_idx)
    }
}

/// Behaviour of a branching instruction.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct BranchingBehaviour {
    /// Whether or not the control flow might fall through to the next instruction.
    pub might_fallthrough: bool,
    /// Whether and where will the control flow branch after execution of this instruction.
    pub alternative_dest: Option<usize>,
}

impl BranchingBehaviour {
    /// Get the successor blocks for this branching behaviour.
    pub fn get_successor_blocks(self, fallthrough: usize) -> NextBlocks {
        let mut result = NextBlocks::new();
        if self.might_fallthrough { result.push(fallthrough); }
        if let Some(branch_to) = self.alternative_dest {
            result.push(branch_to);
        }
        result
    }
}

/// Indicates that this entity has a [`BranchingBehaviour`].
pub trait HasBranchingBehaviour {
    /// Get the [`BranchingBehaviour`] for this "instruction".
    fn get_branching_behaviour(&self) -> BranchingBehaviour;
}

impl<Operand> HasBranchingBehaviour for Branching<Operand> {
    fn get_branching_behaviour(&self) -> BranchingBehaviour {
        let Branching { method, dest } = self;
        let might_fallthrough = !matches!(method, BranchKind::Unconditional);
        BranchingBehaviour { might_fallthrough, alternative_dest: Some(*dest) }
    }
}

impl HasBranchingBehaviour for basic::Marker {
    fn get_branching_behaviour(&self) -> BranchingBehaviour {
        BranchingBehaviour {
            might_fallthrough: !matches!(self, basic::Marker::Ret(_)),
            alternative_dest: None,
        }
    }
}

impl HasBranchingBehaviour for Never {
    fn get_branching_behaviour(&self) -> BranchingBehaviour { match *self {} }
}

impl<K: InstrExt> HasBranchingBehaviour for Instr<K>
    where K::Branching: HasBranchingBehaviour,
          K::Marker: HasBranchingBehaviour,
          K::Extra: HasBranchingBehaviour {
    fn get_branching_behaviour(&self) -> BranchingBehaviour {
        match self {
            Instr::Branch(br) => br.get_branching_behaviour(),
            Instr::Marker(marker) => marker.get_branching_behaviour(),
            Instr::Extra(extra) => extra.get_branching_behaviour(),
            _ => BranchingBehaviour { might_fallthrough: true, alternative_dest: None },
        }
    }
}

/// Default implementation for [`ControlFlow::successor_blocks`].
///
/// Workaround for there being no specialized default methods in Rust.
pub fn successor_blocks_impl<K>(blocks: &[Block<K>], block_idx: usize) -> NextBlocks
    where K: InstrExt,
          K::Branching: HasBranchingBehaviour,
          K::Marker: HasBranchingBehaviour,
          K::Extra: HasBranchingBehaviour {
    blocks[block_idx].last_instr()
        .get_branching_behaviour()
        .get_successor_blocks(block_idx + 1)
}
