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
use smallvec::{SmallVec, smallvec};
use crate::ir::{Block, Instr};
use crate::ir::instr::{basic, InstrExt, Branching, BranchKind, Never};

/// Successor blocks.
pub enum NextBlocks {
    /// Control flow terminates here: block ends with an [`basic::Marker::Ret`].
    Terminated,
    /// Control flow is continuous: block ends with an unconditional branch, or a normal instruction.
    Continuous(usize),
    /// Control flow branches here: block ends with a conditional branch.
    Branching {
        /// If the condition is not satisfied, the control flow falls through to this block.
        fallthrough: usize,
        /// If the condition is satisfied, the control flow branches to this block.
        branch_to: usize,
    },
}

impl IntoIterator for NextBlocks {
    type Item = usize;
    type IntoIter = smallvec::IntoIter<[usize; 2]>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            NextBlocks::Terminated => SmallVec::new(),
            NextBlocks::Continuous(m) => smallvec![m],
            NextBlocks::Branching { fallthrough: m, branch_to: n } => smallvec![m, n],
        }.into_iter()
    }
}

/// A control flow: a series of basic blocks indexed `0..block_count()`, with a successor relation
/// given by `successor_blocks`. Some helper functions are also provided here.
pub trait ControlFlow {
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
        use NextBlocks::*;
        match self.alternative_dest {
            Some(branch_to) if self.might_fallthrough => Branching { fallthrough, branch_to },
            Some(branch_to) => Continuous(branch_to),
            None if self.might_fallthrough => Continuous(fallthrough),
            None => Terminated,
        }
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
    blocks[block_idx]
        .instructions.last().unwrap()
        .get_branching_behaviour()
        .get_successor_blocks(block_idx + 1)
}
