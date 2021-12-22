/*
 * depile: translate three-address code back to C code.
 * Copyright (C) 2021  Ruifeng Xie
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

//! Reconstruct functions from basic blocks.

use std::collections::BTreeSet;
use smallvec::{smallvec, SmallVec};
use crate::{Instr, instr::BranchKind, Block, Blocks};

impl<'a> Block<'a> {
    /// Whether or not this block is the entry to some function.
    pub fn is_function_entry(self) -> bool {
        matches!(self.instructions[0], Instr::EnterProc(_))
    }

    /// Whether or not this block has a [`Instr::Ret`] as its last instruction.
    pub fn is_function_return(self) -> bool {
        matches!(self.instructions.last().unwrap(), Instr::Ret(_))
    }
}

/// Successor blocks.
pub enum NextBlocks {
    /// Control flow terminates here: block ends with an [`Instr::Ret`].
    Terminated,
    /// Control flow is continuous: block ends with an unconditional branch, or a normal instruction.
    Continuous(usize),
    /// Control flow branches here: block ends with a conditional branch.
    Branching(usize, usize),
}

impl IntoIterator for NextBlocks {
    type Item = usize;
    type IntoIter = smallvec::IntoIter<[usize; 2]>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            NextBlocks::Terminated => SmallVec::new(),
            NextBlocks::Continuous(m) => smallvec![m],
            NextBlocks::Branching(m, n) => smallvec![m, n],
        }.into_iter()
    }
}

/// Any program structure with a control flow.
pub trait ControlFlow {
    /// Get all the blocks as a slice.
    fn blocks(&self) -> &[Block];
    /// To which block this instruction index belongs?
    fn parent_block_of(&self, entry: usize) -> usize;

    /// Which blocks are following this one (in the control flow graph)?
    fn successor_blocks(&self, block: Block) -> NextBlocks {
        match block.instructions.last().unwrap() {
            Instr::Ret(_) => NextBlocks::Terminated,
            Instr::Branch { method: BranchKind::Unconditional, dest } => NextBlocks::Continuous(*dest),
            Instr::Branch { method: BranchKind::If(_) | BranchKind::Unless(_), dest } =>
                NextBlocks::Branching(*dest, block.last_index() + 1 + 1),
            _ => NextBlocks::Continuous(block.last_index() + 1 + 1),
        }
    }

    /// Collect all the blocks reachable from the given block into an existing set.
    fn collect_reachable_into(&self, entry: usize, result: &mut BTreeSet<usize>) {
        let k = self.parent_block_of(entry);
        if k >= self.blocks().len() { return; }
        if result.insert(k) {
            for n in self.successor_blocks(self.blocks()[k]) {
                self.collect_reachable_into(n, result);
            }
        }
    }

    /// Calculate all the blocks reachable from the given block.
    fn collect_reachable(&self, block_idx: usize) -> Vec<usize> {
        let mut result = BTreeSet::new();
        let instr_idx = self.blocks()[block_idx].first_index + 1;
        self.collect_reachable_into(instr_idx, &mut result);
        result.into_iter().collect()
    }
}

impl<'a> ControlFlow for Blocks<'a> {
    fn blocks(&self) -> &[Block] { &self.blocks }
    fn parent_block_of(&self, instr_idx: usize) -> usize {
        self.blocks.partition_point(|block| block.first_index + 1 < instr_idx)
    }
}

/// A function.
pub struct Function<'a> {
    /// All the basic blocks in the whole program.
    pub all_blocks: &'a Blocks<'a>,
    /// All relevant basic blocks in this function.
    pub relevant_blocks: Vec<usize>,
}

impl<'a> ControlFlow for Function<'a> {
    fn blocks(&self) -> &[Block] { self.all_blocks.blocks() }
    fn parent_block_of(&self, entry: usize) -> usize { self.all_blocks.parent_block_of(entry) }
}

impl<'a> Blocks<'a> {
    /// Split the basic blocks into functions.
    pub fn functions(&self) -> Vec<Function> {
        self.blocks.iter().copied()
            .enumerate()
            .filter(|(_, block)| block.is_function_entry())
            .map(|(k, _)| Function {
                all_blocks: self,
                relevant_blocks: self.collect_reachable(k),
            })
            .collect()
    }
}

impl<'a> std::fmt::Display for Function<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for &k in &self.relevant_blocks {
            writeln!(f, "Block #{}:", k)?;
            writeln!(f, "{}", self.all_blocks.blocks[k])?;
        }
        Ok(())
    }
}
