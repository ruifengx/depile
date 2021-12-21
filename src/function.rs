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
use either::Either;
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
pub type SuccBlocks = Either<[usize; 1], [usize; 2]>;

/// Any program structure with a control flow.
pub trait ControlFlow {
    /// Get all the blocks as a slice.
    fn blocks(&self) -> &[Block];
    /// To which block this instruction index belongs?
    fn parent_block_of(&self, entry: usize) -> usize;

    /// Which blocks are following this one (in the control flow graph)?
    fn successor_blocks(&self, block: &Block) -> SuccBlocks {
        match block.instructions.last().unwrap() {
            Instr::Branch { method: BranchKind::Unconditional, dest } => Either::Left([*dest]),
            Instr::Branch { method: BranchKind::If(_) | BranchKind::Unless(_), dest } =>
                Either::Right([*dest, self.parent_block_of(block.last_index() + 1)]),
            _ => Either::Left([self.parent_block_of(block.last_index() + 1)]),
        }
    }

    /// Collect all the blocks reachable from the given block into an existing set.
    fn collect_reachable_into(&self, entry: usize, result: &mut BTreeSet<usize>) {
        let k = self.parent_block_of(entry);
        let block = self.blocks()[k];
        result.insert(k);
        match block.instructions.last().unwrap() {
            Instr::Branch { method: BranchKind::Unconditional, dest } =>
                self.collect_reachable_into(*dest, result),
            Instr::Branch { method: BranchKind::If(_) | BranchKind::Unless(_), dest } => {
                self.collect_reachable_into(*dest, result);
                let fallthrough = self.parent_block_of(block.last_index() + 1);
                self.collect_reachable_into(fallthrough, result);
            }
            _ => {
                let fallthrough = self.parent_block_of(block.last_index() + 1);
                self.collect_reachable_into(fallthrough, result);
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

impl<'a> ControlFlow for Blocks<'a> {
    fn blocks(&self) -> &[Block] { &self.blocks }
    fn parent_block_of(&self, instr_idx: usize) -> usize {
        self.blocks.partition_point(|block| block.index_range().contains(&instr_idx))
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
