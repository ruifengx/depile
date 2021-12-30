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
use itertools::Itertools;
use thiserror::Error;
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
pub trait ControlFlow<'a> {
    /// Get all blocks in this control flow.
    fn blocks<'r>(&'r self) -> Box<dyn Iterator<Item=&'r Block> + 'r> where 'a: 'r;
    /// Get all the blocks as a slice.
    fn all_blocks(&self) -> &[Block];
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
        if k >= self.all_blocks().len() { return; }
        if result.insert(k) {
            for n in self.successor_blocks(self.all_blocks()[k]) {
                self.collect_reachable_into(n, result);
            }
        }
    }

    /// Calculate all the blocks reachable from the given block.
    fn collect_reachable(&self, block_idx: usize) -> Vec<usize> {
        let mut result = BTreeSet::new();
        let instr_idx = self.all_blocks()[block_idx].first_index + 1;
        self.collect_reachable_into(instr_idx, &mut result);
        result.into_iter().collect()
    }
}

impl<'a> ControlFlow<'a> for Blocks<'a> {
    fn blocks<'r>(&'r self) -> Box<dyn Iterator<Item=&'r Block> + 'r>
        where 'a: 'r { Box::new(self.blocks.iter()) }
    fn all_blocks(&self) -> &[Block] { &self.blocks }
    fn parent_block_of(&self, instr_idx: usize) -> usize {
        self.blocks.partition_point(|block| block.first_index + 1 < instr_idx)
    }
}

/// A function.
pub struct Function<'a> {
    /// Number of formal parameters.
    pub parameter_count: u64,
    /// All the basic blocks in the whole program.
    pub all_blocks: &'a Blocks<'a>,
    /// All relevant basic blocks in this function.
    pub relevant_blocks: Vec<usize>,
}

impl<'a> ControlFlow<'a> for Function<'a> {
    fn blocks<'r>(&'r self) -> Box<dyn Iterator<Item=&'r Block> + 'r> where 'a: 'r {
        Box::new(self.relevant_blocks
            .iter().copied()
            .map(|k| &self.all_blocks()[k]))
    }
    fn all_blocks(&self) -> &[Block] { self.all_blocks.all_blocks() }
    fn parent_block_of(&self, entry: usize) -> usize { self.all_blocks.parent_block_of(entry) }
}

/// Program validation error during conversion to a series of basic blocks.
#[derive(Debug, Error)]
pub enum Error {
    /// Multiple [`Instr::Ret`] instructions don't agree with each other on number of arguments.
    InconsistentRets(Vec<(usize, u64)>),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::InconsistentRets(rets) => {
                writeln!(f, "inconsistent `ret` instructions:")?;
                for (k, arg_bytes) in rets {
                    write!(f, "- instr {}: ret {}", k, arg_bytes)?;
                    if arg_bytes % 8 != 0 {
                        writeln!(f, " (not a multiple of 8)")?;
                    } else {
                        writeln!(f)?;
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'a> Blocks<'a> {
    /// Split the basic blocks into functions.
    pub fn functions(&self) -> Result<Vec<Function>, Error> {
        self.blocks.iter().copied()
            .enumerate()
            .filter(|(_, block)| block.is_function_entry())
            .map(|(k, _)| Function {
                parameter_count: 0, // to be changed
                all_blocks: self,
                relevant_blocks: self.collect_reachable(k),
            })
            .map(|func| {
                let ks = func.blocks()
                    .map(|block| block.indexed_instructions().last().unwrap())
                    .filter_map(|instr| match instr {
                        (k, Instr::Ret(n_args)) => Some((k, *n_args)),
                        _ => None,
                    }).collect_vec();
                assert_ne!(ks.len(), 0);
                let (_, parameter_bytes) = ks[0];
                if ks.iter().all(|&(_, k)| k == parameter_bytes && k % 8 == 0) {
                    let parameter_count = parameter_bytes / 8;
                    Ok(Function { parameter_count, ..func })
                } else {
                    Err(Error::InconsistentRets(ks))
                }
            })
            .collect()
    }
}

impl<'a> std::fmt::Display for Function<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Function with {} parameters:", self.parameter_count)?;
        for &k in &self.relevant_blocks {
            writeln!(f, "Block #{}:", k)?;
            writeln!(f, "{}", self.all_blocks.blocks[k])?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Blocks;
    use crate::samples;
    use crate::program::read_program;

    #[test]
    fn test_blocks_into_functions() {
        for input in samples::ALL_SAMPLES {
            let program = read_program(input).unwrap();
            let blocks = Blocks::try_from(program.as_ref()).unwrap();
            let functions = blocks.functions().unwrap();
            // to avoid optimizations messing up our tests
            assert!(!functions.is_empty());
        }
    }
}
