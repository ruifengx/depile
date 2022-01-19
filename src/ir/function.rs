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

//! Reconstruct functions from basic blocks.

use std::collections::HashMap;
use std::fmt::Display;
use thiserror::Error;
use crate::analysis::control_flow::{ControlFlow, ControlFlowExt, HasBranchingBehaviour, NextBlocks, successor_blocks_impl};
use crate::ir::{Instr::*, Block};
use crate::ir::instr::{basic, stripped, HasDest, InstrExt};

impl basic::Block {
    /// Whether or not this block is the entry to some function.
    pub fn is_function_entry(&self) -> bool {
        matches!(self.instructions[0], Marker(basic::Marker::EnterProc(_)))
    }

    /// Whether or not this block has a [`basic::Marker::Ret`] as its last instruction.
    pub fn is_function_return(&self) -> bool {
        matches!(self.last_instr(), Marker(basic::Marker::Ret(_)))
    }
}

impl ControlFlow for basic::Blocks {
    fn entry_block_idx(&self) -> usize { self.entry_block }
    fn block_count(&self) -> usize { self.blocks.len() }
    fn successor_blocks(&self, block_idx: usize) -> NextBlocks {
        successor_blocks_impl(&self.blocks, block_idx)
    }
}

impl ControlFlowExt for basic::Blocks {
    type BlockKind = basic::Kind;
    fn get_block(&self, block_idx: usize) -> &basic::Block { &self.blocks[block_idx] }
}

/// A function.
pub struct Function<K: InstrExt = stripped::Kind> {
    /// Number of formal parameters.
    pub parameter_count: u64,
    /// Number of local variables.
    pub local_var_count: u64,
    /// Entry block in this function.
    pub entry_block: usize,
    /// All basic blocks in this function.
    pub blocks: Vec<Block<K>>,
}

impl<K: InstrExt> ControlFlow for Function<K>
    where K::Branching: HasBranchingBehaviour,
          K::Marker: HasBranchingBehaviour,
          K::Extra: HasBranchingBehaviour {
    fn entry_block_idx(&self) -> usize { self.entry_block }
    fn block_count(&self) -> usize { self.blocks.len() }
    fn successor_blocks(&self, block_idx: usize) -> NextBlocks {
        successor_blocks_impl(&self.blocks, block_idx)
    }
}

impl<K: InstrExt> ControlFlowExt for Function<K>
    where K::Branching: HasBranchingBehaviour,
          K::Marker: HasBranchingBehaviour,
          K::Extra: HasBranchingBehaviour {
    type BlockKind = K;
    fn get_block(&self, block_idx: usize) -> &Block<K> { &self.blocks[block_idx] }
}

/// Collection of functions for a [`Program`](super::Program).
pub struct Functions<K: InstrExt = stripped::Kind> {
    /// List of functions, in ascending order for block index.
    pub functions: Vec<Function<K>>,
    /// The index of the entry function (i.e. `main`).
    ///
    /// This `main` function has its first instruction of its entry block preceded by `entrypc`
    /// (in other words, it is marked as the entry point for the whole program).
    pub entry_function: usize,
}

/// Program validation error during conversion to a series of basic blocks.
#[derive(Debug, Error)]
pub enum Error {
    /// Multiple [`basic::Marker::EnterProc`] instructions in one function.
    OverlappingProcs(Vec<(usize, u64)>),
    /// Multiple [`basic::Marker::Ret`] instructions don't agree with each other on number of arguments.
    InconsistentRets(Vec<(usize, u64)>),
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::OverlappingProcs(entries) => {
                writeln!(f, "multiple `enter` instructions in one function:")?;
                for (k, local_bytes) in entries {
                    write!(f, "- instr {}: enter {}", k, local_bytes)?;
                    if local_bytes % 8 != 0 {
                        writeln!(f, " (not a multiple of 8)")?;
                    } else {
                        writeln!(f)?;
                    }
                }
            }
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

impl basic::Blocks {
    /// Split the basic blocks into functions.
    pub fn functions(&self) -> Result<Functions, Error> {
        let mut functions = Vec::new();
        let mut parent_func = HashMap::new();
        for (entry, orig_blocks) in self.blocks.iter().cloned()
            .enumerate()
            .filter(|(_, block)| block.is_function_entry())
            .map(|(k, _)| (k, self.collect_reachable(k))) {
            parent_func.insert(entry, functions.len());
            let mut remap = HashMap::new();
            let mut blocks = Vec::new();
            let mut entries = Vec::new();
            let mut exits = Vec::new();
            for block in orig_blocks {
                use basic::Marker::{EnterProc, Ret};
                remap.insert(block, blocks.len());
                let block = &self.blocks[block];
                let first_index = block.first_index;
                let mut instrs = block.instructions.as_ref();
                if let [Marker(EnterProc(k)), ..] = instrs {
                    entries.push((block.first_index, *k));
                    instrs = instrs.split_first().unwrap().1
                }
                if let [.., Marker(Ret(k))] = instrs {
                    exits.push((block.last_index(), *k));
                    instrs = instrs.split_last().unwrap().1
                }
                let block: stripped::Block = Block {
                    instructions: instrs.iter()
                        .map(|instr| instr.clone().map_kind(
                            std::convert::identity,
                            std::convert::identity,
                            std::convert::identity,
                            |m| panic!("m: {}", m),
                            std::convert::identity,
                        )).collect(),
                    first_index,
                };
                blocks.push(block);
            }
            for block in &mut blocks {
                for instr in block.instructions.as_mut() {
                    if let Branch(br) = instr {
                        *br = br.clone().map_dest(|t| *remap.get(&t).unwrap());
                    }
                }
            }
            assert!(!entries.is_empty());
            assert!(!exits.is_empty());
            let (_, local_bytes) = entries[0];
            let (_, parameter_bytes) = exits[0];
            if !entries.iter().all(|&(_, k)| k == local_bytes && k % 8 == 0) {
                return Err(Error::OverlappingProcs(entries));
            } else if !exits.iter().all(|&(_, k)| k == parameter_bytes && k % 8 == 0) {
                return Err(Error::InconsistentRets(exits));
            } else {
                let local_var_count = local_bytes / 8;
                let parameter_count = parameter_bytes / 8;
                let &entry_block = remap.get(&entry).unwrap();
                functions.push(Function { parameter_count, local_var_count, entry_block, blocks });
            }
        }
        for func in &mut functions {
            for block in &mut func.blocks {
                for instr in block.instructions.as_mut() {
                    if let InterProc(ip) = instr {
                        *ip = ip.clone().map_dest(|t| *parent_func.get(&t).unwrap());
                    }
                }
            }
        }
        let &entry_function = parent_func.get(&self.entry_block).unwrap();
        Ok(Functions { functions, entry_function })
    }
}

impl<K: InstrExt> Display for Function<K>
    where K::Operand: Display,
          K::Branching: Display,
          K::Marker: Display,
          K::InterProc: Display,
          K::Extra: Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "#parameters = {}", self.parameter_count)?;
        writeln!(f, "#local_vars = {}", self.local_var_count)?;
        writeln!(f)?;
        for (k, block) in self.blocks.iter().enumerate() {
            if k == self.entry_block { write!(f, "(ENTRY) ")?; }
            writeln!(f, "Block #{}:", k)?;
            writeln!(f, "{}", block)?;
        }
        Ok(())
    }
}

impl<K: InstrExt> Display for Functions<K>
    where K::Operand: Display,
          K::Branching: Display,
          K::Marker: Display,
          K::InterProc: Display,
          K::Extra: Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, func) in self.functions.iter().enumerate() {
            if k == self.entry_function { write!(f, "(ENTRY) ")?; }
            writeln!(f, "Function #{}:", k)?;
            writeln!(f, "{}", func)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::instr::basic::Blocks;
    use crate::samples;
    use crate::ir::program::read_program;

    #[test]
    fn test_blocks_into_functions() {
        for input in samples::ALL_SAMPLES {
            let program = read_program(input).unwrap();
            let blocks = Blocks::try_from(program.as_ref()).unwrap();
            let functions = blocks.functions().unwrap();
            // to avoid optimizations messing up our tests
            assert!(!functions.functions.is_empty());
        }
    }
}
