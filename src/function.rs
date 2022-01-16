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

use std::collections::{BTreeSet, HashMap};
use std::fmt::Display;
use thiserror::Error;
use smallvec::{smallvec, SmallVec};
use crate::{Instr, instr::BranchKind, Block};
use crate::instr::{basic, Branching, HasDest, stripped};

impl basic::Block {
    /// Whether or not this block is the entry to some function.
    pub fn is_function_entry(&self) -> bool {
        matches!(self.instructions[0], Instr::Marker(basic::Marker::EnterProc(_)))
    }

    /// Whether or not this block has a [`basic::Marker::Ret`] as its last instruction.
    pub fn is_function_return(&self) -> bool {
        matches!(self.instructions.last().unwrap(), Instr::Marker(basic::Marker::Ret(_)))
    }
}

/// Successor blocks.
pub enum NextBlocks {
    /// Control flow terminates here: block ends with an [`basic::Marker::Ret`].
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

impl basic::Blocks {
    /// Which blocks are following this one (in the control flow graph)?
    fn successor_blocks(&self, block_idx: usize) -> NextBlocks {
        let block = &self.blocks[block_idx];
        match block.instructions.last().unwrap() {
            Instr::Marker(basic::Marker::Ret(_)) => NextBlocks::Terminated,
            Instr::Branch(Branching { method: BranchKind::Unconditional, dest }) => NextBlocks::Continuous(*dest),
            Instr::Branch(Branching { method: BranchKind::If(_) | BranchKind::Unless(_), dest }) =>
                NextBlocks::Branching(*dest, block_idx + 1),
            _ => NextBlocks::Continuous(block_idx + 1),
        }
    }

    /// Collect all the blocks reachable from the given block into an existing set.
    fn collect_reachable_into(&self, block_idx: usize, result: &mut BTreeSet<usize>) {
        if block_idx >= self.blocks.len() { return; }
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

/// A function.
pub struct Function {
    /// Number of formal parameters.
    pub parameter_count: u64,
    /// Number of local variables.
    pub local_var_count: u64,
    /// Entry block in this function.
    pub entry_block: usize,
    /// All basic blocks in this function.
    pub blocks: Vec<stripped::Block>,
}

/// Collection of functions for a [`Program`](crate::Program).
pub struct Functions {
    /// List of functions, in ascending order for block index.
    pub functions: Vec<Function>,
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
                use Instr::Marker;
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
                    if let Instr::Branch(br) = instr {
                        *br = br.clone().map_dest(|t| *remap.get(&t).unwrap());
                    }
                }
            }
            assert_ne!(exits.len(), 0);
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
                    if let Instr::InterProc(ip) = instr {
                        *ip = ip.clone().map_dest(|t| *parent_func.get(&t).unwrap());
                    }
                }
            }
        }
        let &entry_function = parent_func.get(&self.entry_block).unwrap();
        Ok(Functions { functions, entry_function })
    }
}

impl Display for Function {
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

impl Display for Functions {
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
    use crate::instr::basic::Blocks;
    use crate::samples;
    use crate::program::read_program;

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
