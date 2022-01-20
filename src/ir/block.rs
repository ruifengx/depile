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

//! Basic blocks, and related API.

use std::fmt::{Debug, Display};
use itertools::Itertools;
use thiserror::Error;
use displaydoc::Display;
use derivative::Derivative;

use crate::ir::instr::{Instr, basic, Branching, HasDest, HasOperand, InstrExt, OutputInfo};
use crate::ir::program::{Program, SourceLine};

/// Basic block.
#[derive(Derivative)]
#[derivative(Debug(bound = "K::Operand: Debug, K::Branching: Debug, K::Marker: Debug, K::InterProc: Debug, K::Extra: Debug"))]
#[derivative(Clone(bound = "K::Operand: Clone, K::Branching: Clone, K::Marker: Clone, K::InterProc: Clone, K::Extra: Clone"))]
#[derivative(Eq(bound = "K::Operand: Eq, K::Branching: Eq, K::Marker: Eq, K::InterProc: Eq, K::Extra: Eq"))]
#[derivative(PartialEq(bound = "K::Operand: PartialEq, K::Branching: PartialEq, K::Marker: PartialEq, K::InterProc: PartialEq, K::Extra: PartialEq"))]
pub struct Block<K: InstrExt> {
    /// Index of the first instruction.
    pub first_index: usize,
    /// All the instructions in this basic block.
    pub instructions: Box<[Instr<K>]>,
}

/// Iterator of indexed instructions into a block.
pub type IndexedInstr<'a, K> = std::iter::Zip<
    std::ops::RangeFrom<usize>,
    std::slice::Iter<'a, Instr<K>>,
>;

impl<K: InstrExt> Block<K> {
    /// Index of the last instruction.
    pub fn last_index(&self) -> usize {
        self.first_index + self.instructions.len() - 1
    }
    /// Range of indices of instructions in this block.
    pub fn index_range(&self) -> std::ops::Range<usize> {
        self.first_index..self.first_index + self.instructions.len()
    }
    /// Get iterator into instructions with indices.
    pub fn indexed(&self) -> IndexedInstr<K> {
        (self.first_index..).zip(self.instructions.iter())
    }
    /// The first instruction in this block.
    pub fn first_instr(&self) -> &Instr<K> { self.instructions.first().unwrap() }
    /// The last instruction in this block.
    pub fn last_instr(&self) -> &Instr<K> { self.instructions.last().unwrap() }
}

impl<K: InstrExt> Display for Block<K>
    where K::Operand: Display,
          K::Branching: Display,
          K::Marker: Display,
          K::InterProc: Display,
          K::Extra: Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, instr) in self.indexed() {
            writeln!(f, "  instr {}: {}", k, instr)?;
        }
        Ok(())
    }
}

/// Program validation error during conversion to a series of basic blocks.
#[derive(Debug, Display, Error)]
pub enum Error {
    /**
     * invalid function call:
     * - found this `call` instruction:     {call_instr}
     * - but its target is not an `enter`:  {target_instr}
     */
    #[allow(missing_docs)]
    CallEnterMismatch {
        call_instr: SourceLine,
        target_instr: SourceLine,
    },
    /**
     * invalid reference to register:
     * - this instruction accesses a return value:      {source_instr}
     * - but the target instruction does not have one:  {target_instr}
     */
    InvalidReference {
        /// The offending instruction (which attempts to read a register).
        source_instr: SourceLine,
        /// Return value of this instruction is undefined.
        target_instr: SourceLine,
    },
    /**
     * invalid `entrypc` instruction: {entry_instr}
     * - it should be directly followed by an `enter` instruction
     * - but we got this instruction instead:  {following_instr}
     */
    InvalidEntry {
        /// The `entrypc` instruction in discussion.
        entry_instr: SourceLine,
        /// The following instruction, expected to be an `enter`.
        following_instr: SourceLine,
    },
    /// no entry point found.
    NoEntryPoint,
    /// found multiple `entrypc` instructions: {0:?}.
    MultipleEntries(Vec<usize>),
}

/// Collection of basic blocks for a [`Program`].
#[derive(Derivative)]
#[derivative(Debug(bound = "K::Operand: Debug, K::Branching: Debug, K::Marker: Debug, K::InterProc: Debug, K::Extra: Debug"))]
#[derivative(Clone(bound = "K::Operand: Clone, K::Branching: Clone, K::Marker: Clone, K::InterProc: Clone, K::Extra: Clone"))]
#[derivative(Eq(bound = "K::Operand: Eq, K::Branching: Eq, K::Marker: Eq, K::InterProc: Eq, K::Extra: Eq"))]
#[derivative(PartialEq(bound = "K::Operand: PartialEq, K::Branching: PartialEq, K::Marker: PartialEq, K::InterProc: PartialEq, K::Extra: PartialEq"))]
pub struct Blocks<K: InstrExt> {
    /// List of basic blocks, in ascending order for instruction index.
    pub blocks: Vec<Block<K>>,
    /// The index of the entry block (marked as `entrypc`).
    pub entry_block: usize,
}

impl<'a> TryFrom<&'a Program> for basic::Blocks {
    type Error = Error;
    /// Partition the [`Program`] into basic [`Block`]s.
    fn try_from(program: &Program) -> Result<basic::Blocks, Error> {
        let n = program.len();
        let mut is_leader = vec![false; n + 1];
        is_leader[0] = true;
        is_leader[n] = true;

        let mut entries = Vec::new();
        for (k, instr) in program.iter().enumerate() {
            for x in instr.get_operands() {
                if let basic::Operand::Register(r) = x {
                    let target = &program[*r - 1];
                    if !target.has_output() {
                        return Err(Error::InvalidReference {
                            source_instr: SourceLine { index: k, instr: instr.clone() },
                            target_instr: SourceLine { index: *r, instr: target.clone() },
                        });
                    }
                }
            }

            match instr {
                // validate `entrypc`
                Instr::Marker(basic::Marker::EntryPc) => {
                    entries.push(k);
                    is_leader[k] = true;
                    let next = &program[k + 1];
                    if !matches!(next, Instr::Marker(basic::Marker::EnterProc(_))) {
                        return Err(Error::InvalidEntry {
                            entry_instr: SourceLine { index: k, instr: instr.clone() },
                            following_instr: SourceLine { index: k, instr: next.clone() },
                        });
                    }
                }
                // we decide that a `call` does not partition the basic block, because control
                // flows are guaranteed to resume later.
                Instr::InterProc(basic::InterProc::Call { dest }) => {
                    let target = &program[*dest - 1];
                    if !matches!(target, Instr::Marker(basic::Marker::EnterProc(_))) {
                        return Err(Error::CallEnterMismatch {
                            call_instr: SourceLine { index: k, instr: instr.clone() },
                            target_instr: SourceLine { index: *dest, instr: target.clone() },
                        });
                    }
                }
                Instr::Branch(Branching { dest, .. }) => {
                    is_leader[*dest - 1] = true;
                    is_leader[k + 1] = true;
                }
                Instr::Marker(basic::Marker::EnterProc(_)) => is_leader[k] = true,
                Instr::Marker(basic::Marker::Ret(_)) => is_leader[k + 1] = true,
                _ => {}
            }
        }
        if entries.is_empty() { return Err(Error::NoEntryPoint); }
        if entries.len() > 1 { return Err(Error::MultipleEntries(entries)); }
        assert!(is_leader[entries[0]] && is_leader[entries[0] + 1]);

        let ranges = is_leader.iter().copied()
            .enumerate()
            .filter(|(_, p)| *p)
            .map(|(k, _)| k)
            .tuple_windows::<(usize, usize)>()
            .collect_vec();

        Ok(Blocks {
            blocks: ranges.iter().copied()
                .map(|(l, r)| Block {
                    instructions: program[l..r].iter().cloned()
                        .map(|instr| instr.map_dest(|dest|
                            ranges.partition_point(|(_, r)| *r < dest)))
                        .collect_vec()
                        .into_boxed_slice(),
                    first_index: l + 1,
                }).collect(),
            entry_block: 1 + is_leader.iter().copied()
                .take(entries[0])
                .filter(|&p| p)
                .count(),
        })
    }
}

impl<K: InstrExt> Display for Blocks<K>
    where K::Operand: Display,
          K::Branching: Display,
          K::Marker: Display,
          K::InterProc: Display,
          K::Extra: Display {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (k, block) in self.blocks.iter().enumerate() {
            if k == self.entry_block { write!(f, "(ENTRY) ")?; }
            writeln!(f, "Block #{}:", k)?;
            writeln!(f, "{}", block)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::Blocks;
    use crate::samples;
    use crate::ir::program::read_program;

    #[test]
    fn test_blocks_from_program() {
        for input in samples::ALL_SAMPLES {
            let program = read_program(input).unwrap();
            let blocks = Blocks::try_from(program.as_ref()).unwrap();
            // to avoid optimizations messing up our tests
            assert!(!blocks.blocks.is_empty());
        }
    }
}
