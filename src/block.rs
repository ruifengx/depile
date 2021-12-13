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

//! Basic blocks, and related API.

use itertools::Itertools;
use thiserror::Error;
use displaydoc::Display;

use crate::instr::{BranchKind, Operand};
use crate::program::SourceLine;
use super::{Instr, Program};

/// Basic block.
pub type Block = [Instr];

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
}

/// Partition the [`Program`] into basic [`Block`]s.
pub fn from_program(program: &Program) -> Result<impl Iterator<Item=&Block>, Error> {
    let n = program.len();
    let mut is_leader = vec![false; n + 1];
    is_leader[0] = true;
    is_leader[n] = true;
    for (k, instr) in program.iter().enumerate() {
        let check_operand = |xs: &[&Operand]| -> Result<(), Error> {
            for x in xs {
                if let Operand::Register(r) = x {
                    let target = &program[*r - 1];
                    match target {
                        Instr::Binary { .. } | Instr::Unary { .. }
                        | Instr::Load(_) | Instr::Move { .. } | Instr::Read(_) => {}
                        _ => return Err(Error::InvalidReference {
                            source_instr: SourceLine { index: k, instr: instr.clone() },
                            target_instr: SourceLine { index: *r, instr: target.clone() },
                        }),
                    }
                }
            }
            Ok(())
        };

        macro_rules! check {
            ($($operand : expr),+ $(,)?) => {
                check_operand(&[$($operand),+])
            }
        }

        match instr {
            Instr::Binary { lhs, rhs, .. } => check!(lhs, rhs)?,
            Instr::Unary { operand, .. } => check!(operand)?,
            Instr::Load(operand) => check!(operand)?,
            Instr::Read(operand) => check!(operand)?,
            Instr::Store { data, address } => check!(data, address)?,
            Instr::Write(operand) => check!(operand)?,
            Instr::PushParam(operand) => check!(operand)?,
            // we decide that a `call` does not partition the basic block, because control
            // flows are guaranteed to resume later.
            Instr::Branch { dest, method: BranchKind::Call } => {
                let target = &program[*dest - 1];
                if !matches!(target, Instr::EnterProc(_)) {
                    return Err(Error::CallEnterMismatch {
                        call_instr: SourceLine { index: k, instr: instr.clone() },
                        target_instr: SourceLine { index: *dest, instr: target.clone() },
                    });
                }
            }
            Instr::Branch { dest, .. } => {
                is_leader[*dest - 1] = true;
                is_leader[k + 1] = true;
            }
            Instr::EnterProc(_) => is_leader[k] = true,
            Instr::Ret(_) => is_leader[k + 1] = true,
            _ => {}
        }
    }
    Ok(is_leader.into_iter()
        .enumerate()
        .filter(|(_, p)| *p)
        .map(|(k, _)| k)
        .tuple_windows()
        .map(|(l, r)| &program[l..r]))
}

/// Print a series of basic blocks.
pub fn display_blocks<'a, I>(blocks: I) -> Result<String, std::fmt::Error>
    where I: Iterator<Item=&'a Block> {
    use std::fmt::Write;
    let mut n = 0;
    let mut res = String::new();
    for (k, block) in blocks.enumerate() {
        writeln!(res, "Block #{}:", k)?;
        for instr in block {
            n += 1;
            writeln!(res, "  instr {}: {}", n, instr)?;
        }
        writeln!(res)?;
    }
    Ok(res)
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::samples;
    use crate::program::read_program;
    use super::from_program;

    #[test]
    fn test_block_from_program() {
        let program = read_program(samples::GCD).unwrap();
        let blocks = from_program(&program).unwrap();
        assert_eq!(blocks.map(|b| b.len()).collect_vec(),
                   vec![1, 1, 2, 9, 3, 1, 33, 1]);
    }
}
