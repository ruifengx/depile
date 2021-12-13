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
use super::{Instr, Program};

/// Basic block.
pub type Block = [Instr];

/// Partition the [`Program`] into basic [`Block`]s.
pub fn from_program(program: &Program) -> impl Iterator<Item=&Block> {
    let n = program.len();
    let mut is_leader = vec![false; n + 1];
    is_leader[0] = true;
    is_leader[n] = true;
    for (k, instr) in program.iter().enumerate() {
        match instr {
            Instr::Branch { dest, .. } => {
                is_leader[*dest - 1] = true;
                is_leader[k + 1] = true;
            }
            Instr::Ret(_) => is_leader[k + 1] = true,
            _ => {}
        }
    }
    is_leader.into_iter()
        .enumerate()
        .filter(|(_, p)| *p)
        .map(|(k, _)| k)
        .tuple_windows()
        .map(|(l, r)| &program[l..r])
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
        let blocks = from_program(&program);
        assert_eq!(blocks.map(|b| b.len()).collect_vec(),
                   vec![1, 1, 2, 9, 3, 13, 16, 5, 1]);
    }
}
