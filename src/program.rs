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

//! Three-address programs.

use parse_display::{Display, FromStr};
use displaydoc::Display as DisplayDoc;
use thiserror::Error;

use crate::instr::Instr;
use crate::program::ParseError::InvalidIndex;

/// A single line in the source program.
///
/// Only used internally and in error messages.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[display("instr {index}: {instr}")]
pub struct SourceLine {
    /// A line index `k` as in `instr k:`.
    pub index: usize,
    /// The instruction.
    pub instr: Instr,
}

/// Parse error for [`Program`]s.
#[derive(Debug, DisplayDoc, Error)]
pub enum ParseError {
    /// invalid index for instruction: expected {expected}, got {actual}
    InvalidIndex {
        /// expected index according to the position of this instruction.
        expected: usize,
        /// actual index specified with the `instr k:` syntax.
        actual: usize,
    },
    /// invalid instruction: {0}
    InvalidInstr(#[from] parse_display::ParseError),
}

/// A program is a series of [`Instr`]uctions.
pub type Program = [Instr];

/// Read from source text to a [`Program`].
pub fn read_program(text: &str) -> Result<Box<Program>, ParseError> {
    text.lines()
        .filter(|line| !line.is_empty())
        .map(str::trim)
        .map(str::parse::<SourceLine>)
        .zip(1..)
        .map(|(line, k)| {
            let SourceLine { index, instr } = line?;
            if k != index { return Err(InvalidIndex { expected: k, actual: index }); }
            Ok(instr)
        })
        .collect()
}

/// Print the [`Program`] as source text.
pub fn display_program(program: &Program) -> Result<String, core::fmt::Error> {
    use std::fmt::Write;
    let mut result = String::new();
    for (instr, k) in program.iter().zip(1..) {
        writeln!(result, "instr {}: {}", k, instr)?
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;

    use crate::samples;
    use super::{display_program, read_program};

    #[test]
    fn test_program() {
        fn test_roundtrip(source: &str) {
            let program = read_program(source).unwrap();
            let printed = display_program(&program).unwrap();
            assert_equal(source.lines().filter(|l| !l.is_empty()), printed.lines());
        }
        test_roundtrip(samples::SIMPLE);
    }
}
