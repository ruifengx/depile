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

use std::fmt::Write;
use parse_display::{Display, FromStr};
use displaydoc::Display as DisplayDoc;
use thiserror::Error;

use crate::instr::Instr;
use crate::program::ParseError::InvalidIndex;

#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[display("instr {index}: {instr}")]
struct SourceLine {
    index: usize,
    instr: Instr,
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
    let mut result = String::new();
    for (instr, k) in program.iter().zip(1..) {
        writeln!(result, "instr {}: {}", k, instr)?
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use itertools::assert_equal;
    use super::{display_program, read_program};

    #[test]
    fn test_program() {
        fn test_roundtrip(source: &str) {
            let program = read_program(source).unwrap();
            let printed = display_program(&program).unwrap();
            assert_equal(source.lines().filter(|l| !l.is_empty()), printed.lines());
        }

        test_roundtrip(indoc::indoc! {r#"
            instr 1: nop
            instr 2: enter 8
            instr 3: move 0 i#-8
            instr 4: cmplt i#-8 24
            instr 5: blbc (4) [11]
            instr 6: mul i#-8 8
            instr 7: add global_array_base#32576 GP
            instr 8: add (7) (6)
            instr 9: store i#-8 (8)
            instr 10: br [4]
            instr 11: add p_base#32560 GP
            instr 12: add (11) x_offset#0
            instr 13: store 13 (12)
            instr 14: add p_base#32560 GP
            instr 15: add (14) y_offset#8
            instr 16: store 7 (15)
            instr 17: ret 0

            instr 18: enter 24
            instr 19: mul 0 8
            instr 20: add local_array_base#-24 FP
            instr 21: add (20) (19)
            instr 22: store a#24 (21)
            instr 23: mul 1 8
            instr 24: add local_array_base#-24 FP
            instr 25: add (24) (23)
            instr 26: store b#16 (25)
            instr 27: mul 2 8
            instr 28: add local_array_base#-24 FP
            instr 29: add (28) (27)
            instr 30: add a#24 b#16
            instr 31: store (30) (29)
            instr 32: mul 2 8
            instr 33: add global_array_base#32576 GP
            instr 34: add (33) (32)
            instr 35: load (34)
            instr 36: cmple (35) a#24
            instr 37: blbs (36) [46]
            instr 38: mul 3 8
            instr 39: add global_array_base#32576 GP
            instr 40: add (39) (38)
            instr 41: add p_base#32560 GP
            instr 42: add (41) y_offset#8
            instr 43: load (42)
            instr 44: add b#16 (43)
            instr 45: store (44) (40)
            instr 46: add p_base#32560 GP
            instr 47: add (46) x_offset#0
            instr 48: mod a#24 3
            instr 49: mul (48) 8
            instr 50: add local_array_base#-24 FP
            instr 51: add (50) (49)
            instr 52: load (51)
            instr 53: store (52) (47)
            instr 54: ret 16
            instr 55: nop
        "#});
    }
}
