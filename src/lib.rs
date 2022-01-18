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

#![doc = include_str!("../README.md")]

//! ## Input Specification
//!
//! Input is handled per line. Lines are trimmed, and empty lines are filtered out.
//!
//! Every line starts with a header indicating the instruction index, followed by the instruction:
//! ```csc-output
//! instr 14: add res_base#32744 GP
//! ```
//! Instructions are parsed into [`ir::Instr`]s structurally.

#![warn(missing_docs)]

pub mod ir;
pub mod analysis;

#[cfg(feature = "cli")]
pub mod cli;

#[cfg(feature = "cli")]
pub use cli::Cli;

#[cfg(test)]
mod samples;
