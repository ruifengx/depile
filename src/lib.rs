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

//! Translate three-address code back to C code.
//!
//! Specification of input format

#![warn(missing_docs)]

pub mod instr;
pub mod program;
pub mod block;
pub mod function;

#[cfg(feature = "cli")]
pub mod cli;

#[cfg(feature = "cli")]
pub use cli::Cli;

#[cfg(test)]
mod samples;

pub use instr::Instr;
pub use program::Program;
pub use block::{Block, Blocks};
pub use function::{Function, ControlFlow};
