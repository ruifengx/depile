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

//! Basic instructions for "raw" three-address code, with 1-1 correspondence to valid input texts.

use std::fmt::Display;
use parse_display::{Display, FromStr};

/// [`Instr`](crate::Instr)uction with kind "basic", i.e. "raw" three-address code.
pub type Instr = crate::Instr<Operand, Marker, InterProc, Extra>;

/// [`BranchKind`](crate::instr::BranchKind) with kind "basic".
pub type BranchKind = crate::instr::BranchKind<Operand>;

/// [`Block`](crate::Block) with kind "basic".
pub type Block = crate::Block<Operand, Marker, InterProc, Extra>;

/// [`Blocks`](crate::block::Blocks) with kind "basic".
pub type Blocks = crate::block::Blocks<Operand, Marker, InterProc, Extra>;

/// Basic inter-procedural instructions.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum InterProc {
    /// Push actual parameters for later use in [`InterProc::Call`].
    #[display("param {0}")]
    PushParam(Operand),
    /// Perform a function call.
    #[display("call [{dest}]")]
    Call {
        /// Destination for the function call.
        dest: usize
    },
}

/// Operands to all the [`Basic`] [`Instr`]uctions.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Operand {
    /// Global pointer.
    GP,
    /// Frame pointer.
    FP,
    /// Integer literal.
    #[display("{0}")]
    Const(i64),
    /// Global offset, field offset, or stack offset.
    #[display("{0}#{1}")]
    Offset(String, i64),
    /// Virtual register for instruction outputs.
    #[display("({0})")]
    Register(usize),
}

/// Kind "basic" have some markups.
#[derive(Debug, Display, FromStr, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Marker {
    /// Denotes the beginning of the `main` function.
    #[display(style = "lowercase")]
    EntryPc,
    /// Denotes a function return. Its operand `{0}` specifies the amount of memory for formal
    /// parameters that needs to be removed (popped) from the stack.
    #[display("ret {0}")]
    Ret(u64),
    /// Denotes the beginning of a function. Its operand `{0}` specifies the amount of memory in
    /// bytes to be allocated on the stack frame for local variables of that function.
    #[display("enter {0}")]
    EnterProc(u64),
}

/// Kind "basic" have no extra instructions.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Extra {}

impl std::str::FromStr for Extra {
    type Err = ();
    fn from_str(_: &str) -> Result<Self, Self::Err> { Err(()) }
}

impl Display for Extra {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {}
    }
}
