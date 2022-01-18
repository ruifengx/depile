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
//!
//! Also repurposed for block-level instructions. These are just like basic instructions, but with
//! the exceptions that all destinations in [`Branch`]ing instructions are interpreted as block
//! indices instead of instruction indices, and that the marker [`EntryPc`] shall never be used.
//!
//! [`Branch`]: crate::ir::Instr::Branch
//! [`EntryPc`]: Marker::EntryPc

use parse_display::{Display, FromStr};
use smallvec::{SmallVec, smallvec};
use crate::ir::{self, instr::{HasDest, HasOperand, OutputInfo}};

/// Instruction kind "basic".
pub type Kind = ir::instr::Kind<Operand, Branching, Marker, InterProc, Extra>;

/// [`Instr`](ir::Instr)uction with kind "basic", i.e. "raw" three-address code.
pub type Instr = ir::Instr<Kind>;

/// [`BranchKind`](ir::instr::BranchKind) with kind "basic".
pub type BranchKind = ir::instr::BranchKind<Operand>;

/// [`Branching`](ir::instr::BranchKind) instructions with kind "basic".
pub type Branching = ir::instr::Branching<Operand>;

impl HasOperand<Operand> for Branching {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> {
        match &self.method {
            BranchKind::If(operand) => smallvec![operand],
            BranchKind::Unless(operand) => smallvec![operand],
            _ => SmallVec::new(),
        }
    }
}

impl OutputInfo for Branching {
    fn has_output(&self) -> bool { false }
}

impl HasDest for Branching {
    fn map_dest(self, f: impl FnOnce(usize) -> usize) -> Self {
        Branching { dest: f(self.dest), ..self }
    }
}

/// [`Block`](ir::Block) with kind "basic".
pub type Block = ir::Block<Kind>;

/// [`Blocks`](ir::Blocks) with kind "basic".
pub type Blocks = ir::Blocks<Kind>;

/// [`Function`](ir::Function) with kind "basic".
pub type Function = ir::Function<Kind>;

/// [`Functions`](ir::Functions) with kind "basic".
pub type Functions = ir::Functions<Kind>;

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

impl HasOperand<Operand> for InterProc {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> {
        match self {
            InterProc::PushParam(operand) => smallvec![operand],
            _ => SmallVec::new(),
        }
    }
}

impl OutputInfo for InterProc {
    fn has_output(&self) -> bool { false }
}

impl HasDest for InterProc {
    fn map_dest(self, f: impl FnOnce(usize) -> usize) -> Self {
        match self {
            InterProc::Call { dest } => InterProc::Call { dest: f(dest) },
            instr => instr,
        }
    }
}

/// Operands to all the "basic" [`Instr`]uctions.
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
pub type Extra = super::Never;
