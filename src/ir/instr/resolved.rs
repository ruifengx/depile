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

//! Instructions, with inter-procedural instructions resolved, i.e. [`basic::InterProc::PushParam`]
//! and [`basic::InterProc::Call`] are merged into a single instruction [`InterProc::Call`].

use std::fmt::{Display, Formatter};
use smallvec::{SmallVec, smallvec};
use parse_display::{Display, FromStr};

use crate::ir;
use ir::instr::{basic, stripped};
use ir::instr::{HasDest, HasOperand, OutputInfo};

pub use basic::{Operand, Branching};
pub use stripped::Marker;
use crate::analysis::control_flow::{BranchingBehaviour, HasBranchingBehaviour};

/// Instruction kind "resolved".
pub type Kind = ir::instr::Kind<Operand, Branching, Marker, InterProc, Extra>;

/// [`Instr`](ir::Instr)uction with kind "resolved".
pub type Instr = ir::Instr<Kind>;

/// [`Block`](ir::Block) with kind "resolved".
pub type Block = ir::Block<Kind>;

/// [`Blocks`](ir::Blocks) with kind "resolved".
pub type Blocks = ir::Blocks<Kind>;

/// [`Function`](ir::Function) with kind "resolved".
pub type Function = ir::Function<Kind>;

/// [`Functions`](ir::Functions) with kind "resolved".
pub type Functions = ir::Functions<Kind>;

/// Inter-procedural instructions with kind "resolved".
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum InterProc {
    /// Perform a function call with a parameter list.
    Call {
        /// The target function for this function call.
        dest: usize,
        /// Parameter list for this function call.
        param_list: Vec<Operand>,
    }
}

impl Display for InterProc {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let InterProc::Call { dest, param_list } = self;
        write!(f, "call [{}]", dest)?;
        for param in param_list {
            write!(f, " {}", param)?;
        }
        Ok(())
    }
}

impl HasOperand<Operand> for InterProc {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> {
        let InterProc::Call { param_list, .. } = self;
        param_list.iter().collect()
    }
}

impl OutputInfo for InterProc {
    fn has_output(&self) -> bool { false }
}

impl HasDest for InterProc {
    fn map_dest(self, f: impl FnOnce(usize) -> usize) -> Self {
        let InterProc::Call { dest, param_list } = self;
        InterProc::Call { dest: f(dest), param_list }
    }
}

/// Extra instructions of kind "resolved".
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Extra {
    /// An extra instruction to take a snapshot of some temporary value.
    #[display("snapshot {0}")]
    Snapshot(Operand),
}

impl HasBranchingBehaviour for Extra {
    fn get_branching_behaviour(&self) -> BranchingBehaviour {
        BranchingBehaviour { might_fallthrough: true, alternative_dest: None }
    }
}

impl HasOperand<Operand> for Extra {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> {
        let Extra::Snapshot(operand) = self;
        smallvec![operand]
    }
}

impl OutputInfo for Extra {
    fn has_output(&self) -> bool { true }
}

impl HasDest for Extra {
    fn map_dest(self, _: impl FnOnce(usize) -> usize) -> Self { self }
}
