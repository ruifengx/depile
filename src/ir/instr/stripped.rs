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

//! Stripped instructions for use in [`Function`](ir::Function)s.

use crate::ir;
use parse_display::{Display, FromStr};
use crate::analysis::control_flow::{BranchingBehaviour, HasBranchingBehaviour};

/// Kind "stripped" use the same operand, as well as the same branching, inter-procedural, and
/// extra instructions as kind "basic".
pub use super::basic::{Operand, Branching, InterProc, Extra};

/// Instruction kind "stripped".
pub type Kind = ir::instr::Kind<Operand, Branching, Marker, InterProc, Extra>;

/// [`Instr`](ir::Instr)uction with kind "stripped".
pub type Instr = ir::Instr<Kind>;

/// Marker instructions for kind "stripped".
#[derive(Debug, Display, FromStr, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Marker {
    /// Mark the end of a function.
    #[display("ret")]
    Ret,
}

impl HasBranchingBehaviour for Marker {
    fn get_branching_behaviour(&self) -> BranchingBehaviour {
        BranchingBehaviour { alternative_dest: None, might_fallthrough: false }
    }
}

/// [`Block`](ir::Block) with kind "stripped".
pub type Block = ir::Block<Kind>;

/// [`Blocks`](ir::Blocks) with kind "stripped".
pub type Blocks = ir::Blocks<Kind>;

/// [`Function`](ir::Function) with kind "stripped".
pub type Function = ir::Function<Kind>;

/// [`Functions`](ir::Functions) with kind "stripped".
pub type Functions = ir::Functions<Kind>;
