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

//! Stripped instructions for use in [`Function`](crate::Function)s.

/// Kind "stripped" use the same operand, as well as the same branching, inter-procedural, and
/// extra instructions as kind "basic".
pub use super::basic::{Operand, Branching, InterProc, Extra};

/// Instruction kind "stripped".
pub type Kind = crate::instr::Kind<Operand, Branching, Marker, InterProc, Extra>;

/// [`Instr`](crate::Instr)uction with kind "stripped".
pub type Instr = crate::Instr<Kind>;

/// Kind "stripped" has no marker instructions.
pub type Marker = super::Never;

/// [`Block`](crate::Block) with kind "stripped".
pub type Block = crate::Block<Kind>;

/// [`Blocks`](crate::block::Blocks) with kind "stripped".
pub type Blocks = crate::block::Blocks<Kind>;

/// [`Function`](crate::Function) with kind "stripped".
pub type Function = crate::Function<Kind>;

/// [`Functions`](crate::function::Functions) with kind "stripped".
pub type Functions = crate::function::Functions<Kind>;
