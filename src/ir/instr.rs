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

//! Instructions for three-address code.

pub mod basic;
pub mod stripped;
pub mod resolved;
pub mod structured;

use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::str::FromStr;
use derivative::Derivative;
use parse_display::{Display, FromStr};
use smallvec::{SmallVec, smallvec};

/// Binary operators.
#[derive(Debug, Display, FromStr, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[display(style = "lowercase")]
#[allow(missing_docs)]
pub enum BOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    CmpEq,
    CmpLe,
    CmpLt,
}

/// Unary operators.
#[derive(Debug, Display, FromStr, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[display(style = "lowercase")]
#[allow(missing_docs)]
pub enum UOp {
    Neg,
}

/// Branching methods.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum BranchKind<Operand> {
    #[display("br")]
    Unconditional,
    #[display("blbs {0}")]
    If(Operand),
    #[display("blbc {0}")]
    Unless(Operand),
}

/// Common branching instructions.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[display("{method} [{dest}]")]
pub struct Branching<Operand> {
    /// The condition of the branching.
    pub method: BranchKind<Operand>,
    /// Destination, interpreted differently according to the context. It might be one of:
    /// 1. instruction index when dealing with "raw" input;
    /// 2. block index when dealing with programs structured as a series of basic blocks.
    pub dest: usize,
}

/// Extension point for instructions.
///
/// The `Self` type is essentially insignificant, to avoid the awkwardness of manually specifying
/// all the bounds using `derivative`, we instead impose the superfluous bounds here. Use [`Kind`]
/// to have all the bounds automatically implemented.
pub trait InstrExt: Copy + Eq + Ord + Debug + Display + FromStr {
    /// Operand type.
    type Operand;
    /// Branching instructions, eventually replaced by structural control flow.
    type Branching;
    /// Marker instructions, eventually completely eliminated.
    type Marker;
    /// Inter-procedural instruction, i.e. function call related stuff.
    type InterProc;
    /// Other instructions, e.g. φ-nodes in SSA form.
    type Extra;
}

/// An instruction kind.
///
/// Note: this type is only intended to be used as a "marker" for [`Instr`].
/// Don't bother making an instance of this type.
///
/// See also [`basic::Kind`], [`basic::Instr`], etc.
#[derive(Display, FromStr)]
#[display("", bound(""))]
#[from_str(default_fields("_phantom"), bound(""))]
#[derive(Derivative)]
#[derivative(Debug(bound = ""))]
#[derivative(Copy(bound = ""), Clone(bound = ""))]
#[derivative(Ord(bound = ""), PartialOrd(bound = ""))]
#[derivative(Eq(bound = ""), PartialEq(bound = ""))]
pub struct Kind<Operand, Branching, Marker, InterProc, Extra> {
    _phantom: PhantomData<*const (Operand, Branching, Marker, InterProc, Extra)>,
}

impl<Operand, Branching, Marker, InterProc, Extra> InstrExt
for Kind<Operand, Branching, Marker, InterProc, Extra> {
    type Operand = Operand;
    type Branching = Branching;
    type Marker = Marker;
    type InterProc = InterProc;
    type Extra = Extra;
}

/// Number of operands for an instruction.
pub trait HasOperand<Operand> {
    /// An instruction has no more than two (and possibly zero) operands as input.
    fn get_operands(&self) -> SmallVec<[&Operand; 2]>;
}

/// Manipulate the "destination" field in an instruction.
pub trait HasDest {
    /// Apply a transformation to all the "destination" fields in this instruction.
    fn map_dest(self, f: impl FnOnce(usize) -> usize) -> Self;
}

/// Information on output of an instruction.
pub trait OutputInfo {
    /// An instruction might have an output. This indicates whether or not the instruction register
    /// `rk` is properly defined after the execution of this instruction (assumed to have index `k`).
    fn has_output(&self) -> bool;
}

/// Instructions.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[allow(missing_docs)]
#[display(style = "lowercase")]
pub enum Instr<K: InstrExt = basic::Kind> {
    /// Binary operations.
    #[display("{op} {lhs} {rhs}")]
    Binary {
        op: BOp,
        lhs: K::Operand,
        rhs: K::Operand,
    },
    /// Unary operations.
    #[display("{op} {operand}")]
    Unary {
        op: UOp,
        operand: K::Operand,
    },
    /// Branching operations.
    #[display("{0}")]
    Branch(K::Branching),
    /// Pointer dereference.
    #[display("load {0}")]
    Load(K::Operand),
    /// Pointer dereference and assign.
    #[display("store {data} {address}")]
    Store {
        data: K::Operand,
        address: K::Operand,
    },
    #[display("move {source} {dest}")]
    Move {
        source: K::Operand,
        dest: K::Operand,
    },
    /// Defined as `scanf("%lld", &x);` in C.
    #[display("read")]
    Read,
    /// Defined as `printf(" %lld", x);` in C.
    #[display("write {0}")]
    Write(K::Operand),
    /// Defined as `printf("\n");` in C.
    #[display("wrl")]
    WriteLn,
    /// Inter-procedural (function call related) instruction.
    #[display("{0}")]
    InterProc(K::InterProc),
    Nop,
    /// Marker instructions.
    #[display("{0}")]
    Marker(K::Marker),
    /// Other instructions.
    #[display("{0}")]
    Extra(K::Extra),
}

use Instr::*;

impl<K1: InstrExt> Instr<K1> {
    /// Transform into (potentially) another kind of instruction.
    pub fn map_kind<K2: InstrExt>(
        self,
        mut map_operand: impl FnMut(K1::Operand) -> K2::Operand,
        map_branching: impl FnOnce(K1::Branching) -> K2::Branching,
        map_inter_proc: impl FnOnce(K1::InterProc) -> K2::InterProc,
        map_marker: impl FnOnce(K1::Marker) -> K2::Marker,
        map_extra: impl FnOnce(K1::Extra) -> K2::Extra,
    ) -> Instr<K2> {
        match self {
            Binary { op, lhs, rhs } => Binary {
                op,
                lhs: map_operand(lhs),
                rhs: map_operand(rhs),
            },
            Unary { op, operand } => Unary {
                op,
                operand: map_operand(operand),
            },
            Branch(br) => Branch(map_branching(br)),
            Load(operand) => Load(map_operand(operand)),
            Store { data, address } => Store {
                data: map_operand(data),
                address: map_operand(address),
            },
            Move { source, dest } => Move {
                source: map_operand(source),
                dest: map_operand(dest),
            },
            Read => Read,
            Write(operand) => Write(map_operand(operand)),
            WriteLn => WriteLn,
            InterProc(ip) => InterProc(map_inter_proc(ip)),
            Nop => Nop,
            Marker(marker) => Marker(map_marker(marker)),
            Extra(extra) => Extra(map_extra(extra)),
        }
    }
}

impl<Operand, K: InstrExt<Operand=Operand>> HasOperand<Operand> for Instr<K>
    where K::Branching: HasOperand<Operand>,
          K::InterProc: HasOperand<Operand>,
          K::Extra: HasOperand<Operand> {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> {
        match self {
            Binary { lhs, rhs, .. } => smallvec![lhs, rhs],
            Unary { operand, .. } => smallvec![operand],
            Load(operand) => smallvec![operand],
            Store { data, address } => smallvec![data, address],
            Write(operand) => smallvec![operand],
            InterProc(inter) => inter.get_operands(),
            Extra(extra) => extra.get_operands(),
            _ => SmallVec::new(),
        }
    }
}

/// This `HasDest` is only implemented for [`basic::Instr`]uctions for a reason.
///
/// Other than the "basic" kind, instructions tends to interpret the destination field in
/// [`InterProc`], [`Branch`], and [`Extra`] differently. Therefore, it is
/// not very likely that any meaningful transformation on these destinations could be done with
/// a single mapping function.
///
/// For instructions other than the "basic" kind, match against the three kind mentioned above
/// and call `map_dest` on them, or implement [`HasDest`] for that specific kind of
/// [`Instr`]uctions (and do it with _special care_).
impl HasDest for basic::Instr {
    fn map_dest(self, f: impl FnOnce(usize) -> usize) -> Self {
        match self {
            InterProc(inter) => InterProc(inter.map_dest(f)),
            Branch(br) => Branch(br.map_dest(f)),
            Extra(extra) => Extra(extra.map_dest(f)),
            instr => instr,
        }
    }
}

impl<Kind: InstrExt> OutputInfo for Instr<Kind>
    where Kind::Branching: OutputInfo,
          Kind::InterProc: OutputInfo,
          Kind::Extra: OutputInfo {
    fn has_output(&self) -> bool {
        match self {
            Binary { .. } | Unary { .. } | Load(_) | Move { .. } | Read => true,
            InterProc(inter) => inter.has_output(),
            Extra(extra) => extra.has_output(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ir::instr::Branching;
    use super::{BOp, UOp, basic::{Instr, BranchKind, InterProc, Marker, Operand}};

    macro_rules! assert_equiv {
        ($($str: literal => $val: expr),+ $(,)?) => {
            $(
                assert_eq!($val.to_string(), $str);
                assert_eq!($val, $str.parse().unwrap());
            )+
        }
    }

    #[test]
    fn test_operand() {
        assert_equiv! {
            "GP" => Operand::GP,
            "FP" => Operand::FP,
            "42" => Operand::Const(42),
            "(42)" => Operand::Register(42),
            "y_offset#8" => Operand::FieldOffset("y".to_string(), 8),
            "x_base#32760" => Operand::BaseAddress("x".to_string(), 32760),
            "a#-8" => Operand::Var("a".to_string(), -8),
        }
    }

    #[test]
    fn test_instruction() {
        assert_equiv! {
            "nop" => Instr::Nop,
            // arithmetic
            "add (41) y_offset#8" => Instr::Binary {
                op: BOp::Add,
                lhs: Operand::Register(41),
                rhs: Operand::FieldOffset("y".to_string(), 8),
            },
            "neg a#24" => Instr::Unary {
                op: UOp::Neg,
                operand: Operand::Var("a".to_string(), 24),
            },
            // branching
            "blbs (36) [46]" => Instr::Branch(Branching {
                method: BranchKind::If(Operand::Register(36)),
                dest: 46,
            }),
            // inter-procedural
            "call [23]" => Instr::InterProc(InterProc::Call { dest: 23 }),
            "param (59)" => Instr::InterProc(InterProc::PushParam(Operand::Register(59))),
            // moving
            "load (13)" => Instr::Load(Operand::Register(13)),
            "move i#-8 j#-16" => Instr::Move {
                source: Operand::Var("i".to_string(), -8),
                dest: Operand::Var("j".to_string(), -16),
            },
            "store (15) (11)" => Instr::Store {
                data: Operand::Register(15),
                address: Operand::Register(11),
            },
            // input & output
            "read" => Instr::Read,
            "write x#-64" => Instr::Write(Operand::Var("x".to_string(), -64)),
            "wrl" => Instr::WriteLn,
            // function related markups
            "entrypc" => Instr::Marker(Marker::EntryPc),
            "enter 8" => Instr::Marker(Marker::EnterProc(8)),
            "ret 0" => Instr::Marker(Marker::Ret(0)),
        }
    }
}

/// Replacement for the not yet stable "never" type.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum Never {}

impl Never {
    /// Get anything from absurdity.
    pub fn absurd<T>(self) -> T { match self {} }
}

impl std::str::FromStr for Never {
    type Err = ();
    fn from_str(_: &str) -> Result<Self, Self::Err> { Err(()) }
}

impl Display for Never {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { match *self {} }
}

impl<Operand> HasOperand<Operand> for Never {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> { match *self {} }
}

impl OutputInfo for Never {
    fn has_output(&self) -> bool { match *self {} }
}

impl HasDest for Never {
    fn map_dest(self, _: impl FnOnce(usize) -> usize) -> Self { match self {} }
}
