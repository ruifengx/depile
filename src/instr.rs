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

//! Instructions for three-address code.

use parse_display::{Display, FromStr};

/// Operands to all the [`Instr`]uctions.
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
pub enum BranchKind {
    #[display("br")]
    Unconditional,
    #[display("blbs {0}")]
    If(Operand),
    #[display("blbc {0}")]
    Unless(Operand),
    #[display(style = "lowercase")]
    Call,
}

/// Instructions.
#[derive(Debug, Display, FromStr, Clone, Ord, PartialOrd, Eq, PartialEq)]
#[allow(missing_docs)]
#[display(style = "lowercase")]
pub enum Instr {
    /// Binary operations.
    #[display("{op} {lhs} {rhs}")]
    Binary {
        op: BOp,
        lhs: Operand,
        rhs: Operand,
    },
    /// Unary operations.
    #[display("{op} {operand}")]
    Unary {
        op: UOp,
        operand: Operand,
    },
    /// Branching operations.
    #[display("{method} [{dest}]")]
    Branch {
        method: BranchKind,
        dest: usize,
    },
    #[display("load {0}")]
    Load(Operand),
    #[display("store {data} {address}")]
    Store {
        data: Operand,
        address: Operand,
    },
    #[display("move {source} {dest}")]
    Move {
        source: Operand,
        dest: Operand,
    },
    /// Defined as `scanf("%lld", &x);` in C.
    #[display("read {0}")]
    Read(Operand),
    /// Defined as `printf(" %lld", x);` in C.
    #[display("write {0}")]
    Write(Operand),
    /// Defined as `printf("\n");` in C.
    #[display("wrl")]
    WriteLn,
    #[display("param {0}")]
    PushParam(Operand),
    /// Denotes the beginning of a function. Its operand `{0}` specifies the amount of memory in
    /// bytes to be allocated on the stack frame for local variables of that function.
    #[display("enter {0}")]
    EnterProc(u64),
    /// Denotes a function return. Its operand `{0}` specifies the amount of memory for formal
    /// parameters that needs to be removed (popped) from the stack.
    #[display("ret {0}")]
    Ret(u64),
    /// Denotes the beginning of the `main` function.
    EntryPc,
    Nop,
}

impl Instr {
    /// Is the register `rk` properly defined after this instruction `k`?
    pub fn has_output(&self) -> bool {
        matches!(self, Instr::Binary { .. } | Instr::Unary { .. } |
            Instr::Load(_) | Instr::Move { .. } | Instr::Read(_))
    }
}

#[cfg(test)]
mod tests {
    use super::{BOp, BranchKind, Instr, Operand, UOp};

    macro_rules! assert_equiv {
        ($($str: expr => $val: expr),+ $(,)?) => {
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
            "y_offset#8" => Operand::Offset("y_offset".to_string(), 8),
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
                rhs: Operand::Offset("y_offset".to_string(), 8),
            },
            "neg a#24" => Instr::Unary {
                op: UOp::Neg,
                operand: Operand::Offset("a".to_string(), 24),
            },
            // branching
            "blbs (36) [46]" => Instr::Branch {
                method: BranchKind::If(Operand::Register(36)),
                dest: 46,
            },
            "call [23]" => Instr::Branch {
                method: BranchKind::Call,
                dest: 23
            },
            // moving
            "load (13)" => Instr::Load(Operand::Register(13)),
            "move i#-8 j#-16" => Instr::Move {
                source: Operand::Offset("i".to_string(), -8),
                dest: Operand::Offset("j".to_string(), -16),
            },
            "store (15) (11)" => Instr::Store {
                data: Operand::Register(15),
                address: Operand::Register(11),
            },
            // input & output
            "read x#-64" => Instr::Read(Operand::Offset("x".to_string(), -64)),
            "write x#-64" => Instr::Write(Operand::Offset("x".to_string(), -64)),
            "wrl" => Instr::WriteLn,
            // function related
            "entrypc" => Instr::EntryPc,
            "enter 8" => Instr::EnterProc(8),
            "ret 0" => Instr::Ret(0),
            "param (59)" => Instr::PushParam(Operand::Register(59)),
        }
    }
}
