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

//! Conversion to C.

use std::fmt::{Display, Formatter};
use itertools::Itertools;
use crate::ir::instr::{BOp, HasOperand, OutputInfo, UOp};
use crate::ir::instr::structured::{
    Instr, Operand, Extra, InterProc, Branching,
    Block, Condition, Functions,
    write_indented,
};

struct Wrapper<'a, T: ?Sized> (&'a T);

impl<'a, T: ToC + ?Sized> Display for Wrapper<'a, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result { self.0.fmt_c(f) }
}

macro_rules! c {
    ($e: expr) => { Wrapper($e) }
}

/// Conversion to C code.
pub trait ToC {
    /// [`Display`]-style implementation.
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result;
    /// Transform to C source code.
    fn to_c_code(&self) -> String {
        format!("{}", Wrapper(self))
    }
}

impl ToC for Operand {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Operand::GP => write!(f, "global_storage"),
            Operand::FP => write!(f, "frame_storage"),
            Operand::Const(x) => write!(f, "{}", x),
            Operand::BaseAddress(x, k) => write!(f, "/* {}_base: */ {}", x, k),
            Operand::FieldOffset(x, k) => write!(f, "/* {}_offset: */ {}", x, k),
            Operand::Var(x, k) if *k < 0 => write!(f, "/* {}: */ frame_storage[{}]", x, -k / 8),
            Operand::Var(x, _) => write!(f, "{}", x),
            Operand::Register(r) => write!(f, "reg_{}", r),
        }
    }
}

impl ToC for UOp {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        match self { UOp::Neg => write!(f, "-") }
    }
}

impl ToC for BOp {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{}", match self {
            BOp::Add => "+",
            BOp::Sub => "-",
            BOp::Mul => "*",
            BOp::Div => "/",
            BOp::Mod => "*",
            BOp::CmpEq => "==",
            BOp::CmpLe => "<=",
            BOp::CmpLt => "<",
        })
    }
}

impl ToC for InterProc {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        let InterProc::Call { dest, param_list } = self;
        write!(f, "global_function_{}({})", dest, param_list.iter()
            .format_with(", ", |param, k| k(&c!(param))))?;
        Ok(())
    }
}

struct Indented<'a>(&'a Block);

impl<'a> Display for Indented<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let mut buffer = String::new();
        for (k, instr) in self.0.as_ref() {
            if instr.has_output() {
                write_indented(f, format_args!("reg_{} = {};", k, c!(instr)), &mut buffer)?;
            } else if !matches!(instr, Instr::Branch(_)) {
                write_indented(f, format_args!("{};", c!(instr)), &mut buffer)?;
            } else {
                write_indented(f, format_args!("{}", c!(instr)), &mut buffer)?;
            }
        }
        Ok(())
    }
}

struct Braced<'a>(&'a Block);

impl<'a> Display for Braced<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{{\n{}}}", Indented(self.0))
    }
}

impl ToC for Condition {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "some condition here")?;
        Ok(())
    }
}

impl ToC for Branching {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Branching::If { condition, then_branch, else_branch } => {
                write!(f, "if ({}) {}", c!(condition), Braced(then_branch))?;
                if let Some(else_branch) = else_branch {
                    write!(f, " else {}", Braced(else_branch))?;
                }
                Ok(())
            }
            Branching::While { condition, loop_body } =>
                write!(f, "while ({}) {}", c!(condition), Braced(loop_body)),
        }
    }
}

impl ToC for Instr {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        match self {
            Instr::Binary { op, lhs, rhs } =>
                write!(f, "{} {} {}", c!(lhs), c!(op), c!(rhs)),
            Instr::Unary { op, operand } =>
                write!(f, "{} {}", c!(op), c!(operand)),
            Instr::Branch(br) => br.fmt_c(f),
            Instr::Load(operand) => write!(f, "DEREF({})", c!(operand)),
            Instr::Store { data, address } =>
                write!(f, "DEREF({}) = {}", c!(address), c!(data)),
            Instr::Move { source, dest } =>
                write!(f, "{} = {}", c!(dest), c!(source)),
            Instr::Read => write!(f, "ReadLong()"),
            Instr::Write(operand) => write!(f, "WriteLong({})", c!(operand)),
            Instr::WriteLn => write!(f, "WriteLn()"),
            Instr::InterProc(ip) => ip.fmt_c(f),
            Instr::Nop => Ok(()),
            Instr::Marker(marker) => match *marker {},
            Instr::Extra(Extra::Snapshot(x)) => write!(f, "{}", c!(x)),
        }
    }
}

const PRELUDE: &str = indoc::indoc! {r#"
    #include <stdint.h>
    #include <stdio.h>

    typedef uint64_t WORD;
    typedef char *ADDR;

    #define DEREF(p) (*(WORD *) (p))
    inline WORD ReadLone() {
        WORD x = 0;
        scanf("%" PRIu64, &x);
        return x;
    }
    inline void WriteLong(WORD x) {
        printf(" %" PRIu64, x);
    }
    inline void WriteLn() {
        printf("\n");
    }

    static WORD global_back_buffer[32768 / 8];
    const ADDR global_storage = (ADDR) global_back_buffer;
"#};

impl ToC for Functions {
    fn fmt_c(&self, f: &mut Formatter) -> std::fmt::Result {
        writeln!(f, "{}", PRELUDE)?;
        for (k, func) in self.functions.iter().enumerate() {
            let mut params = vec![String::new(); func.parameter_count as usize];
            for (_, instr) in func.body.as_ref() {
                for operand in instr.get_operands() {
                    if let Operand::Var(x, k) = operand {
                        if *k > 0 {
                            params[((*k - 16) / 8) as usize] = x.clone();
                        }
                    }
                }
            }
            params.reverse();
            for (k, param) in params.iter_mut().enumerate() {
                if param.is_empty() {
                    *param = format!("ignored_param_{}", k);
                }
            }
            writeln!(f, "void global_function_{}({}) {{", k, params.into_iter()
                .format_with(", ", |p, k| k(&format_args!("WORD {}", p))))?;
            if func.local_var_count > 0 {
                writeln!(f, "  WORD frame_storage[{}] = {{0}};", func.local_var_count)?;
            }
            writeln!(f, "{}}}", Indented(&func.body))?;
        }
        write!(f, indoc::indoc! {r#"
            int main() {{
              global_function_{}();
              return 0;
            }}
        "#}, self.entry_function)
    }
}
