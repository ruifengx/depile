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

//! C-like expressions and statements.

use std::collections::BTreeMap;
use std::fmt::{Display, Formatter};
use thiserror::Error;
use displaydoc::Display;
use itertools::Itertools;
use crate::ir::instr::{BOp, UOp, structured};
use structured::{Instr, Branching, Extra, InterProc, Operand, write_indented};

/// C expressions.
#[allow(missing_docs)]
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Expr {
    Binary { op: BOp, lhs: Box<Expr>, rhs: Box<Expr> },
    Not(Box<Expr>),
    Neg(Box<Expr>),
    Deref(Box<Expr>),
    Read,
    Var(i64),
    Param(String),
    Const(i64),
    FP,
    GP,
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Binary { op, lhs, rhs } =>
                write!(f, "({lhs} {} {rhs})", op.pretty()),
            Expr::Not(expr) => write!(f, "!{expr}"),
            Expr::Neg(expr) => write!(f, "-{expr}"),
            Expr::Deref(expr) => write!(f, "DEREF({expr})"),
            Expr::Read => write!(f, "ReadLong()"),
            Expr::Var(x) => write!(f, "{x}"),
            Expr::Param(x) => write!(f, "{x}"),
            Expr::Const(c) => write!(f, "{c}"),
            Expr::FP => write!(f, "frame_storage"),
            Expr::GP => write!(f, "global_storage"),
        }
    }
}

/// C statements.
#[allow(missing_docs)]
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Statement {
    Assigment { dest: Expr, source: Expr },
    Write(Expr),
    WriteLn,
    Call(usize, Box<[Expr]>),
    If {
        condition: Expr,
        then_branch: Box<[Statement]>,
        else_branch: Option<Box<[Statement]>>,
    },
    While {
        condition: Expr,
        loop_body: Box<[Statement]>,
    },
}

struct Indented<'a>(&'a [Statement]);

impl<'a> Display for Indented<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        let mut buffer = String::new();
        for statement in self.0 {
            write_indented(f, format_args!("{}", statement), &mut buffer)?;
        }
        Ok(())
    }
}

struct Braced<'a>(&'a [Statement]);

impl<'a> Display for Braced<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{{\n{}}}", Indented(self.0))
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Statement::Assigment { dest, source } => write!(f, "{dest} = {source};"),
            Statement::Write(x) => write!(f, "WriteLong({x});"),
            Statement::WriteLn => write!(f, "WriteLn();"),
            Statement::Call(t, params) =>
                write!(f, "global_function_{t}({})", params.iter().format(", ")),
            Statement::If { condition, then_branch, else_branch } => {
                write!(f, "if ({condition}) {}", Braced(then_branch))?;
                if let Some(else_branch) = else_branch {
                    write!(f, " else {}", Braced(else_branch))?;
                }
                Ok(())
            }
            Statement::While { condition, loop_body } =>
                write!(f, "while ({condition}) {}", Braced(loop_body)),
        }
    }
}

/// C Functions.
#[derive(Debug, Clone)]
pub struct Function {
    /// Number of formal parameters.
    pub parameters: Vec<String>,
    /// Number of local variables.
    pub local_var_count: u64,
    /// Function body.
    pub body: Box<[Statement]>,
}

/// Collection of C functions.
#[derive(Debug, Clone)]
pub struct Functions {
    /// List of functions, in ascending order for block index.
    pub functions: Box<[Function]>,
    /// The index of the entry function (i.e. `main`).
    ///
    /// This `main` function has its first instruction of its entry block preceded by `entrypc`
    /// (in other words, it is marked as the entry point for the whole program).
    pub entry_function: usize,
}

const PRELUDE: &str = indoc::indoc! {r#"
    #include <stdint.h>
    #include <stdio.h>
    #include <inttypes.h>

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

impl Display for Functions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}\n\n", PRELUDE)?;
        for (k, func) in self.functions.iter().enumerate() {
            writeln!(f, "void global_function_{k}({}) {{", func.parameters.iter()
                .format_with(", ", |x, k| k(&format_args!("WORD {x}"))))?;
            if func.local_var_count > 0 {
                writeln!(f, "  WORD frame_storage[{}] = {{0}};", func.local_var_count)?;
            }
            writeln!(f, "{}}}\n", Indented(&func.body))?;
        }
        write!(f, indoc::indoc! {r#"
            int main() {{
              global_function_{}();
              return 0;
            }}
        "#}, self.entry_function)
    }
}

struct Conversion {
    reg_status: BTreeMap<usize, Expr>,
    output: Vec<Statement>,
}

/// Conversion error.
#[derive(Debug, Display, Error, Copy, Clone)]
pub enum Error {
    /// register ({0}) has already been killed
    RegisterKilled(usize),
}

impl Conversion {
    fn derived(&self) -> Conversion {
        Conversion {
            reg_status: self.reg_status.clone(),
            output: Vec::new(),
        }
    }
    fn derived_on(&self, block: &[(usize, Instr)]) -> Result<Conversion, Error> {
        let mut conv = self.derived();
        conv.run_on_block(block)?;
        Ok(conv)
    }
    fn get_register(&self, r: usize) -> Result<Expr, Error> {
        self.reg_status.get(&r).cloned()
            .ok_or(Error::RegisterKilled(r))
    }
    fn record_register(&mut self, r: usize, val: Expr) {
        self.reg_status.insert(r, val);
    }
    fn invalidate_registers(&mut self) { self.reg_status.clear() }
    fn emit(&mut self, s: Statement) { self.output.push(s); }
    fn handle_operand(&self, operand: &Operand) -> Result<Expr, Error> {
        Ok(match operand {
            Operand::GP => Expr::GP,
            Operand::FP => Expr::FP,
            Operand::Const(x) => Expr::Const(*x),
            Operand::BaseAddress(_, k) => Expr::Const(*k),
            Operand::FieldOffset(_, k) => Expr::Const(*k),
            Operand::Var(x, k) if *k > 0 => Expr::Param(x.clone()),
            Operand::Var(_, k) => Expr::Var(*k),
            Operand::Register(r) => self.get_register(*r)?,
        })
    }
    fn handle_operand_boxed(&mut self, operand: &Operand) -> Result<Box<Expr>, Error> {
        self.handle_operand(operand).map(Box::new)
    }
    fn handle_branch(&mut self, br: &Branching) -> Result<(), Error> {
        match br {
            Branching::If { condition, then_branch, else_branch } => {
                let c_cond = self.derived_on(condition.preparation.as_ref())?;
                assert!(c_cond.output.is_empty(), "condition should not produce true statements");
                let negation = condition.negation;
                let mut condition = c_cond.handle_operand(&condition.value)?;
                if negation { condition = Expr::Not(Box::new(condition)); }
                let c_then = self.derived_on(then_branch.as_ref())?;
                let then_branch = c_then.output.into_boxed_slice();
                let else_branch = if let Some(else_branch) = else_branch {
                    let c_else = self.derived_on(else_branch.as_ref())?;
                    Some(c_else.output.into_boxed_slice())
                } else { None };
                self.emit(Statement::If { condition, then_branch, else_branch });
                Ok(())
            }
            Branching::While { condition, loop_body } => {
                let c_cond = self.derived_on(condition.preparation.as_ref())?;
                assert!(c_cond.output.is_empty(), "condition should not produce true statements");
                let negation = condition.negation;
                let mut condition = c_cond.handle_operand(&condition.value)?;
                if negation { condition = Expr::Not(Box::new(condition)); }
                let c_body = self.derived_on(loop_body.as_ref())?;
                let loop_body = c_body.output.into_boxed_slice();
                self.emit(Statement::While { condition, loop_body });
                Ok(())
            }
        }
    }
    fn handle_inter_proc(&mut self, ip: &InterProc) -> Result<(), Error> {
        let InterProc::Call { dest, param_list } = ip;
        let param_list = param_list.iter()
            .map(|x| self.handle_operand(x))
            .collect::<Result<Box<[_]>, _>>()?;
        self.emit(Statement::Call(*dest, param_list));
        Ok(())
    }
    fn handle_instr(&mut self, r: usize, instr: &Instr) -> Result<(), Error> {
        match instr {
            Instr::Nop => {}
            Instr::Marker(marker) => match *marker {},
            Instr::Binary { op, lhs, rhs } => {
                let lhs = self.handle_operand_boxed(lhs)?;
                let rhs = self.handle_operand_boxed(rhs)?;
                self.record_register(r, Expr::Binary { op: *op, lhs, rhs });
            }
            Instr::Unary { op: UOp::Neg, operand } => {
                let operand = self.handle_operand_boxed(operand)?;
                self.record_register(r, Expr::Neg(operand));
            }
            Instr::Branch(br) => self.handle_branch(br)?,
            Instr::Load(address) => {
                let address = self.handle_operand_boxed(address)?;
                self.record_register(r, Expr::Deref(address));
            }
            Instr::Store { data, address } => {
                let data = self.handle_operand(data)?;
                let dest = Expr::Deref(self.handle_operand_boxed(address)?);
                self.record_register(r, dest.clone());
                self.emit(Statement::Assigment { dest, source: data });
                self.invalidate_registers();
            }
            Instr::Move { source, dest } => {
                let source = self.handle_operand(source)?;
                let dest = self.handle_operand(dest)?;
                self.emit(Statement::Assigment { source, dest });
                self.invalidate_registers();
            }
            Instr::Read => self.record_register(r, Expr::Read),
            Instr::Write(operand) => {
                let operand = self.handle_operand(operand)?;
                self.emit(Statement::Write(operand));
            }
            Instr::WriteLn => self.emit(Statement::WriteLn),
            Instr::InterProc(ip) => self.handle_inter_proc(ip)?,
            Instr::Extra(Extra::Snapshot(operand)) => {
                let operand = self.handle_operand(operand)?;
                self.record_register(r, operand);
            }
        }
        Ok(())
    }
    fn run_on_block(&mut self, block: &[(usize, Instr)]) -> Result<(), Error> {
        for (r, instr) in block {
            self.handle_instr(*r, instr)?;
        }
        Ok(())
    }
}

impl structured::Function {
    /// Convert this structured function to C function.
    pub fn to_c(&self) -> Result<Function, Error> {
        let mut conv = Conversion { reg_status: BTreeMap::new(), output: Vec::new() };
        conv.run_on_block(self.body.as_ref())?;
        let body = conv.output.into_boxed_slice();
        Ok(Function { parameters: self.param_list(), local_var_count: self.local_var_count, body })
    }
}

impl structured::Functions {
    /// Convert collections of structured functions to C functions.
    pub fn to_c(&self) -> Result<Functions, Error> {
        let functions = self.functions.iter()
            .map(structured::Function::to_c)
            .collect::<Result<Box<[_]>, _>>()?;
        Ok(Functions { functions, entry_function: self.entry_function })
    }
}

#[cfg(test)]
mod tests {
    use crate::samples;
    use crate::ir::instr::basic::Blocks;
    use crate::ir::program::read_program;

    #[test]
    fn test_to_structured() {
        for input in samples::ALL_SAMPLES {
            let program = read_program(input).unwrap();
            let blocks = Blocks::try_from(program.as_ref()).unwrap();
            let functions = blocks.functions().unwrap();
            let functions = functions.resolve().unwrap();
            let functions = functions.to_structured();
            let functions = functions.to_c().unwrap();
            // to avoid optimizations messing up our tests
            assert!(!functions.functions.is_empty());
        }
    }
}
