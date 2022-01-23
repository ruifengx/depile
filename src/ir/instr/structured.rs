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

//! "Structured" instructions. In this flavour of instructions, branching instructions own their
//! successor blocks. Raw `goto`s are eliminated, and all of them are turned into control flow
//! structures.

use std::collections::BTreeSet;
use std::fmt::{Arguments, Display, Formatter, Write};
use smallvec::SmallVec;
use crate::ir::{self, instr::{resolved, BranchKind, OutputInfo, HasOperand}};
use crate::analysis::data_flow::dominator::{DomRel, get_dominators};

pub use ir::instr::{
    basic::Operand,
    resolved::{InterProc, Extra},
};

/// Instruction kind "structured".
pub type Kind = ir::instr::Kind<Operand, Branching, Marker, InterProc, Extra>;

/// [`Instr`](ir::Instr)uction with kind "structured".
pub type Instr = ir::Instr<Kind>;

/// Structured blocks.
pub type Block = Box<[(usize, Instr)]>;

/// Structured functions.
pub struct Function {
    /// Number of formal parameters.
    pub parameter_count: u64,
    /// Number of local variables.
    pub local_var_count: u64,
    /// Function body.
    pub body: Block,
}

impl Function {
    /// Get list of parameter names.
    pub fn param_list(&self) -> Vec<String> {
        let mut params = vec![String::new(); self.parameter_count as usize];
        for (_, instr) in self.body.as_ref() {
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
        params
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "#parameters = {}", self.parameter_count)?;
        writeln!(f, "#local_vars = {}", self.local_var_count)?;
        writeln!(f)?;
        for (k, instr) in self.body.iter() {
            writeln!(f, "instr {}: {}", k, instr)?;
        }
        Ok(())
    }
}

/// Collection of structured functions.
pub struct Functions {
    /// List of functions, in ascending order for block index.
    pub functions: Box<[Function]>,
    /// The index of the entry function (i.e. `main`).
    ///
    /// This `main` function has its first instruction of its entry block preceded by `entrypc`
    /// (in other words, it is marked as the entry point for the whole program).
    pub entry_function: usize,
}

impl Display for Functions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (k, func) in self.functions.iter().enumerate() {
            if k == self.entry_function { write!(f, "(ENTRY) ")?; }
            writeln!(f, "Function #{}:", k)?;
            writeln!(f, "{}", func)?;
        }
        Ok(())
    }
}

/// Condition for branching instructions.
#[allow(missing_docs)]
#[derive(Clone, Eq, PartialEq)]
pub struct Condition {
    /// Preparation instructions.
    pub preparation: Block,
    pub value: Operand,
    pub negation: bool,
}

/// Control flow structures for "structured" instructions.
#[derive(Clone, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum Branching {
    /// `if` statements.
    If {
        condition: Condition,
        then_branch: Block,
        else_branch: Option<Block>,
    },
    /// `while` statements.
    While {
        condition: Condition,
        loop_body: Block,
    },
}

impl HasOperand<Operand> for Branching {
    fn get_operands(&self) -> SmallVec<[&Operand; 2]> {
        let mut result = BTreeSet::new();
        let blocks = match self {
            Branching::If { condition, then_branch, else_branch } => {
                let mut blocks = vec![condition.preparation.as_ref(), then_branch];
                if let Some(else_branch) = else_branch {
                    blocks.push(else_branch);
                }
                blocks
            }
            Branching::While { condition, loop_body } =>
                vec![condition.preparation.as_ref(), loop_body],
        };
        for block in blocks {
            for (_, instr) in block {
                result.extend(instr.get_operands());
            }
        }
        result.into_iter().collect()
    }
}

impl OutputInfo for Branching {
    fn has_output(&self) -> bool { false }
}

pub(crate) fn write_indented<W>(f: &mut W, v: Arguments, buffer: &mut String) -> std::fmt::Result
    where W: Write + ?Sized {
    buffer.clear();
    writeln!(buffer, "{}", v)?;
    for line in buffer.lines() {
        writeln!(f, "  {}", line)?;
    }
    Ok(())
}

fn write_prep(condition: &Condition, f: &mut Formatter<'_>) -> std::fmt::Result {
    writeln!(f, "prepare {{")?;
    let mut buffer = String::new();
    for (k, instr) in condition.preparation.iter() {
        write_indented(f, format_args!("instr {}: {}", k, instr), &mut buffer)?;
    }
    writeln!(f, "}}")
}

impl Display for Branching {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Branching::If { condition, then_branch, else_branch } => {
                write_prep(condition, f)?;
                let neg = if condition.negation { " not" } else { "" };
                writeln!(f, "if{neg} {} {{", condition.value)?;
                let mut buffer = String::new();
                for (k, instr) in then_branch.iter() {
                    write_indented(f, format_args!("instr {}: {}", k, instr), &mut buffer)?;
                }
                if let Some(else_branch) = else_branch {
                    writeln!(f, "}} else {{")?;
                    for (k, instr) in else_branch.iter() {
                        write_indented(f, format_args!("instr {}: {}", k, instr), &mut buffer)?;
                    }
                }
                write!(f, "}}")
            }
            Branching::While { condition, loop_body } => {
                write_prep(condition, f)?;
                let neg = if condition.negation { " not" } else { "" };
                writeln!(f, "while{neg} {} {{", condition.value)?;
                let mut buffer = String::new();
                for (k, instr) in loop_body.iter() {
                    write_indented(f, format_args!("instr {}: {}", k, instr), &mut buffer)?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// Kind "structured" has no `Marker` instructions.
pub type Marker = super::Never;

#[must_use]
#[derive(Debug)]
struct Context {
    block_idx: usize,
    fallthrough_to: usize,
    last_is_br: Option<usize>,
    ret_seen: bool,
}

fn lift_block_iter(first_index: usize, instructions: &[resolved::Instr])
                   -> impl Iterator<Item=(usize, Instr)> + '_ {
    (first_index..).zip(instructions.iter().cloned().map(|instr| instr.map_kind(
        std::convert::identity,
        |_| unreachable!(),
        std::convert::identity,
        |_| unreachable!(),
        std::convert::identity,
    )))
}

struct ToStructured<'a> {
    function: &'a resolved::Function,
    dominators: DomRel,
}

impl<'a> ToStructured<'a> {
    fn run(&mut self, mut block_idx: usize, output: &mut Vec<(usize, Instr)>) -> Context {
        loop {
            let context = self.run_single(block_idx, output);
            if context.last_is_br.is_some() || context.ret_seen
                || self.dominators[context.fallthrough_to]
                .binary_search(&context.block_idx).is_err() { break context; }
            block_idx = context.fallthrough_to;
        }
    }

    fn run_single(&mut self, block_idx: usize, output: &mut Vec<(usize, Instr)>) -> Context {
        let block = &self.function.blocks[block_idx];
        if let ir::Instr::Marker(resolved::Marker::Ret) = block.last_instr() {
            let (_, instrs) = block.instructions.split_last().unwrap();
            output.extend(lift_block_iter(block.first_index, instrs));
            Context { block_idx, last_is_br: None, fallthrough_to: block_idx + 1, ret_seen: true }
        } else if let ir::Instr::Branch(br) = block.last_instr() {
            let (_, instrs) = block.instructions.split_last().unwrap();
            let (condition, negation) = match &br.method {
                BranchKind::Unconditional => {
                    output.extend(lift_block_iter(block.first_index, instrs));
                    return Context {
                        block_idx,
                        last_is_br: Some(br.dest),
                        fallthrough_to: block_idx + 1,
                        ret_seen: false,
                    };
                }
                // note that negation is flipped because of the control flow structure
                BranchKind::If(cond) => (cond.clone(), true),
                BranchKind::Unless(cond) => (cond.clone(), false),
            };
            let preparation = lift_block_iter(block.first_index, instrs).collect();
            let condition = Condition { value: condition, negation, preparation };
            let mut body = Vec::new();
            let body_ctxt = self.run(block_idx + 1, &mut body);
            if let Some(body_br) = body_ctxt.last_is_br {
                if body_br > block_idx { // forward br: if-then-else
                    assert_eq!(br.dest, body_ctxt.fallthrough_to);
                    let mut else_branch = Vec::new();
                    let ctxt = self.run(br.dest, &mut else_branch);
                    assert_eq!(ctxt.last_is_br, None);
                    assert_eq!(ctxt.fallthrough_to, body_br);
                    output.push((block.last_index(), Instr::Branch(Branching::If {
                        condition,
                        then_branch: body.into_boxed_slice(),
                        else_branch: Some(else_branch.into_boxed_slice()),
                    })));
                    Context { block_idx, fallthrough_to: body_br, last_is_br: None, ret_seen: false }
                } else { // backward br: while
                    assert_eq!(body_br, block_idx);
                    assert_eq!(br.dest, body_ctxt.fallthrough_to);
                    let loop_body = body.into_boxed_slice();
                    output.push((block.last_index(), Instr::Branch(Branching::While {
                        condition,
                        loop_body,
                    })));
                    Context { block_idx, fallthrough_to: br.dest, last_is_br: None, ret_seen: false }
                }
            } else { // no br: if-then
                assert_eq!(br.dest, body_ctxt.fallthrough_to);
                output.push((block.last_index(), Instr::Branch(Branching::If {
                    condition,
                    then_branch: body.into_boxed_slice(),
                    else_branch: None,
                })));
                Context { block_idx, fallthrough_to: br.dest, last_is_br: None, ret_seen: false }
            }
        } else {
            output.extend(lift_block_iter(block.first_index, &block.instructions));
            Context { block_idx, fallthrough_to: block_idx + 1, last_is_br: None, ret_seen: false }
        }
    }
}

impl resolved::Function {
    /// Transforms the function into structured [`Function`]s.
    pub fn to_structured(&self) -> Function {
        let mut body = Vec::new();
        let mut runner = ToStructured { function: self, dominators: get_dominators(self) };
        let ctxt = runner.run(self.entry_block, &mut body);
        assert_eq!(ctxt.last_is_br, None);
        assert!(ctxt.ret_seen);
        Function {
            parameter_count: self.parameter_count,
            local_var_count: self.local_var_count,
            body: body.into_boxed_slice(),
        }
    }
}

impl resolved::Functions {
    /// Transforms all the function into structured [`Function`]s.
    pub fn to_structured(&self) -> Functions {
        let functions = self.functions.iter().map(resolved::Function::to_structured).collect();
        Functions { functions, entry_function: self.entry_function }
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
            // to avoid optimizations messing up our tests
            assert!(!functions.functions.is_empty());
        }
    }
}
