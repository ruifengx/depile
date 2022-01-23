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

use crate::ir::{Block, Blocks, Instr, Program};
use crate::ir::instr::{basic, stripped, HasDest};

impl stripped::Functions {
    /// Destruct the functions into blocks.
    pub fn destruct(&self) -> basic::Blocks {
        let mut blocks: Vec<basic::Block> = Vec::new();
        let mut start_block = Vec::new();
        let mut total_blocks = 0;
        for func in &self.functions {
            start_block.push(func.entry_block + total_blocks);
            total_blocks += func.blocks.len();
        }
        for (n, func) in self.functions.iter().enumerate() {
            for (k, block) in func.blocks.iter().enumerate() {
                let mut instructions = Vec::new();
                let mut first_index = block.first_index;
                if k == func.entry_block {
                    first_index -= 1;
                    instructions.push(Instr::Marker(
                        basic::Marker::EnterProc(func.local_var_count * 8)));
                }
                instructions.extend(block.instructions.iter().map(|instr| instr.clone().map_kind(
                    std::convert::identity,
                    |br| br.map_dest(|t| t + start_block[n]),
                    |ip| ip.map_dest(|t| start_block[t]),
                    |stripped::Marker::Ret| basic::Marker::Ret(func.parameter_count * 8),
                    std::convert::identity,
                )));
                let instructions = instructions.into_boxed_slice();
                blocks.push(Block { first_index, instructions })
            }
        }
        Blocks { blocks, entry_block: start_block[self.entry_function] }
    }
}

impl basic::Blocks {
    /// Flatten the basic blocks into a continuous program.
    pub fn flatten(&self) -> Box<Program> {
        let mut program = vec![Instr::Nop];
        let mut first_instr = Vec::new();
        let mut total_instr = 1;
        for (n, block) in self.blocks.iter().enumerate() {
            if n == self.entry_block { total_instr += 1; }
            first_instr.push(total_instr + 1);
            total_instr += block.instructions.len();
        }
        for (n, block) in self.blocks.iter().enumerate() {
            if n == self.entry_block { program.push(Instr::Marker(basic::Marker::EntryPc)); }
            for instr in block.instructions.iter() {
                program.push(instr.clone().map_dest(|t| first_instr[t]));
            }
        }
        program.push(Instr::Nop);
        program.into_boxed_slice()
    }
}

#[cfg(test)]
mod tests {
    use crate::samples;
    use crate::ir::Blocks;
    use crate::ir::program::read_program;

    #[test]
    fn test_functions_destruct_flatten() {
        for input in samples::ALL_SAMPLES {
            let program = read_program(input).unwrap();
            let blocks = Blocks::try_from(program.as_ref()).unwrap();
            let functions = blocks.functions().unwrap();
            let new_blocks = functions.destruct();
            let new_program = new_blocks.flatten();
            assert_eq!(program, new_program);
        }
    }
}
