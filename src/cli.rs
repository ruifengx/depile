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

//! Command line interface support.

use std::path::PathBuf;
use thiserror::Error;
use displaydoc::Display as DisplayDoc;
use parse_display::{Display, FromStr};
use clap::{ArgEnum, Parser};

use crate::ir::{block, function, Blocks};
use crate::ir::program::{self, display_program, read_program};

/// Entry to the command line interface.
#[derive(Parser)]
#[clap(author, version, about)]
pub struct Cli {
    /// The input three-address code source file.
    #[clap(parse(from_os_str))]
    input: PathBuf,
    /// Output format.
    #[clap(short, long, arg_enum, default_value_t = Format::Functions)]
    target: Format,
}

/// Supported target formats.
#[derive(Debug, Display, FromStr, ArgEnum, Copy, Clone, Eq, PartialEq)]
#[display(style = "snake_case")]
pub enum Format {
    /// Print out the input file unchanged (disregarding whitespaces).
    Raw,
    /// Partition the input file as basic blocks.
    Blocks,
    /// Partition the input file as basic blocks, and group the basic blocks into functions.
    Functions,
}

/// All kinds of errors that might happen during command line execution.
#[derive(Debug, DisplayDoc, Error)]
pub enum Error {
    /// "errors" from [`clap`], including requests such as `--version` or `--help`.
    #[displaydoc("{0}")]
    InvalidArguments(#[from] clap::Error),
    /// parse error: {0}
    InvalidInput(#[from] program::ParseError),
    /// failed to parse into basic blocks: {0}
    MalformedBlocks(#[from] block::Error),
    /// failed to group into functions: {0}
    MalformedFunctions(#[from] function::Error),
    /// failed to read file: {0}
    Io(#[from] std::io::Error),
    /// cannot format the output: {0}
    CannotFormat(#[from] std::fmt::Error),
}

/// Result type for the command line interface.
pub type Result = std::result::Result<(), Error>;

impl Cli {
    /// Run the command line interface.
    pub fn run() -> Result {
        let options: Cli = Cli::try_parse()?;
        let contents = std::fs::read_to_string(&options.input)?;
        let program = read_program(&contents)?;
        match options.target {
            Format::Raw => {
                println!("{}", display_program(&program)?)
            }
            Format::Blocks => {
                let blocks = Blocks::try_from(program.as_ref())?;
                println!("{}", blocks);
            }
            Format::Functions => {
                let blocks = Blocks::try_from(program.as_ref())?;
                let functions = blocks.functions()?;
                println!("{}", functions);
            }
        }
        Ok(())
    }
}
