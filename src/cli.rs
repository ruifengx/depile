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
use displaydoc::Display as DisplayDoc;
use parse_display::{Display, FromStr};
use thiserror::Error;
use clap::{AppSettings, Parser};

use crate::{block, Blocks, program::{self, display_program, read_program}};

/// Entry to the command line interface.
#[derive(Parser)]
#[clap(global_setting(AppSettings::PropagateVersion))]
#[clap(global_setting(AppSettings::UseLongFormatForHelpSubcommand))]
#[clap(setting(AppSettings::SubcommandRequiredElseHelp))]
#[clap(author, version, about)]
pub struct Cli {
    /// The input three-address code source file.
    input: PathBuf,
    /// The subcommand to execute.
    #[clap(short, long)]
    target_format: TargetFormat,
}

/// Supported target formats.
#[derive(Debug, Display, FromStr, Eq, PartialEq)]
pub enum TargetFormat {
    /// Print out the input file unchanged (disregarding whitespaces).
    Echo,
    /// Partition the input file as basic blocks.
    Blocks,
}

/// All kinds of errors that might happen during command line execution.
#[derive(Debug, DisplayDoc, Error)]
pub enum Error {
    /// "errors" from [`clap`], including requests such as `--version` or `--help`.
    #[displaydoc("{0}")]
    InvalidArguments(#[from] clap::Error),
    /// parse error: {0}
    InvalidInput(#[from] program::ParseError),
    /// malformed program: {0}
    MalformedInput(#[from] block::Error),
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
        match options.target_format {
            TargetFormat::Echo => {
                println!("{}", display_program(&program)?)
            }
            TargetFormat::Blocks => {
                let blocks = Blocks::try_from(program.as_ref())?;
                println!("{}", blocks);
            }
        }
        Ok(())
    }
}
