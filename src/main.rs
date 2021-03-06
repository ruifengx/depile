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

//! Translate three-address code back to C code.
//!
//! Three-address code format specification: [CS 380C].
//! [CS 380C]: https://www.cs.utexas.edu/users/mckinley/380C/labs/lab1.html.

#![warn(missing_docs)]

use depile::Cli;

fn main() {
    if let Err(err) = Cli::run() {
        eprintln!("{}", err);
    }
}
