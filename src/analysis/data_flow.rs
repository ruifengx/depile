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

//! Data flow analyses.
//!
//! # Design Notes
//! We don't introduce dedicated ENTRY and EXIT nodes for analysis, that's because we are protected
//! by [`Marker::EnterProc`] and [`Marker::Ret`] instructions. [`Marker::EnterProc`] should never
//! become a target for branching, and [`Marker::Ret`] should never branch to another instruction.
//! This fact ensures that the first and the last blocks in a function are never part of a loop, so
//! not introducing ENTRY and EXIT nodes should not be causing us any problems.
//!
//! [`Marker::EnterProc`]: crate::ir::instr::basic::Marker::EnterProc
//! [`Marker::Ret`]: crate::ir::instr::basic::Marker::Ret

pub mod dominator;

use crate::ir::Block;
use crate::ir::instr::InstrExt;
use super::control_flow::{Dual, ControlFlowExt};
use super::lattice::JoinSemiLattice;

/// Result of a data flow analysis.
pub struct AnalysisRes<T> {
    /// `IN[B]` for some block `B`.
    pub r#in: T,
    /// `OUT[B]` for some block `B`.
    pub out: T,
}

/// Forward data flow analysis.
pub trait ForwardAnalysis<K: InstrExt>: JoinSemiLattice + Clone + Sized {
    /// The boundary condition: value for the ENTRY block.
    fn v_entry() -> Self;
    /// Transfer function `f` such that `OUT[B] = f(IN[B])`.
    ///
    /// `IN[B]` is provided as input, `OUT[B]` provided for update, the returned `bool` indicates
    /// whether or not the `OUT[B]` changed. For monotone frameworks, `IN[B] = f(OUT[B])` can be
    /// substituted with `OUT[B] = OUT[B] ⊓ f(IN[B])`. This allows using
    /// [`JoinSemiLattice::join_assign`] on `OUT[B]`.
    fn transfer_function(block_idx: usize, block: &Block<K>, input: &Self, output: &mut Self) -> bool;
    /// Run this forward data flow analysis.
    fn run_forward<F: ControlFlowExt<BlockKind=K>>(flow: F) -> Vec<AnalysisRes<Self>> {
        Inverted::<Self>::run_backward(Dual::from(flow)).into_iter()
            .map(|res| AnalysisRes {
                r#in: res.out.0,
                out: res.r#in.0,
            }).collect()
    }
}

/// Backward data flow analysis.
pub trait BackwardAnalysis<K: InstrExt>: JoinSemiLattice + Clone + Sized {
    /// The boundary condition: value for EXIT blocks.
    fn v_exit() -> Self;
    /// Transfer function `f` such that `IN[B] = f(OUT[B])`.
    ///
    /// `OUT[B]` is provided as input, `IN[B]` provided for update, the returned `bool` indicates
    /// whether or not the `IN[B]` changed. For monotone frameworks, `IN[B] = f(OUT[B])` can be
    /// substituted with `IN[B] = IN[B] ⊓ f(OUT[B])`. This allows using
    /// [`JoinSemiLattice::join_assign`] on `IN[B]`.
    fn transfer_function(block_idx: usize, block: &Block<K>, input: &mut Self, output: &Self) -> bool;
    /// Run this backward data flow analysis.
    fn run_backward<F: ControlFlowExt<BlockKind=K>>(flow: F) -> Vec<AnalysisRes<Self>> {
        let bottom = Self::bottom(&flow);
        let mut r#in = vec![bottom.clone(); flow.block_count()];
        let mut out = vec![bottom; flow.block_count()];
        #[allow(clippy::needless_range_loop)]
        for block_idx in 0..flow.block_count() {
            if flow.successor_blocks(block_idx).is_empty() {
                out[block_idx] = Self::v_exit();
            }
        }
        let mut changed = true;
        while changed {
            changed = false;
            #[allow(clippy::needless_range_loop)]
            for block_idx in 0..flow.block_count() {
                let block = flow.get_block(block_idx);
                changed |= out[block_idx].join_assign_many(
                    flow.successor_blocks(block_idx).into_iter()
                        .map(|successor| r#in[successor].clone())
                );
                Self::transfer_function(block_idx, block, &mut r#in[block_idx], &out[block_idx]);
            }
        }
        itertools::zip_eq(r#in.into_iter(), out.into_iter())
            .map(|(r#in, out)| AnalysisRes { r#in, out })
            .collect()
    }
}

#[repr(transparent)]
#[derive(Default, Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
struct Inverted<T>(T);

impl<T: JoinSemiLattice> JoinSemiLattice for Inverted<T> {
    fn bottom<K: InstrExt>(env: &dyn ControlFlowExt<BlockKind=K>) -> Self { Inverted(T::bottom(env)) }
    fn join_assign(&mut self, other: Self) -> bool {
        T::join_assign(&mut self.0, other.0)
    }
}

impl<K: InstrExt, T: ForwardAnalysis<K>> BackwardAnalysis<K> for Inverted<T> {
    fn v_exit() -> Self { Inverted(T::v_entry()) }
    fn transfer_function(block_idx: usize, block: &Block<K>, input: &mut Self, output: &Self) -> bool {
        T::transfer_function(block_idx, block, &output.0, &mut input.0)
    }
}
