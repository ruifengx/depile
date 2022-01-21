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

//! (Semi-)Lattice for data flow analysis.

use crate::analysis::control_flow::ControlFlowExt;
use crate::ir::instr::InstrExt;

/// Semi-lattice with a `⊓` operation.
///
/// # Note
/// This trait does not require a [`PartialOrd`], because the partial order implied by the
/// semi-lattice structure is usually different from the `#[derive(PartialOrd)]` order:
/// - The order implied by semi-lattice structure is somewhat "conservative", in that it is more
///   reluctant to specify an order for pairs of seemingly-unrelated elements; e.g. for sets, such
///   partial order is usually based on set inclusion.
/// - In contrast, the latter is in some sense more permissive, because it tends to make a
///   best-effort comparison for any pair of elements; e.g. [`PartialOrd`] for [`BTreeSet`] is in
///   fact a total order (a lexicographical order).
/// Fortunately, we make no use of the partial order itself in data flow analysis, so this fact
/// does not make a real obstacle.
pub trait JoinSemiLattice<K: InstrExt> {
    /// The `⊥` element for this semi-lattice: `⊥ ⊓ x = x`.
    fn bottom(env: &dyn ControlFlowExt<BlockKind=K>) -> Self;
    /// Update `self` to `self ⊓ other`, returning whether or not the value becomes different.
    fn join_assign(&mut self, other: Self) -> bool;
    /// Join all of `others` into `self`, returning whether or not the value becomes different.
    fn join_assign_many(&mut self, others: impl Iterator<Item=Self>) -> bool
        where Self: Sized {
        let mut changed = false;
        for other in others {
            changed |= self.join_assign(other);
        }
        changed
    }
}
