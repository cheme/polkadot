// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Client related externalities. TODO EMCH more comment
use hash_db::Hasher;

pub type CHOut<C> = <<C as Externalities>::H as Hasher>::Out;

/// TODO EMCH doc
pub trait Externalities {
  type H: Hasher;

	/// TODO EMCH doc
	/// !!! retrun none if the block has been pruned.
  /// TODO ???
	fn state_root_at(&self, block_number: u64) -> Option<CHOut<Self>>;
}
