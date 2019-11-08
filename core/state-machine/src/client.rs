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

//! Client related externalities.
//! This gives access to client information through the state machine.
//! Those information are targetting previous block history.
pub use crate::testing::NoClient;

/// This is implementing part of client backend for a given past block.
pub trait Externalities: Send + Sync {
	/// Get value for a key at a previous block. TODO consider using hash??
	fn storage_at(&self, key: &[u8], block_number: u64) -> Option<Vec<u8>>;
}

impl<C: Externalities> Externalities for std::sync::Arc<C> {
	fn storage_at(&self, key: &[u8], block_number: u64) -> Option<Vec<u8>> {
		<C as Externalities>::storage_at(&*self, key, block_number)
	}
}
