// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate client interfaces.
#![warn(missing_docs)]

pub mod backend;
pub mod call_executor;
pub mod client;
pub mod cht;
pub mod execution_extensions;
pub mod in_mem;
pub mod light;
pub mod leaves;
pub mod notifications;
pub mod proof_provider;
pub mod export_import;

pub use sp_blockchain as blockchain;
pub use backend::*;
pub use notifications::*;
pub use call_executor::*;
pub use client::*;
pub use light::*;
pub use notifications::*;
pub use proof_provider::*;
pub use export_import::*;

pub use sp_state_machine::{StorageProof, ExecutionStrategy};
pub use sp_database::error::DatabaseError;

/// Usage Information Provider interface
///
pub trait UsageProvider<Block: sp_runtime::traits::Block> {
	/// Get usage info about current client.
	fn usage_info(&self) -> ClientInfo<Block>;
}

/// Utility methods for the client.
pub mod utils {
	use sp_blockchain::{HeaderBackend, HeaderMetadata, Error};
	use sp_runtime::traits::Block as BlockT;
	use std::borrow::Borrow;
	use crate::DatabaseError;

	/// Returns a function for checking block ancestry, the returned function will
	/// return `true` if the given hash (second parameter) is a descendent of the
	/// base (first parameter). If the `current` parameter is defined, it should
	/// represent the current block `hash` and its `parent hash`, if given the
	/// function that's returned will assume that `hash` isn't part of the local DB
	/// yet, and all searches in the DB will instead reference the parent.
	pub fn is_descendent_of<'a, Block: BlockT, T>(
		client: &'a T,
		current: Option<(Block::Hash, Block::Hash)>,
	) -> impl Fn(&Block::Hash, &Block::Hash) -> Result<bool, Error> + 'a
		where T: HeaderBackend<Block> + HeaderMetadata<Block, Error = Error>,
	{
		move |base, hash| {
			if base == hash { return Ok(false); }

			let current = current.as_ref().map(|(c, p)| (c.borrow(), p.borrow()));

			let mut hash = hash;
			if let Some((current_hash, current_parent_hash)) = current {
				if base == current_hash { return Ok(false); }
				if hash == current_hash {
					if base == current_parent_hash {
						return Ok(true);
					} else {
						hash = current_parent_hash;
					}
				}
			}

			let ancestor = sp_blockchain::lowest_common_ancestor(client, *hash, *base)?;

			Ok(ancestor.hash == *base)
		}
	}

	/// A state visitor implementation for a given backend at a given block.
	pub struct StateVisitorImpl<'a, B: BlockT, BA>(pub &'a BA, pub &'a B::Hash);

	impl<'a, B, BA> crate::StateVisitor for StateVisitorImpl<'a, B, BA>
		where
			B: BlockT,
			BA: crate::backend::Backend<B>,
	{
		fn state_visit(
			&self,
			mut visitor: impl FnMut(Option<&[u8]>, Vec<u8>, Vec<u8>) -> std::result::Result<(), DatabaseError>,
		) -> std::result::Result<(), DatabaseError> {
			let mut state = self.0.state_at(sp_runtime::generic::BlockId::Hash(self.1.clone()))
				.map_err(|e| DatabaseError(Box::new(e)))?;
			use sp_state_machine::Backend;
			let trie_state = state.as_trie_backend().expect("Snapshot runing on a trie backend.");

			let mut prev_child = None;
			let prev_child = &mut prev_child;
			let mut prefixed_storage_key = None;
			let prefixed_storage_key = &mut prefixed_storage_key;
			trie_state.for_key_values(|child, key, value| {
				if child != prev_child.as_ref() {
					*prefixed_storage_key = child.map(|ci| ci.prefixed_storage_key().into_inner());
					*prev_child = child.cloned();
				}
				visitor(
					prefixed_storage_key.as_ref().map(Vec::as_slice),
					key,
					value,
				).expect("Failure adding value to snapshot db.");
			}).map_err(|e| {
				let error: String = e.into();
				DatabaseError(Box::new(sp_blockchain::Error::Backend(error)))
			})?;
			Ok(())
		}
	}
}
