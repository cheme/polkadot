// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

pub use sp_blockchain as blockchain;
pub use backend::*;
pub use notifications::*;
pub use call_executor::*;
pub use client::*;
pub use light::*;
pub use notifications::*;
pub use proof_provider::*;

pub use sp_state_machine::{StorageProof, ExecutionStrategy, CloneableSpawn};
pub use sp_state_machine::backend::{ProofCheckBackend as ProofCheckBackendT,
	ProofBackendStateFor, InstantiableStateBackend, HashDBNodesTransaction};
pub use sp_runtime::traits::HashFor;

/// DB backend for state supported by client db implementation.
pub type DbStorage<Block> = DbStorageHash<HashFor<Block>>;
/// DB backend for state supported by client db implementation.
pub type DbStorageHash<H> = std::sync::Arc<dyn sp_state_machine::Storage<H>>;

/// Static definition of the proving backend
pub type ProvingBackend<Block> = ProvingBackendHash<HashFor<Block>>;
/// Static definition of the proving backend
pub type ProvingBackendHash<H> = sp_state_machine::ProvingBackend<sp_state_machine::MemoryDB<H>, H>;

/// Trie backend proof check.
pub type ProofCheckBackend<Block> = ProofCheckBackendHash<HashFor<Block>>;
/// Static definition of the verification backend
pub type ProofCheckBackendHash<H> = sp_state_machine::TrieBackend<sp_state_machine::MemoryDB<H>, H>;

/// State backend configuration for default `sp_trie` patricia trie.
pub type TrieStateBackend<Block> = TrieStateBackendHash<HashFor<Block>>;
/// State backend configuration for default `sp_trie` patricia trie.
pub type TrieStateBackendHash<H> = sp_state_machine::TrieBackend<DbStorageHash<H>, H>;

/// Static definition of the state backend to use with tests.
/// TODO EMCH rename to TrieBackendState + the same alias in bench
pub type DbState<B> = sp_state_machine::TrieBackend<
	std::sync::Arc<dyn sp_state_machine::Storage<HashFor<B>>>, HashFor<B>
>;

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
}
