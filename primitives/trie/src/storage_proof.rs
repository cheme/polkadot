// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

use sp_std::vec::Vec;
use codec::{Codec, Encode, Decode};
use hash_db::{Hasher, HashDB};

/// A proof that some set of key-value pairs are included in the storage trie. The proof contains
/// the storage values so that the partial storage backend can be reconstructed by a verifier that
/// does not already have access to the key-value pairs.
///
/// The proof consists of the set of serialized nodes in the storage trie accessed when looking up
/// the keys covered by the proof. Verifying the proof requires constructing the partial trie from
/// the serialized nodes and performing the key lookups.
#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
pub struct TrieNodesStorageProof {
	trie_nodes: Vec<Vec<u8>>,
}

/// Trait for proofs that can be use as a partial backend for verification.
pub trait StorageProof: Codec + sp_std::fmt::Debug + Sized + 'static {
	/// Merges multiple storage proofs covering potentially different sets of keys into one proof
	/// covering all keys. The merged proof output may be smaller than the aggregate size of the input
	/// proofs due to deduplication of trie nodes.
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self>;

	/// Returns a new empty proof.
	///
	/// An empty proof is capable of only proving trivial statements (ie. that an empty set of
	/// key-value pairs exist in storage).
	fn empty() -> Self;

	/// Returns whether this is an empty proof.
	fn is_empty(&self) -> bool;
}

impl TrieNodesStorageProof {
	/// Constructs a storage proof from a subset of encoded trie nodes in a storage backend.
	pub fn new(trie_nodes: Vec<Vec<u8>>) -> Self {
		TrieNodesStorageProof { trie_nodes }
	}

	/// Create an iterator over trie nodes constructed from the proof. The nodes are not guaranteed
	/// to be traversed in any particular order.
	pub fn iter_nodes(self) -> StorageProofNodeIterator {
		StorageProofNodeIterator::new(self)
	}

	/// Creates a `MemoryDB` from `Self`.
	pub fn into_memory_db<H: Hasher>(self) -> crate::MemoryDB<H> {
		self.into()
	}
}

impl StorageProof for TrieNodesStorageProof {
	fn merge<I>(proofs: I) -> Self where I: IntoIterator<Item=Self> {
		let trie_nodes = proofs.into_iter()
			.flat_map(|proof| proof.iter_nodes())
			.collect::<sp_std::collections::btree_set::BTreeSet<_>>()
			.into_iter()
			.collect();

		Self { trie_nodes }
	}

	fn empty() -> Self {
		TrieNodesStorageProof {
			trie_nodes: Vec::new(),
		}
	}

	fn is_empty(&self) -> bool {
		self.trie_nodes.is_empty()
	}
}

/// An iterator over trie nodes constructed from a storage proof. The nodes are not guaranteed to
/// be traversed in any particular order.
pub struct StorageProofNodeIterator {
	inner: <Vec<Vec<u8>> as IntoIterator>::IntoIter,
}

impl StorageProofNodeIterator {
	fn new(proof: TrieNodesStorageProof) -> Self {
		StorageProofNodeIterator {
			inner: proof.trie_nodes.into_iter(),
		}
	}
}

impl Iterator for StorageProofNodeIterator {
	type Item = Vec<u8>;

	fn next(&mut self) -> Option<Self::Item> {
		self.inner.next()
	}
}

impl<H: Hasher> From<TrieNodesStorageProof> for crate::MemoryDB<H> {
	fn from(proof: TrieNodesStorageProof) -> Self {
		let mut db = crate::MemoryDB::default();
		for item in proof.iter_nodes() {
			db.insert(crate::EMPTY_PREFIX, &item);
		}
		db
	}
}
