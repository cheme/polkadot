// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, sync::Arc};

use kvdb::KeyValueDB;
use node_primitives::Hash;
use sp_trie::DBValue;
use hash_db::{HashDB, AsHashDB, Prefix, Hasher as _, BinaryHasher, HasherHybrid};
use hash_db::HashDBHybrid;

pub type Hasher = sp_state_machine::RefHasher<sp_core::Blake2Hasher>;

/// Immutable generated trie database with root.
pub struct SimpleTrie<'a> {
	pub db: Arc<dyn KeyValueDB>,
	pub overlay: &'a mut HashMap<Vec<u8>, Option<Vec<u8>>>,
}

impl<'a> AsHashDB<Hasher, DBValue> for SimpleTrie<'a> {
	fn as_hash_db(&self) -> &dyn hash_db::HashDB<Hasher, DBValue> { &*self }

	fn as_hash_db_mut<'b>(&'b mut self) -> &'b mut (dyn HashDB<Hasher, DBValue> + 'b) {
		&mut *self
	}
}

impl<'a> HashDB<Hasher, DBValue> for SimpleTrie<'a> {
	fn get(&self, key: &Hash, prefix: Prefix) -> Option<DBValue> {
		let key = sp_trie::prefixed_key::<Hasher>(key, prefix);
		if let Some(value) = self.overlay.get(&key) {
			return value.clone();
		}
		self.db.get(0, &key).expect("Database backend error")
	}

	fn contains(&self, hash: &Hash, prefix: Prefix) -> bool {
		self.get(hash, prefix).is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> Hash {
		let key = Hasher::hash(value);
		self.emplace(key, prefix, value.to_vec());
		key
	}

	fn emplace(&mut self, key: Hash, prefix: Prefix, value: DBValue) {
		let key = sp_trie::prefixed_key::<Hasher>(&key, prefix);
		self.overlay.insert(key, Some(value));
	}

	fn remove(&mut self, key: &Hash, prefix: Prefix) {
		let key = sp_trie::prefixed_key::<Hasher>(key, prefix);
		self.overlay.insert(key, None);
	}
}

impl<'a> HashDBHybrid<Hasher, DBValue> for SimpleTrie<'a> {
	fn insert_hybrid(
		&mut self,
		prefix: Prefix,
		value: &[u8],
		callback: fn(&[u8]) -> core::result::Result<Option<Hash>, ()>,
	) -> bool {
		if let Ok(result) = callback(value) {
			if let Some(key) = result {
				let key = sp_trie::prefixed_key::<Hasher>(&key, prefix);
				self.overlay.insert(key, Some(value.to_vec()));
			} else {
				let key = Hasher::hash(value);
				let key = sp_trie::prefixed_key::<Hasher>(&key, prefix);
				self.overlay.insert(key, Some(value.to_vec()));
			}
			true
		} else {
			false
		}
	}

	fn insert_branch_hybrid<
		I: Iterator<Item = Option<Hash>>,
	>(
		&mut self,
		prefix: Prefix,
		value: &[u8],
		no_child_value: &[u8],
		nb_children: usize,
		children: I,
		buffer: &mut <<Hasher as HasherHybrid>::InnerHasher as BinaryHasher>::Buffer,
	) -> Hash {
		let hash = Hasher::hash_hybrid(
			no_child_value,
			nb_children,
			children,
			buffer,
		);
		let key = sp_trie::prefixed_key::<Hasher>(&hash, prefix);
		self.overlay.insert(key, Some(value.to_vec()));
		hash
	}

	fn insert_branch_hybrid_proof<
		I: Iterator<Item = Option<Hash>>,
		I2: Iterator<Item = Hash>,
	>(
		&mut self,
		prefix: Prefix,
		value: &[u8],
		no_child_value: &[u8],
		nb_children: usize,
		children: I,
		additional_hashes: I2,
		buffer: &mut <<Hasher as HasherHybrid>::InnerHasher as BinaryHasher>::Buffer,
	) -> Option<Hash> {
		Hasher::hash_hybrid_proof(
			no_child_value,
			nb_children,
			children,
			additional_hashes,
			buffer,
		).map(|hash| {
			let key = sp_trie::prefixed_key::<Hasher>(&hash, prefix);
			self.overlay.insert(key, Some(value.to_vec()));
			hash
		})
	}
}



