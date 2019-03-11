// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Test utils

use std::collections::{HashMap, HashSet};
use primitives::H256;
use crate::{DBValue, ChangeSet, CommitSet, MetaDb, HashDb, KeySpace};

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct TestDb {
	pub data: HashMap<(KeySpace, H256), DBValue>,
	pub meta: HashMap<(KeySpace, Vec<u8>), DBValue>,
}

impl MetaDb for TestDb {
	type Error = ();

	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, ()> {
    // terrible access (for test only)
		Ok(self.meta.get(&(Vec::new(), key.to_vec())).cloned())
	}
}

impl HashDb for TestDb {
	type Error = ();
	type Hash = H256;

	fn get(&self, key_space: &KeySpace, key: &H256) -> Result<Option<DBValue>, ()> {
		Ok(self.data.get(&(key_space.clone(), *key)).cloned())
	}
}

impl TestDb {
	pub fn commit(&mut self, commit: &CommitSet<H256>) {
		self.data.extend(commit.data.inserted.iter().cloned());
		self.meta.extend(commit.meta.inserted.iter().cloned());
    // TODO keyspace delete
		for k in commit.data.deleted.iter() {
			self.data.remove(k);
		}
		self.meta.extend(commit.meta.inserted.iter().cloned());
		for k in commit.meta.deleted.iter() {
			self.meta.remove(k);
		}
	}

	pub fn data_eq(&self, other: &TestDb) -> bool {
		self.data == other.data
	}
}

pub fn make_changeset(inserted: &[(u64,u64)], deleted: &[(u64,u64)], deleted_ks: &[u64]) -> ChangeSet<H256> {
	ChangeSet {
		inserted: inserted
			.iter()
			.map(|(ks, v)| {
				((ks.to_be_bytes().to_vec(), H256::from_low_u64_be(*v)),
        H256::from_low_u64_be(*v).as_bytes().to_vec())
			})
			.collect(),
		deleted: deleted.iter().map(|v| (v.0.to_be_bytes().to_vec(), H256::from_low_u64_be(v.1))).collect(),
		deleted_keyspace: deleted_ks.iter().map(|v| (v.to_be_bytes().to_vec(), Vec::new())).collect(),
	}
}

pub fn make_commit(inserted: &[(u64,u64)], deleted: &[(u64,u64)], deleted_ks: &[u64]) -> CommitSet<H256> {
	CommitSet {
		data: make_changeset(inserted, deleted, deleted_ks),
		meta: ChangeSet::default(),
	}
}

pub fn make_changeset_ks0(inserted: &[u64], deleted: &[u64]) -> ChangeSet<H256> {
  let inserted_0: Vec<(u64,u64)> = inserted.iter().map(|i|(0u64,*i)).collect();
  let deleted_0: Vec<(u64,u64)> = deleted.iter().map(|i|(0u64,*i)).collect();
  make_changeset(&inserted_0[..], &deleted_0[..], &[])
}

pub fn make_commit_ks0(inserted: &[u64], deleted: &[u64]) -> CommitSet<H256> {
  let inserted_0: Vec<(u64,u64)> = inserted.iter().map(|i|(0u64,*i)).collect();
  let deleted_0: Vec<(u64,u64)> = deleted.iter().map(|i|(0u64,*i)).collect();
  make_commit(&inserted_0[..], &deleted_0[..], &[])
}


pub fn make_db(inserted: &[(u64,u64)]) -> TestDb {
	TestDb {
		data: inserted
			.iter()
			.map(|(ks,v)| {
				((ks.to_be_bytes().to_vec(), H256::from_low_u64_be(*v)),
        H256::from_low_u64_be(*v).as_bytes().to_vec())
			})
			.collect(),
		meta: Default::default(),
	}
}
pub fn make_db_ks0(inserted: &[u64]) -> TestDb {
	TestDb {
		data: inserted
			.iter()
			.map(|v| {
				((0u64.to_be_bytes().to_vec(), H256::from_low_u64_be(*v)),
        H256::from_low_u64_be(*v).as_bytes().to_vec())
			})
			.collect(),
		meta: Default::default(),
	}
}
