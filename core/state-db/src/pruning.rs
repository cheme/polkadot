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

//! Pruning window.
//!
//! For each block we maintain a list of nodes pending deletion.
//! There is also a global index of node key to block number.
//! If a node is re-inserted into the window it gets removed from
//! the death list.
//! The changes are journaled in the DB.

use std::collections::{HashMap, HashSet, VecDeque};
use std::mem;
use crate::codec::{Encode, Decode};
use crate::{CommitSet, Error, MetaDb, to_meta_key, Hash, KeySpace};
use log::{trace, warn};

const LAST_PRUNED: &[u8] = b"last_pruned";
const PRUNING_JOURNAL: &[u8] = b"pruning_journal";

/// See module documentation.
pub struct RefWindow<BlockHash: Hash, Key: Hash> {
	death_rows: VecDeque<DeathRow<BlockHash, Key>>,
	death_index: HashMap<(KeySpace, Key), u64>,
	// for individual death row we move index on reinsert, for 
	// keyspace we maintain multiple index : this is 
	// costy but sensible when considering keyspace deletion
	// to be less frequent than insertion into this keyspace
	death_index_keyspace: HashMap<KeySpace, Vec<u64>>,
	pending_number: u64,
	pending_records: Vec<(u64, JournalRecord<BlockHash, Key>)>,
	pending_prunings: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct DeathRow<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	journal_key: Vec<u8>,
	deleted: HashSet<(KeySpace, Key)>,
	/// value in map are keys that should not be deleted from KeySpace
	deleted_keyspace: HashMap<KeySpace, HashSet<Key>>,
}

// TODO this is stored as meta: this is therefore a breaking change!!
#[derive(Encode, Decode)]
struct JournalRecord<BlockHash: Hash, Key: Hash> {
	hash: BlockHash,
	inserted: Vec<(KeySpace, Key)>,
	deleted: Vec<(KeySpace, Key)>,
	deleted_keyspace: Vec<(KeySpace, Vec<Key>)>,
}

fn to_journal_key(block: u64) -> Vec<u8> {
	to_meta_key(PRUNING_JOURNAL, &block)
}

impl<BlockHash: Hash, Key: Hash> RefWindow<BlockHash, Key> {
	pub fn new<D: MetaDb>(db: &D) -> Result<RefWindow<BlockHash, Key>, Error<D::Error>> {
		let last_pruned = db.get_meta(&to_meta_key(LAST_PRUNED, &()))
			.map_err(|e| Error::Db(e))?;
		let pending_number: u64 = match last_pruned {
			Some(buffer) => u64::decode(&mut buffer.as_slice()).ok_or(Error::Decoding)? + 1,
			None => 0,
		};
		let mut block = pending_number;
		let mut pruning = RefWindow {
			death_rows: Default::default(),
			death_index: Default::default(),
			death_index_keyspace: Default::default(),
			pending_number: pending_number,
			pending_records: Default::default(),
			pending_prunings: 0,
		};
		// read the journal
		trace!(target: "state-db", "Reading pruning journal. Pending #{}", pending_number);
		loop {
			let journal_key = to_journal_key(block);
			match db.get_meta(&journal_key).map_err(|e| Error::Db(e))? {
				Some(record) => {
					let record: JournalRecord<BlockHash, Key> = Decode::decode(&mut record.as_slice()).ok_or(Error::Decoding)?;
					trace!(target: "state-db", "Pruning journal entry {} ({} inserted, {} deleted, {} deleted keyspace)",
						block,
						record.inserted.len(),
						record.deleted.len(),
						record.deleted_keyspace.len());
					pruning.import(&record.hash, journal_key, record.inserted.into_iter(), record.deleted, record.deleted_keyspace);
				},
				None => break,
			}
			block += 1;
		}
		Ok(pruning)
	}

	fn import<I: IntoIterator<Item=(KeySpace, Key)>>(
		&mut self,
		hash: &BlockHash,
		journal_key: Vec<u8>,
		inserted: I,
		deleted: Vec<(KeySpace, Key)>,
		deleted_keyspace: Vec<(KeySpace, Vec<Key>)>,
	) {
		// remove all re-inserted keys from death rows
		for k in inserted {
			if let Some(block) = self.death_index.remove(&k) {
				self.death_rows[(block - self.pending_number) as usize].deleted.remove(&k);
			}
			if let Some(blocks) = self.death_index_keyspace.get(&k.0) {
				for block in blocks.iter() {
					self.death_rows[(block - self.pending_number) as usize].deleted_keyspace.entry(k.0.clone())
						.or_insert_with(|| HashSet::new()).insert(k.1.clone());
				}
			}
		}

		// add new keys
		let imported_block = self.pending_number + self.death_rows.len() as u64;
		for k in deleted.iter() {
			self.death_index.insert(k.clone(), imported_block);
		}
		for k in deleted_keyspace.iter() {
			self.death_index_keyspace.entry(k.0.clone())
				.or_insert_with(|| Vec::new()).push(imported_block);
		}

		self.death_rows.push_back(
			DeathRow {
				hash: hash.clone(),
				deleted: deleted.into_iter().collect(),
				deleted_keyspace: deleted_keyspace.into_iter().map(|(k,v)|(k,v.into_iter().collect())).collect(),
				journal_key: journal_key,
			}
		);

	}

	pub fn window_size(&self) -> u64 {
		(self.death_rows.len() + self.pending_records.len() - self.pending_prunings) as u64
	}

	pub fn next_hash(&self) -> Option<BlockHash> {
		self.death_rows.get(self.pending_prunings).map(|r| r.hash.clone())
	}

	pub fn mem_used(&self) -> usize {
		0
	}

	pub fn pending(&self) -> u64 {
		self.pending_number + self.pending_prunings as u64
	}

	pub fn have_block(&self, hash: &BlockHash) -> bool {
		self.death_rows.iter().skip(self.pending_prunings).any(|r| r.hash == *hash) ||
			self.pending_records.iter().any(|(_, record)| record.hash == *hash)
	}

	/// Prune next block. Expects at least one block in the window. Adds changes to `commit`.
	pub fn prune_one(&mut self, commit: &mut CommitSet<Key>) {
		if let Some(pruned) = self.death_rows.get(self.pending_prunings) {
			trace!(target: "state-db", "Pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			let index = self.pending_number + self.pending_prunings as u64;
			commit.data.deleted.extend(pruned.deleted.iter().cloned());
			commit.data.deleted_keyspace.extend(pruned.deleted_keyspace.iter().map(|(k, v)|(k.clone(), v.iter().cloned().collect())));
			commit.meta.inserted.push(((Vec::new(), to_meta_key(LAST_PRUNED, &())), index.encode()));
			commit.meta.deleted.push((Vec::new(), pruned.journal_key.clone()));
			self.pending_prunings += 1;
		} else if let Some((block, pruned)) = self.pending_records.get(self.pending_prunings - self.death_rows.len()) {
			trace!(target: "state-db", "Pruning pending{:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			commit.data.deleted.extend(pruned.deleted.iter().cloned());
			commit.data.deleted_keyspace.extend(pruned.deleted_keyspace.iter().cloned());
			commit.meta.inserted.push(((Vec::new(), to_meta_key(LAST_PRUNED, &())), block.encode()));
			let journal_key = to_journal_key(*block);
			commit.meta.deleted.push((Vec::new(), journal_key));
			self.pending_prunings += 1;
		} else {
			warn!(target: "state-db", "Trying to prune when there's nothing to prune");
		}
	}

	/// Add a change set to the window. Creates a journal record and pushes it to `commit`
	pub fn note_canonical(&mut self, hash: &BlockHash, commit: &mut CommitSet<Key>) {
		trace!(target: "state-db", "Adding to pruning window: {:?} ({} inserted, {} deleted, {} keyspace delete)",
			hash, commit.data.inserted.len(),
			commit.data.deleted.len(),
			commit.data.deleted_keyspace.len());
		let inserted = commit.data.inserted.iter().map(|(k, _)| k.clone()).collect();
		let deleted = ::std::mem::replace(&mut commit.data.deleted, Vec::new());
		let deleted_keyspace = ::std::mem::replace(&mut commit.data.deleted_keyspace, Vec::new());
		let journal_record = JournalRecord {
			hash: hash.clone(),
			inserted,
			deleted,
			deleted_keyspace,
		};
		// Calculate pending block number taking pending canonicalizations into account, but not pending prunings
		// as these are always applied last.
		let block = self.pending_number + (self.death_rows.len() + self.pending_records.len()) as u64;
		let journal_key = to_journal_key(block);
		commit.meta.inserted.push(((Vec::new(), journal_key.clone()), journal_record.encode()));
		self.pending_records.push((block, journal_record));
	}

	/// Apply all pending changes
	pub fn apply_pending(&mut self) {
		for (block, journal_record) in mem::replace(&mut self.pending_records, Default::default()).into_iter() {
			trace!(target: "state-db", "Applying pruning window record: {}: {:?}", block, journal_record.hash);
			let journal_key = to_journal_key(block);
			self.import(&journal_record.hash, journal_key, journal_record.inserted.into_iter(), journal_record.deleted, journal_record.deleted_keyspace);
		}
		for _ in 0 .. self.pending_prunings {
			let pruned = self.death_rows.pop_front().expect("pending_prunings is always < death_rows.len()");
			trace!(target: "state-db", "Applying pruning {:?} ({} deleted)", pruned.hash, pruned.deleted.len());
			for k in pruned.deleted.iter() {
				self.death_index.remove(&k);
			}
			trace!(target: "state-db", "Applying pruning {:?} ({} keyspace deleted)", pruned.hash, pruned.deleted_keyspace.len());
			for k in pruned.deleted_keyspace.keys() {
				// reinsert case consider an exception so pay removal cost
				// otherwhise iterate and delete all range would be faster
				let reinsert = if let Some(mut v) = self.death_index_keyspace.remove(k) {
					if v.len() > 1 {
						// insertion of index by growing death_raws order so remove first is safe
						// we do not use vecdeque as it is not consider the common case
						Some(v.split_off(1))
					} else {
						None
					}
				} else { None };
				if let Some(v) = reinsert { self.death_index_keyspace.insert(k.clone(), v); }
			}
			self.pending_number += 1;
		}
		self.pending_prunings = 0;
	}

	/// Revert all pending changes
	pub fn revert_pending(&mut self) {
		self.pending_records.clear();
		self.pending_prunings = 0;
	}
}

#[cfg(test)]
mod tests {
	use super::RefWindow;
	use primitives::H256;
	use crate::CommitSet;
	use crate::test::{make_db_ks0, make_commit_ks0, TestDb};

	fn check_journal(pruning: &RefWindow<H256, H256>, db: &TestDb) {
		let restored: RefWindow<H256, H256> = RefWindow::new(db).unwrap();
		assert_eq!(pruning.pending_number, restored.pending_number);
		assert_eq!(pruning.death_rows, restored.death_rows);
		assert_eq!(pruning.death_index, restored.death_index);
	}

	#[test]
	fn created_from_empty_db() {
		let db = make_db_ks0(&[]);
		let pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		assert_eq!(pruning.pending_number, 0);
		assert!(pruning.death_rows.is_empty());
		assert!(pruning.death_index.is_empty());
	}

	#[test]
	fn prune_empty() {
		let db = make_db_ks0(&[]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		assert_eq!(pruning.pending_number, 0);
		assert!(pruning.death_rows.is_empty());
		assert!(pruning.death_index.is_empty());
		assert!(pruning.pending_prunings == 0);
		assert!(pruning.pending_records.is_empty());
	}

	#[test]
	fn prune_one() {
		let mut db = make_db_ks0(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit_ks0(&[4, 5], &[1, 3]);
		let h = H256::random();
		pruning.note_canonical(&h, &mut commit);
		db.commit(&commit);
		assert!(pruning.have_block(&h));
		pruning.apply_pending();
		assert!(pruning.have_block(&h));
		assert!(commit.data.deleted.is_empty());
		assert_eq!(pruning.death_rows.len(), 1);
		assert_eq!(pruning.death_index.len(), 2);
		assert!(db.data_eq(&make_db_ks0(&[1, 2, 3, 4, 5])));
		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		assert!(!pruning.have_block(&h));
		db.commit(&commit);
		pruning.apply_pending();
		assert!(!pruning.have_block(&h));
		assert!(db.data_eq(&make_db_ks0(&[2, 4, 5])));
		assert!(pruning.death_rows.is_empty());
		assert!(pruning.death_index.is_empty());
		assert_eq!(pruning.pending_number, 1);
	}

	#[test]
	fn prune_two() {
		let mut db = make_db_ks0(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit_ks0(&[4], &[1]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit_ks0(&[5], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db_ks0(&[1, 2, 3, 4, 5])));

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db_ks0(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db_ks0(&[3, 4, 5])));
		assert_eq!(pruning.pending_number, 2);
	}

	#[test]
	fn prune_two_pending() {
		let mut db = make_db_ks0(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit_ks0(&[4], &[1]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit_ks0(&[5], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db_ks0(&[1, 2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db_ks0(&[2, 3, 4, 5])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		pruning.apply_pending();
		assert!(db.data_eq(&make_db_ks0(&[3, 4, 5])));
		assert_eq!(pruning.pending_number, 2);
	}

	#[test]
	fn reinserted_survives() {
		let mut db = make_db_ks0(&[1, 2, 3]);
		let mut pruning: RefWindow<H256, H256> = RefWindow::new(&db).unwrap();
		let mut commit = make_commit_ks0(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit_ks0(&[2], &[]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		let mut commit = make_commit_ks0(&[], &[2]);
		pruning.note_canonical(&H256::random(), &mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db_ks0(&[1, 2, 3])));
		pruning.apply_pending();

		check_journal(&pruning, &db);

		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db_ks0(&[1, 2, 3])));
		let mut commit = CommitSet::default();
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db_ks0(&[1, 2, 3])));
		pruning.prune_one(&mut commit);
		db.commit(&commit);
		assert!(db.data_eq(&make_db_ks0(&[1, 3])));
		pruning.apply_pending();
		assert_eq!(pruning.pending_number, 3);
	}
}
