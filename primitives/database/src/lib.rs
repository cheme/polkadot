// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! The main database trait, allowing Substrate to store data persistently.

mod mem;
mod kvdb;

pub use mem::MemDb;
pub use crate::kvdb::as_database;

/// An identifier for a column.
pub type ColumnId = u32;

/// An alteration to the database.
#[derive(Clone)]
pub enum Change<H> {
	Set(ColumnId, Vec<u8>, Vec<u8>),
	Remove(ColumnId, Vec<u8>),
	Store(H, Vec<u8>),
	Release(H),
	DeleteChild(ColumnId, ChildBatchRemove<H>),
}

/// An alteration to the database that references the data.
pub enum ChangeRef<'a, H> {
	Set(ColumnId, &'a [u8], &'a [u8]),
	Remove(ColumnId, &'a [u8]),
	Store(H, &'a [u8]),
	Release(H),
	DeleteChild(ColumnId, ChildBatchRemove<H>),
}

/// A series of changes to the database that can be committed atomically. They do not take effect
/// until passed into `Database::commit`.
#[derive(Default, Clone)]
pub struct Transaction<H>(pub Vec<Change<H>>);

/// Removing child trie got different
/// implementation depending on database
/// capability.
#[derive(Clone)]
pub struct ChildBatchRemove<H> {
	/// For database without key iteration
	/// we delete by parsing the whole trie.
	pub root: H,

	/// Database that allows iteration can only
	/// delete all key using this keyspace.
	pub keyspace: Vec<u8>,
}

impl<H> Transaction<H> {
	/// Create a new transaction to be prepared and committed atomically.
	pub fn new() -> Self {
		Transaction(Vec::new())
	}
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	pub fn set(&mut self, col: ColumnId, key: &[u8], value: &[u8]) {
		self.0.push(Change::Set(col, key.to_vec(), value.to_vec()))
	}
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	pub fn set_from_vec(&mut self, col: ColumnId, key: &[u8], value: Vec<u8>) {
		self.0.push(Change::Set(col, key.to_vec(), value))
	}
	/// Remove the value of `key` in `col`.
	pub fn remove(&mut self, col: ColumnId, key: &[u8]) {
		self.0.push(Change::Remove(col, key.to_vec()))
	}
	/// Store the `preimage` of `hash` into the database, so that it may be looked up later with
	/// `Database::lookup`. This may be called multiple times, but `Database::lookup` but subsequent
	/// calls will ignore `preimage` and simply increase the number of references on `hash`.
	pub fn store(&mut self, hash: H, preimage: &[u8]) {
		self.0.push(Change::Store(hash, preimage.to_vec()))
	}
	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::lookup` to
	/// be unable to provide the preimage.
	pub fn release(&mut self, hash: H) {
		self.0.push(Change::Release(hash))
	}
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	pub fn delete_child(&mut self, col: ColumnId, child: ChildBatchRemove<H>) {
		self.0.push(Change::DeleteChild(col, child))
	}
}

pub trait Database<H: Clone>: Send + Sync {
	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit(&self, transaction: Transaction<H>) {
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => self.set(col, &key, &value),
				Change::Remove(col, key) => self.remove(col, &key),
				Change::Store(hash, preimage) => self.store(&hash, &preimage),
				Change::Release(hash) => self.release(&hash),
				Change::DeleteChild(col, child) => self.delete_child(col, child.clone()),
			}
		}
	}

	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit_ref<'a>(&self, transaction: &mut dyn Iterator<Item=ChangeRef<'a, H>>) {
		let mut tx = Transaction::new();
		for change in transaction {
			match change {
				ChangeRef::Set(col, key, value) => tx.set(col, key, value),
				ChangeRef::Remove(col, key) => tx.remove(col, key),
				ChangeRef::Store(hash, preimage) => tx.store(hash, preimage),
				ChangeRef::Release(hash) => tx.release(hash),
				ChangeRef::DeleteChild(col, child) => tx.delete_child(col, child.clone()),
			}
		}
		self.commit(tx);
	}

	/// Retrieve the value previously stored against `key` or `None` if
	/// `key` is not currently in the database.
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>>;
	
	/// Call `f` with the value previously stored against `key`.
	///
	/// This may be faster than `get` since it doesn't allocate.
	/// Use `with_get` helper function if you need `f` to return a value from `f`
	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.get(col, key).map(|v| f(&v));
	}
	
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	fn set(&self, col: ColumnId, key: &[u8], value: &[u8]) {
		let mut t = Transaction::new();
		t.set(col, key, value);
		self.commit(t);
	}
	/// Remove the value of `key` in `col`.
	fn remove(&self, col: ColumnId, key: &[u8]) {
		let mut t = Transaction::new();
		t.remove(col, key);
		self.commit(t);
	}

	/// Retrieve the first preimage previously `store`d for `hash` or `None` if no preimage is
	/// currently stored.
	fn lookup(&self, hash: &H) -> Option<Vec<u8>>;
	
	/// Call `f` with the preimage stored for `hash` and return the result, or `None` if no preimage
	/// is currently stored.
	///
	/// This may be faster than `lookup` since it doesn't allocate.
	/// Use `with_lookup` helper function if you need `f` to return a value from `f`
	fn with_lookup(&self, hash: &H, f: &mut dyn FnMut(&[u8])) {
		self.lookup(hash).map(|v| f(&v));
	}
	
	/// Store the `preimage` of `hash` into the database, so that it may be looked up later with
	/// `Database::lookup`. This may be called multiple times, but `Database::lookup` but subsequent
	/// calls will ignore `preimage` and simply increase the number of references on `hash`.
	fn store(&self, hash: &H, preimage: &[u8]) {
		let mut t = Transaction::new();
		t.store(hash.clone(), preimage);
		self.commit(t);
	}
	
	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::lookup` to
	/// be unable to provide the preimage.
	fn release(&self, hash: &H) {
		let mut t = Transaction::new();
		t.release(hash.clone());
		self.commit(t);
	}
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	fn delete_child(&self, col: ColumnId, child: ChildBatchRemove<H>) {
		let mut t = Transaction::new();
		t.delete_child(col, child);
		self.commit(t);
	}
}

/// Call `f` with the value previously stored against `key` and return the result, or `None` if
/// `key` is not currently in the database.
///
/// This may be faster than `get` since it doesn't allocate.
pub fn with_get<R, H: Clone>(db: &dyn Database<H>, col: ColumnId, key: &[u8], mut f: impl FnMut(&[u8]) -> R) -> Option<R> {
	let mut result: Option<R> = None;
	let mut adapter = |k: &_| { result = Some(f(k)); };
	db.with_get(col, key, &mut adapter);
	result
}

/// Call `f` with the preimage stored for `hash` and return the result, or `None` if no preimage
/// is currently stored.
///
/// This may be faster than `lookup` since it doesn't allocate.
pub fn with_lookup<R, H: Clone>(db: &dyn Database<H>, hash: &H, mut f: impl FnMut(&[u8]) -> R) -> Option<R> {
	let mut result: Option<R> = None;
	let mut adapter = |k: &_| { result = Some(f(k)); };
	db.with_lookup(hash, &mut adapter);
	result
}
