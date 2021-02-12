// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The main database trait, allowing Substrate to store data persistently.

pub mod error;
mod mem;
mod kvdb;

use codec::{Encode, Decode};
pub use mem::MemDb;
pub use crate::kvdb::{as_database, arc_as_database};
pub use ordered::RadixTreeDatabase;

/// An identifier for a column.
pub type ColumnId = u32;

/// An alteration to the database.
#[derive(Clone)]
pub enum Change<H> {
	Set(ColumnId, Vec<u8>, Vec<u8>),
	Remove(ColumnId, Vec<u8>),
	Store(H, Vec<u8>),
	Release(H),
}

/// An alteration to the database that references the data.
pub enum ChangeRef<'a, H> {
	Set(ColumnId, &'a [u8], &'a [u8]),
	Remove(ColumnId, &'a [u8]),
	Store(H, &'a [u8]),
	Release(H),
}

/// A series of changes to the database that can be committed atomically. They do not take effect
/// until passed into `Database::commit`.
#[derive(Default, Clone)]
pub struct Transaction<H>(pub Vec<Change<H>>);

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
}

pub trait Database<H: Clone>: Send + Sync {
	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => self.set(col, &key, &value),
				Change::Remove(col, key) => self.remove(col, &key),
				Change::Store(hash, preimage) => self.store(&hash, &preimage),
				Change::Release(hash) => self.release(&hash),
			}?;
		}

		Ok(())
	}

	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit_ref<'a>(&self, transaction: &mut dyn Iterator<Item=ChangeRef<'a, H>>) -> error::Result<()> {
		let mut tx = Transaction::new();
		for change in transaction {
			match change {
				ChangeRef::Set(col, key, value) => tx.set(col, key, value),
				ChangeRef::Remove(col, key) => tx.remove(col, key),
				ChangeRef::Store(hash, preimage) => tx.store(hash, preimage),
				ChangeRef::Release(hash) => tx.release(hash),
			}
		}
		self.commit(tx)
	}

	/// Retrieve the value previously stored against `key` or `None` if
	/// `key` is not currently in the database.
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>>;

	/// Check if the value exists in the database without retrieving it.
	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		self.get(col, key).is_some()
	}

	/// Call `f` with the value previously stored against `key`.
	///
	/// This may be faster than `get` since it doesn't allocate.
	/// Use `with_get` helper function if you need `f` to return a value from `f`
	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.get(col, key).map(|v| f(&v));
	}

	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	fn set(&self, col: ColumnId, key: &[u8], value: &[u8]) -> error::Result<()> {
		let mut t = Transaction::new();
		t.set(col, key, value);
		self.commit(t)
	}
	/// Remove the value of `key` in `col`.
	fn remove(&self, col: ColumnId, key: &[u8]) -> error::Result<()> {
		let mut t = Transaction::new();
		t.remove(col, key);
		self.commit(t)
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
	fn store(&self, hash: &H, preimage: &[u8]) -> error::Result<()> {
		let mut t = Transaction::new();
		t.store(hash.clone(), preimage);
		self.commit(t)
	}

	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::lookup` to
	/// be unable to provide the preimage.
	fn release(&self, hash: &H) -> error::Result<()> {
		let mut t = Transaction::new();
		t.release(hash.clone());
		self.commit(t)
	}
}

impl<H: Clone> Database<H> for std::sync::Arc<dyn Database<H>> {
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		self.as_ref().commit(transaction)
	}

	fn commit_ref<'a>(&self, transaction: &mut dyn Iterator<Item=ChangeRef<'a, H>>) -> error::Result<()> {
		self.as_ref().commit_ref(transaction)
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		self.as_ref().get(col, key)
	}

	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.as_ref().with_get(col, key, f)
	}

	fn set(&self, col: ColumnId, key: &[u8], value: &[u8]) -> error::Result<()> {
		self.as_ref().set(col, key, value)
	}

	fn remove(&self, col: ColumnId, key: &[u8]) -> error::Result<()> {
		self.as_ref().remove(col, key)
	}

	fn lookup(&self, hash: &H) -> Option<Vec<u8>> {
		self.as_ref().lookup(hash)
	}

	fn with_lookup(&self, hash: &H, f: &mut dyn FnMut(&[u8])) {
		self.as_ref().with_lookup(hash, f)
	}

	fn store(&self, hash: &H, preimage: &[u8]) -> error::Result<()> {
		self.as_ref().store(hash, preimage)
	}

	fn release(&self, hash: &H) -> error::Result<()> {
		self.as_ref().release(hash)
	}
}

impl<H: Clone> Database<H> for std::sync::Arc<dyn OrderedDatabase<H>> {
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		self.as_ref().commit(transaction)
	}

	fn commit_ref<'a>(&self, transaction: &mut dyn Iterator<Item=ChangeRef<'a, H>>) -> error::Result<()> {
		self.as_ref().commit_ref(transaction)
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		self.as_ref().get(col, key)
	}

	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.as_ref().with_get(col, key, f)
	}

	fn set(&self, col: ColumnId, key: &[u8], value: &[u8]) -> error::Result<()> {
		self.as_ref().set(col, key, value)
	}

	fn remove(&self, col: ColumnId, key: &[u8]) -> error::Result<()> {
		self.as_ref().remove(col, key)
	}

	fn lookup(&self, hash: &H) -> Option<Vec<u8>> {
		self.as_ref().lookup(hash)
	}

	fn with_lookup(&self, hash: &H, f: &mut dyn FnMut(&[u8])) {
		self.as_ref().with_lookup(hash, f)
	}

	fn store(&self, hash: &H, preimage: &[u8]) -> error::Result<()> {
		self.as_ref().store(hash, preimage)
	}

	fn release(&self, hash: &H) -> error::Result<()> {
		self.as_ref().release(hash)
	}
}

pub trait OrderedDatabase<H: Clone>: Database<H> {
	/// Iterate on value from the database.
	fn iter<'a>(&'a self, col: ColumnId) -> Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a>;

	/// Iterate on value over a given prefix, the prefix can be removed from
	/// the resulting keys.
	fn prefix_iter<'a>(
		&'a self,
		col: ColumnId,
		prefix: &'a [u8],
		trim_prefix: bool,
	) -> Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a>;

	/// Iterate from a start position (same seek then iterate).
	fn iter_from<'a>(
		&'a self,
		col: ColumnId,
		start: &[u8],
	) -> Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a>;

	/// Clear by prefix
	fn clear_prefix(
		&self,
		col: ColumnId,
		prefix: &[u8],
	) {
		// Default implementation got problematic memory consumption,
		// specific implementation should be use for backend targetting
		// large volume.
		let keys: Vec<_> = self.prefix_iter(col, prefix, false).map(|kv| kv.0).collect();
		for key in keys {
			// iterating on remove individually is bad for perf.
			self.remove(col, key.as_slice());
		}
	}
}

impl<H> std::fmt::Debug for dyn Database<H> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "Database")
	}
}

impl<H> std::fmt::Debug for dyn OrderedDatabase<H> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "OrderedDatabase")
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

mod ordered {
	use super::*;
	use codec::Codec;
	use std::sync::Arc;
	use parking_lot::RwLock;
	use radix_tree::{Derivative, Value, TreeConf, Node,
		radix::{RadixConf, impls::Radix256Conf},
		children::{Children, Children256},
	};

	use core::fmt::Debug;

	radix_tree::flatten_children!(
		!value_bound: Codec,
		Children256Flatten,
		Node256Flatten,
		Node256LazyHashBackend,
		Children256,
		Radix256Conf,
		radix_tree::backends::LazyBackend<
			radix_tree::backends::ArcBackend<
				radix_tree::backends::TransactionBackend<WrapColumnDb<H>>
			>
		>,
		H,
		{ H: Debug + PartialEq + Clone}
	);

	#[derive(Clone)]
	pub struct WrapColumnDb<H> {
		inner: Arc<dyn Database<H>>,
		col: ColumnId,
		prefix: Option<&'static [u8]>,
	}

	macro_rules! subcollection_prefixed_key {
		($prefix: ident, $key: ident) => {
			let mut prefixed_key;
			let $key = if let Some(k) = $prefix {
				prefixed_key = Vec::with_capacity(k.len() + $key.len());
				prefixed_key.extend_from_slice(&k[..]);
				prefixed_key.extend_from_slice(&$key[..]);
				&prefixed_key[..]
			} else {
				&$key[..]
			};
		}
	}

	impl<H: Clone> radix_tree::backends::ReadBackend for WrapColumnDb<H> {
		fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
			let prefix = &self.prefix;
			subcollection_prefixed_key!(prefix, k);
			self.inner.get(self.col, k)
		}
	}

	#[derive(Clone)]
	/// Ordered database implementation through a indexing radix tree overlay.
	pub struct RadixTreeDatabase<H: Clone + PartialEq + Debug> {
		inner: Arc<dyn Database<H>>,
		trees: Arc<RwLock<Vec<radix_tree::Tree<Node256LazyHashBackend<Vec<u8>, H>>>>>,
	}

	impl<H: Clone + PartialEq + Debug> RadixTreeDatabase<H> {
		/// Create new radix tree database.
		pub fn new(inner: Arc<dyn Database<H>>) -> Self {
			RadixTreeDatabase {
				inner,
				trees: Arc::new(RwLock::new(Vec::<radix_tree::Tree<Node256LazyHashBackend<Vec<u8>, H>>>::new())),
			}
		}
		fn lazy_column_init(&self, col: ColumnId) {
			let index = col as usize;
			loop {
				let len = self.trees.read().len();
				if len <= index {
					self.trees.write().push(radix_tree::Tree::from_backend(
						radix_tree::backends::ArcBackend::new(
							radix_tree::backends::TransactionBackend::new(
								WrapColumnDb {
									inner: self.inner.clone(),
									col: len as u32,
									prefix: None,
								}
							)
						)
					))
				} else {
					break;
				}
			}
		}
	}

	impl<H: Clone + PartialEq + Debug + Default> Database<H> for RadixTreeDatabase<H> {
		fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
			self.lazy_column_init(col);
			self.trees.write()[col as usize].get_mut(key).cloned()
		}
		fn lookup(&self, _hash: &H) -> Option<Vec<u8>> {
			unimplemented!("No hash lookup on radix tree layer");
		}
		fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
			for change in transaction.0.into_iter() {
				match change {
					Change::Set(col, key, value) => {
						self.lazy_column_init(col);
						self.trees.write()[col as usize].insert(key.as_slice(), value);
					},
					Change::Remove(col, key) => {
						self.lazy_column_init(col);
						self.trees.write()[col as usize].remove(key.as_slice());
					},
					Change::Store(_hash, _preimage) => {
						unimplemented!("No hash lookup on radix tree layer");
					},
					Change::Release(_hash) => {
						unimplemented!("No hash lookup on radix tree layer");
					},
				};
			}

			let len = self.trees.read().len();
			let mut transaction = Transaction::<H>::default();
			for i in 0..len {
				self.trees.write()[i].commit();
			}
			for i in 0..len {
				for (key, change) in {
					let tree = &self.trees.read()[i];
					let change = tree.init.0.write().drain_changes();
					change
				} {
					if let Some(value) = change {
						transaction.set(i as u32, key.as_slice(), value.as_slice());
					} else {
						transaction.remove(i as u32, key.as_slice());
					}
				}
			}

			Ok(())
		}
	}

	impl<H: Clone + PartialEq + Debug + Default + 'static> OrderedDatabase<H> for RadixTreeDatabase<H> {
		fn iter<'a>(&'a self, col: ColumnId) -> Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a> {
			self.lazy_column_init(col);
			let tree = self.trees.read()[col as usize].clone();
			Box::new(tree.owned_iter())
		}
		fn prefix_iter<'a>(
			&'a self,
			col: ColumnId,
			prefix: &'a [u8],
			trim_prefix: bool,
		) -> Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a> {
			self.lazy_column_init(col);
			let tree = self.trees.read()[col as usize].clone();
			if trim_prefix {
				let len = prefix.len();
				Box::new(tree.owned_prefix_iter(prefix).map(move |mut kv| {
					kv.0 = kv.0.split_off(len);
					kv
				}))
			} else {
				Box::new(tree.owned_prefix_iter(prefix))
			}
		}
		fn iter_from<'a>(
			&'a self,
			col: ColumnId,
			start: &[u8],
		) -> Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a> {
			self.lazy_column_init(col);
			let tree = self.trees.read()[col as usize].clone();
			Box::new(tree.owned_iter_from(start))
		}
	}
}

#[derive(Clone, Debug, Encode, Decode)]
/// Different storage mode.
pub enum SnapshotDBMode {
	/// Do not apply binary diff between consecutive values.
	NoDiff,
	/// Use xdelta3 VcDiff.
	Xdelta3Diff,
}

impl Default for SnapshotDBMode {
	fn default() -> Self {
		SnapshotDBMode::NoDiff
	}
}

#[derive(Clone, Debug, Default, Encode, Decode)]
/// Configuration of snapshot db conf.
pub struct SnapshotDbConf {
	/// Is snapshot db active.
	pub enabled: bool,
	/// Should we use this db value instead of trie value in state machine
	/// when possible.
	pub primary_source: bool,
	/// Do we use node backend.
	pub no_node_backend: bool,
	/// Do we maintain key modification journaling for pruning?
	pub journal_pruning: bool,
	/// Should we debug value access in state machine against the trie values.
	pub debug_assert: bool,
	/// Lower block support, this should block reorg before it.
	/// TODO use actual block nb type.
	pub start_block: Option<u32>,
	/// Diff usage.
	pub diff_mode: SnapshotDBMode,
	/// If defined, pruning window size to apply, `None` for archive.
	pub pruning: Option<Option<u32>>,
	/// Lazy pruning window. (place holder TODO unimplemented)
	pub lazy_pruning: Option<u32>,
	/// Technical field to identify if the conf has been initialized.
	/// TODO remove and have Variable::is_defined function in remote historied_db
	pub lazy_set: bool,
}

/// Implement exposed acces method to the snapshot db.
pub trait SnapshotDb {
	/// Disable snapshot db and remove its content.
	fn clear_snapshot_db(&self) -> error::Result<()>;

	/// Change current snapshot db behavior.
	fn update_running_conf(
		&self,
		use_as_primary: Option<bool>,
		debug_assert: Option<bool>,
		pruning_window: Option<Option<u32>>,
		lazy_pruning_window: Option<u32>,
	) -> error::Result<()>;
}

/// The error type for snapshot database operations.
#[derive(Debug)]
pub enum SnapshotDbError {
	Unsupported,
}

impl std::fmt::Display for SnapshotDbError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			SnapshotDbError::Unsupported => {
				write!(f, "Unsupported snapshot db.")
			},
		}
	}
}

impl std::error::Error for SnapshotDbError {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		None
	}
}

fn unsupported_error() -> error::Result<()> {
	Err(error::DatabaseError(Box::new(SnapshotDbError::Unsupported)))
}

/// Use '()' when no snapshot implementation.
impl SnapshotDb for () {
	fn clear_snapshot_db(&self) -> error::Result<()> {
		unsupported_error()
	}

	fn update_running_conf(
		&self,
		_use_as_primary: Option<bool>,
		_debug_assert: Option<bool>,
		_pruning_window: Option<Option<u32>>,
		_lazy_pruning_window: Option<u32>,
	) -> error::Result<()> {
		unsupported_error()
	}
}
