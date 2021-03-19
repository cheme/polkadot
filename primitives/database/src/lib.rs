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
	Store(ColumnId, H, Vec<u8>),
	Reference(ColumnId, H),
	Release(ColumnId, H),
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
	/// `Database::get`. This may be called multiple times, but subsequent
	/// calls will ignore `preimage` and simply increase the number of references on `hash`.
	pub fn store(&mut self, col: ColumnId, hash: H, preimage: Vec<u8>) {
		self.0.push(Change::Store(col, hash, preimage))
	}
	/// Increase the number of references for `hash` in the database.
	pub fn reference(&mut self, col: ColumnId, hash: H) {
		self.0.push(Change::Reference(col, hash))
	}
	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::get` to
	/// be unable to provide the preimage.
	pub fn release(&mut self, col: ColumnId, hash: H) {
		self.0.push(Change::Release(col, hash))
	}
}

pub trait Database<H: Clone + AsRef<[u8]>>: Send + Sync {
	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()>;

	/// Retrieve the value previously stored against `key` or `None` if
	/// `key` is not currently in the database.
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>>;

	/// Check if the value exists in the database without retrieving it.
	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		self.get(col, key).is_some()
	}

	/// Check value size in the database possibly without retrieving it.
	fn value_size(&self, col: ColumnId, key: &[u8]) -> Option<usize> {
		self.get(col, key).map(|v| v.len())
	}

	/// Call `f` with the value previously stored against `key`.
	///
	/// This may be faster than `get` since it doesn't allocate.
	/// Use `with_get` helper function if you need `f` to return a value from `f`
	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.get(col, key).map(|v| f(&v));
	}
}

impl<H: Clone + AsRef<[u8]>> Database<H> for std::sync::Arc<dyn Database<H>> {
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		self.as_ref().commit(transaction)
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		self.as_ref().get(col, key)
	}

	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.as_ref().with_get(col, key, f)
	}
}

impl<H: Clone + AsRef<[u8]>> Database<H> for std::sync::Arc<dyn OrderedDatabase<H>> {
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		self.as_ref().commit(transaction)
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		self.as_ref().get(col, key)
	}

	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.as_ref().with_get(col, key, f)
	}
}

pub trait OrderedDatabase<H: Clone + AsRef<[u8]>>: Database<H> {
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
	) -> error::Result<()> {
		let mut transaction = Transaction::new();
		// Default implementation got problematic memory consumption,
		// specific implementation should be use for backend targetting
		// large volume other multiple transactions.
		for key in self.prefix_iter(col, prefix, false).map(|kv| kv.0) {
			// iterating on remove individually is bad for perf.
			transaction.remove(col, key.as_slice());
		}
		self.commit(transaction)?;

		Ok(())
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
pub fn with_get<R, H: Clone + AsRef<[u8]>>(
	db: &dyn Database<H>,
	col: ColumnId,
	key: &[u8], mut f: impl FnMut(&[u8]) -> R
) -> Option<R> {
	let mut result: Option<R> = None;
	let mut adapter = |k: &_| { result = Some(f(k)); };
	db.with_get(col, key, &mut adapter);
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

	/// Trait alias for macro compatibility.
	/// TODO try alternative in radix_tree crate
	pub trait AsRefu8: AsRef<[u8]> { }

	impl<T: AsRef<[u8]>> AsRefu8 for T { }

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
		{ H: Debug + PartialEq + Clone + AsRefu8 }
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

	impl<H: Clone + AsRef<[u8]>> radix_tree::backends::ReadBackend for WrapColumnDb<H> {
		fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
			let prefix = &self.prefix;
			subcollection_prefixed_key!(prefix, k);
			self.inner.get(self.col, k)
		}
	}

	#[derive(Clone)]
	/// Ordered database implementation through a indexing radix tree overlay.
	pub struct RadixTreeDatabase<H: Clone + PartialEq + Debug + AsRef<[u8]>> {
		inner: Arc<dyn Database<H>>,
		trees: Arc<RwLock<Vec<radix_tree::Tree<Node256LazyHashBackend<Vec<u8>, H>>>>>,
	}

	impl<H: Clone + PartialEq + Debug + AsRef<[u8]>> RadixTreeDatabase<H> {
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

	impl<H> Database<H> for RadixTreeDatabase<H>
		where H: Clone + PartialEq + Debug + Default + AsRef<[u8]>,
	{
		fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
			self.lazy_column_init(col);
			self.trees.write()[col as usize].get_mut(key).cloned()
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
					Change::Store(_col, _hash, _preimage) => {
						unimplemented!("No hash lookup on radix tree layer");
					},
					Change::Reference(_col, _hash) => {
						unimplemented!("No hash lookup on radix tree layer");
					},
					Change::Release(_col, _hash) => {
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

	impl<H> OrderedDatabase<H> for RadixTreeDatabase<H>
		where H: Clone + PartialEq + Debug + Default + 'static + AsRef<[u8]>,
	{
		fn iter<'a>(&'a self, col: ColumnId) -> ChildStateIter<'a> {
			self.lazy_column_init(col);
			let tree = self.trees.read()[col as usize].clone();
			Box::new(tree.owned_iter())
		}
		fn prefix_iter<'a>(
			&'a self,
			col: ColumnId,
			prefix: &'a [u8],
			trim_prefix: bool,
		) -> ChildStateIter<'a> {
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
		) -> ChildStateIter<'a> {
			self.lazy_column_init(col);
			let tree = self.trees.read()[col as usize].clone();
			Box::new(tree.owned_iter_from(start))
		}
	}
}

/// Full key value state iterator at a given state.
/// First element is top state iterator, second element
/// is children states iterator.
pub type StateIter<'a> = (
	ChildStateIter<'a>,
	Box<dyn Iterator<Item = (Vec<u8>, ChildStateIter<'a>)> + 'a>,
);

/// Full key value state iterator at a given state,
/// from a given parent state.
pub type ChildStateIter<'a> = Box<dyn Iterator<Item = (Vec<u8>, Vec<u8>)> + 'a>;

/// Delta key value state iterator at a given state.
pub type StateIterDelta<'a> = Box<
	dyn Iterator<Item = (Option<Vec<u8>>, ChildStateIterDelta<'a>)> + 'a,
>;

/// Delta key value state iterator at a given state,
/// from a given parent state.
pub type ChildStateIterDelta<'a> = Box<
	dyn Iterator<Item = (Vec<u8>, Option<Vec<u8>>)> + 'a,
>;
