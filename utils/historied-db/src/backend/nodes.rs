// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
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

//! Linear backend possibly stored into multiple nodes.

use crate::rstd::marker::PhantomData;
use crate::rstd::btree_map::BTreeMap;
use crate::rstd::cell::RefCell;
use crate::rstd::vec::Vec;
use super::{LinearStorage};
use crate::historied::HistoriedValue;
use derivative::Derivative;
use crate::InitFrom;
use crate::backend::encoded_array::EncodedArrayValue;

pub trait EstimateSize {
	fn estimate_size(&self) -> usize;
}

/// Node storage metadata
pub trait NodesMeta: Sized {
	/// If true, then we apply a content size limit,
	/// otherwhise we use the number of node limit.
	const APPLY_SIZE_LIMIT: bool;
	/// The size limit to apply.
	const MAX_NODE_LEN: usize;
	/// Maximum number of items one.
	const MAX_NODE_ITEMS: usize;
	/// Maximum number of index items one.
	const MAX_INDEX_ITEMS: usize;
	/// Prefix to isolate nodes.
	const STORAGE_PREFIX: &'static [u8];
}

/// Backend storing nodes.
pub trait NodeStorage<V, S, D, M: NodesMeta>: Clone {
	fn get_node(&self, reference_key: &[u8], relative_index: u32) -> Option<Node<V, S, D, M>>;

	/// a default addressing scheme for storage that natively works
	/// as a simple key value storage.
	fn vec_address(reference_key: &[u8], relative_index: u32) -> Vec<u8> {
		let storage_prefix = M::STORAGE_PREFIX;
		let mut result = Vec::with_capacity(reference_key.len() + storage_prefix.len() + 8);
		result.extend_from_slice(storage_prefix);
		result.extend_from_slice(&(reference_key.len() as u32).to_be_bytes());
		result.extend_from_slice(reference_key);
		result.extend_from_slice(&relative_index.to_be_bytes());
		result
	}
}

pub trait NodeStorageMut<V, S, D, M> {
	fn set_node(&mut self, reference_key: &[u8], relative_index: u32, node: &Node<V, S, D, M>);
	fn remove_node(&mut self, reference_key: &[u8], relative_index: u32);
}

// Note that this should not be use out of test as it clone the whole btree map many times.
impl<V, S, D: Clone, M: NodesMeta> NodeStorage<V, S, D, M> for BTreeMap<Vec<u8>, Node<V, S, D, M>> {
	fn get_node(&self, reference_key: &[u8], relative_index: u32) -> Option<Node<V, S, D, M>> {
		let key = Self::vec_address(reference_key, relative_index);
		self.get(&key).cloned()
	}
}

impl<V, S, D: Clone, M: NodesMeta> NodeStorageMut<V, S, D, M> for BTreeMap<Vec<u8>, Node<V, S, D, M>> {
	fn set_node(&mut self, reference_key: &[u8], relative_index: u32, node: &Node<V, S, D, M>) {
		let key = Self::vec_address(reference_key, relative_index);
		self.insert(key, node.clone());
	}
	fn remove_node(&mut self, reference_key: &[u8], relative_index: u32) {
		let key = Self::vec_address(reference_key, relative_index);
		self.remove(&key);
	}
}

#[derive(Derivative)]
#[derivative(Clone(bound="D: Clone"))]
/// A node is a linear backend and some meta information.
pub struct Node<V, S, D, M> {
	data: D,
	changed: bool,
	reference_len: usize,
	_ph: PhantomData<(V, S, D, M)>,
}

/// Head is the entry node, it contains fetched nodes and additional
/// information about this backend state.
pub struct Head<V, S, D, M, B> {
	inner: Node<V, S, D, M>,
	/// end index - 1 at 0
	fetched: RefCell<Vec<Node<V, S, D, M>>>, // TODO consider smallvec
	old_start_node_index: u32,
	old_end_node_index: u32,
	// inclusive.
	start_node_index: u32,
	// non inclusive (next index to use)
	end_node_index: u32,
	len: usize,
	reference_key: Vec<u8>,
	backend: B,
}

impl<V, S, D: Clone, M, B> Head<V, S, D, M, B>
	where
		M: NodesMeta,
		B: NodeStorageMut<V, S, D, M>,
{
	pub fn flush_changes(&mut self) {
		for d in self.old_start_node_index .. self.start_node_index {
			self.backend.remove_node(&self.reference_key[..], d);
		}
		// this comparison is needed for the case we clear to 0 nodes indexes.
		let start_end = crate::rstd::cmp::max(self.end_node_index, self.old_start_node_index);
		self.old_start_node_index = self.start_node_index;
		for d in start_end .. self.old_end_node_index {
			self.backend.remove_node(&self.reference_key[..], d);
		}
		self.old_end_node_index = self.end_node_index;
		for (index, mut node) in self.fetched.borrow_mut().iter_mut().enumerate() {
			if node.changed {
				self.backend.set_node(&self.reference_key[..], self.end_node_index - 1 - index as u32 , node);
				node.changed = false;
			}
		}
	}
}

/// Information needed to initialize a new `Head`.
#[derive(Clone)]
pub struct InitHead<B> {
	/// The key of the historical value stored in nodes.
	pub key: Vec<u8>,
	/// The nodes backend.
	pub backend: B,
}

impl<V, S, D, M, B> InitFrom for Head<V, S, D, M, B>
	where
		D: InitFrom<Init = ()>,
		B: Clone,
{
	type Init = InitHead<B>; // TODO key to clone and backend refcell.
	fn init_from(init: Self::Init) -> Self {
		Head {
			inner: Node {
				data: D::init_from(()),
				changed: false,
				reference_len: 0,
				_ph: PhantomData,
			},
			fetched: RefCell::new(Vec::new()),
			old_start_node_index: 0,
			old_end_node_index: 0,
			start_node_index: 0,
			end_node_index: 0,
			len: 0,
			reference_key: init.key,
			backend: init.backend,
		}
	}
}

impl<V, S, D, M, B> Head<V, S, D, M, B>
	where
		D: InitFrom<Init = ()> + LinearStorage<V, S>,
		B: NodeStorage<V, S, D, M>,
		M: NodesMeta,
		S: EstimateSize,
		V: EstimateSize,
{
	// return node index (if node index is end_node_index this is in head),
	// and index in it.
	// Fetch is done backward
	fn fetch_node(&self, index: usize) -> Option<(usize, usize)> {
		if self.len > index {
			let mut start = self.len as usize - self.inner.data.len();
			if index >= start {
				return Some((self.end_node_index as usize, index - start));
			}
			let mut i = self.end_node_index as usize;
			while i > self.start_node_index as usize {
				i -= 1;
				let fetch_index = self.end_node_index as usize - i - 1;
				if let Some(node) = self.fetched.borrow().get(fetch_index) {
					start -= node.data.len();
					if index >= start {
						return Some((fetch_index, index - start));
					}
				} else {
					if let Some(node) = self.backend.get_node(self.reference_key.as_slice(), i as u32) {
						start -= node.data.len();
						let r = if index >= start {
							Some((self.fetched.borrow().len(), index - start))
						} else {
							None
						};
						self.fetched.borrow_mut().push(node);

						if r.is_some() {
							return r;
						}
					} else {
						return None;
					}
				}
			}
		}
		None
	}
}

/// Notice that all max node operation are only for push and pop operation.
/// 'insert' and 'remove' operation would need to use a call to 'realign'
/// operation to rewrite correctly the sizes.
impl<V, S, D, M, B> LinearStorage<V, S> for Head<V, S, D, M, B>
	where
		D: InitFrom<Init = ()> + LinearStorage<V, S>,
		B: NodeStorage<V, S, D, M>,
		M: NodesMeta,
		S: EstimateSize,
		V: EstimateSize,
{	
	// Fetched node index (end_node_index is head).
	// If true the node needs to be inserted.
	// Inner node linear storage index.
	type Index = (u32, D::Index);
	fn last(&self) -> Option<Self::Index> {
		if self.len == 0 {
			return None;
		}
		if let Some(inner_index) = self.inner.data.last() {
			return Some((self.end_node_index, inner_index));
		}

		let mut i = self.end_node_index;
		while i > self.start_node_index {
			i -= 1;
			let fetch_index = self.end_node_index - i - 1;
			let inner_index = if let Some(node) = self.fetched.borrow().get(fetch_index as usize) {
				node.data.last()
			} else {
				if let Some(node) = self.backend.get_node(self.reference_key.as_slice(), i) {
					let inner_index = node.data.last();
					self.fetched.borrow_mut().push(node);
					inner_index
				} else {
					None
				}
			};
			if let Some(inner_index) = inner_index {
				return Some((i, inner_index));
			}
		}
		None
	}
	fn previous_index(&self, mut index: Self::Index) -> Option<Self::Index> {
		if index.0 == self.end_node_index {
			if let Some(inner_index) = self.inner.data.last() {
				index.1 = inner_index;
				return Some(index);
			}
		}
		while index.0 > self.start_node_index {
			index.0 -= 1;
			let fetch_index = self.end_node_index - index.0 - 1;
			let inner_index = if let Some(node) = self.fetched.borrow().get(fetch_index as usize) {
				node.data.last()
			} else {
				if let Some(node) = self.backend.get_node(self.reference_key.as_slice(), index.0) {
					let inner_index = node.data.last();
					self.fetched.borrow_mut().push(node);
					inner_index
				} else {
					None
				}
			};
			if let Some(inner_index) = inner_index {
				index.1 = inner_index;
				return Some(index);
			}
		}
		None
	}
	fn lookup(&self, index: usize) -> Option<Self::Index> {
		// TODO see if could replace all fetch node with handle use and replace this.
		self.fetch_node(index).and_then(|(node_index, inner_node_index)| {
			if node_index == self.end_node_index as usize {
				self.inner.data.lookup(inner_node_index).map(|index| (node_index as u32, index))
			} else {
				self.fetched.borrow().get(node_index)
					.and_then(|inner|
					inner.data.lookup(inner_node_index).map(|index| (node_index as u32, index))
				)
			}
		})
	}
	fn len(&self) -> usize {
		self.len
	}
	fn get(&self, index: Self::Index) -> HistoriedValue<V, S> {
		if index.0 == self.end_node_index {
			return self.inner.data.get(index.1)
		}
		self.fetched.borrow()[index.0 as usize].data.get(index.1)
	}
	fn get_state(&self, index: Self::Index) -> S {
		if index.0 == self.end_node_index {
			return self.inner.data.get_state(index.1)
		}
		self.fetched.borrow()[index.0 as usize].data.get_state(index.1)
	}
	fn truncate_until(&mut self, split_off: usize) {
		let i = {
			let mut fetched_mut;
			let (node, i, ix) = match self.fetch_node(split_off) {
				Some((i, ix)) if i == self.end_node_index as usize =>  {
					(&mut self.inner, i, ix)
				},
				Some((i, ix)) => {
					fetched_mut = self.fetched.borrow_mut();
					if let Some(node) = fetched_mut.get_mut(i) {
						(node, i, ix)
					} else {
						unreachable!("fetch node returns existing index");
					}
				},
				None => {
					return;
				},
			};

			if ix > 0 {
				if M::APPLY_SIZE_LIMIT {
					let mut add_size = 0;
					for i in 0..ix {
						node.data.lookup(i).map(|h| {
							let h = node.data.get(h);
							add_size += h.value.estimate_size() + h.state.estimate_size()
						});
					}
					node.reference_len -= add_size;
				}
				node.changed = true;
				node.data.truncate_until(ix)
			}
			self.start_node_index += self.end_node_index - i as u32 - 1;
			if self.len > split_off {
				self.len -= split_off;
			} else {
				self.len = 0;
			}
			i
		};
		// reversed ordered.
		self.fetched.borrow_mut().truncate(i + 1);
	}
	fn push(&mut self, value: HistoriedValue<V, S>) {
		self.len += 1;
		let mut additional_size: Option<usize> = None;
		
		if !M::APPLY_SIZE_LIMIT {
			if self.inner.data.len() < M::MAX_NODE_ITEMS {
				self.inner.data.push(value);
				return;
			}
		} else {
			let add_size = value.value.estimate_size() + value.state.estimate_size(); 
			additional_size = Some(add_size);
			if self.inner.reference_len + add_size < M::MAX_NODE_LEN {
				self.inner.reference_len += add_size;
				self.inner.data.push(value);
				return;
			}
		}

		let add_size = additional_size.unwrap_or_else(||
			value.value.estimate_size() + value.state.estimate_size()
		);
		self.end_node_index += 1;
		let mut data = D::init_from(());
		data.push(value);
		let new_node = Node::<V, S, D, M> {
			data,
			changed: true,
			reference_len: add_size,
			_ph: PhantomData,
		};
		self.inner.changed = true;
		let prev = crate::rstd::mem::replace(&mut self.inner, new_node);
		self.fetched.borrow_mut().insert(0, prev);
	}
	fn insert(&mut self, index: Self::Index, h: HistoriedValue<V, S>) {
		let mut fetched_mut;
		let node = if index.0 == self.end_node_index {
			&mut self.inner
		} else {
			fetched_mut = self.fetched.borrow_mut();
			&mut fetched_mut[index.0 as usize]
		};

		if M::APPLY_SIZE_LIMIT {
			node.reference_len += h.value.estimate_size() + h.state.estimate_size();
		}
		node.changed = true;
		self.len += 1;
		node.data.insert(index.1, h);
	}
	fn remove(&mut self, index: Self::Index) {
		let mut fetched_mut;
		let node = if index.0 == self.end_node_index {
			&mut self.inner
		} else {
			fetched_mut = self.fetched.borrow_mut();
			&mut fetched_mut[index.0 as usize]
		};

		node.changed = true;
		self.len -= 1;

		if M::APPLY_SIZE_LIMIT {
			let h = node.data.get(index.1);
			node.reference_len -= h.value.estimate_size() + h.state.estimate_size();
		}
		node.data.remove(index.1);
	}
	fn pop(&mut self) -> Option<HistoriedValue<V, S>> {
		if self.len == 0 {
			return None;
		}

		if let Some(h) = self.inner.data.pop() {
			self.len -= 1;
			if self.inner.data.len() > 0 {
				if M::APPLY_SIZE_LIMIT {
					self.inner.reference_len -= h.value.estimate_size() + h.state.estimate_size();
				}
				self.inner.changed = true;
			} else {
				if self.fetched.borrow().len() == 0 {
					if self.len > self.inner.data.len() + 1 {
						self.fetch_node(self.len - self.inner.data.len() - 1);
					}
				}
				if self.fetched.borrow().len() > 0 {
					let removed = self.fetched.borrow_mut().remove(0);
					self.inner = removed;
				}
			}

			Some(h)
		} else {
			if self.fetched.borrow().len() == 0 {
				if self.len > self.inner.data.len() + 1 {
					self.fetch_node(self.len - self.inner.data.len() - 1);
				}
			}
			if self.fetched.borrow().len() > 0 {
				let removed = self.fetched.borrow_mut().remove(0);
				self.inner = removed;
				self.pop()
			} else {
				None
			}
		}
	}
	fn clear(&mut self) {
		self.start_node_index = 0;
		self.end_node_index = 0;
		self.len = 0;
		self.fetched.borrow_mut().clear();
		self.inner.reference_len = 0;
		self.inner.changed = true;
		self.inner.data.clear();
	}
	fn truncate(&mut self, at: usize) {
		let (in_head, i) = {
			let mut fetched_mut;
			let (node, i, ix, in_head) = match self.fetch_node(at) {
				Some((i, ix)) if i == self.end_node_index as usize =>  {
					(&mut self.inner, i, ix, true)
				},
				Some((i, ix)) => {
					fetched_mut = self.fetched.borrow_mut();
					if let Some(node) = fetched_mut.get_mut(i) {
						(node, i, ix, false)
					} else {
						unreachable!("fetch node returns existing index");
					}
				},
				None => {
					return;
				},
			};

			if ix < node.data.len() {

				if M::APPLY_SIZE_LIMIT {
					let mut add_size = 0;
					for i in ix..node.data.len() {
						node.data.lookup(i).map(|h| {
							let h = node.data.get(h);
							add_size += h.value.estimate_size() + h.state.estimate_size()
						});
					}
					node.reference_len -= add_size;
				}
				node.changed = true;
				node.data.truncate(ix)
			}
			(in_head, i)
		};
		if !in_head {
			let fetch_index = i as u32;
			self.end_node_index -= fetch_index + 1;
			if self.len > at {
				self.len = at;
			}
			let mut fetched_mut = self.fetched.borrow_mut();
			// reversed ordered.
			for i in 0..fetch_index + 1 {
				let removed = fetched_mut.remove(0);
				if i == fetch_index {
					self.inner = removed;
				}
			}
			self.inner.changed = true;
		}
	}
	fn emplace(&mut self, index: Self::Index, h: HistoriedValue<V, S>) {
		let mut fetched_mut;
		let node = if index.0 == self.end_node_index {
			&mut self.inner
		} else {
			fetched_mut = self.fetched.borrow_mut();
			&mut fetched_mut[index.0 as usize]
		};

		node.changed = true;

		if M::APPLY_SIZE_LIMIT {
			let h = node.data.get(index.1);
			node.reference_len -= h.value.estimate_size() + h.state.estimate_size();
			node.reference_len += h.value.estimate_size() + h.state.estimate_size();
		}
		node.data.emplace(index.1, h);
	}
}

// TODO use size of instead of u8
impl EstimateSize for Vec<u8> {
	fn estimate_size(&self) -> usize {
		self.len()
	}
}

impl EstimateSize for u32 {
	fn estimate_size(&self) -> usize {
		4
	}
}

impl EstimateSize for u16 {
	fn estimate_size(&self) -> usize {
		2
	}
}

impl<V: EstimateSize> EstimateSize for Option<V> {
	fn estimate_size(&self) -> usize {
		1 + self.as_ref().map(|v| v.estimate_size()).unwrap_or(0)
	}
}

impl<V: EstimateSize, S: EstimateSize> EstimateSize for crate::backend::in_memory::MemoryOnly<V, S> {
	fn estimate_size(&self) -> usize {
		unimplemented!("This should be avoided");
	}
}

//D is backend::encoded_array::EncodedArray<'_, std::vec::Vec<u8>, backend::encoded_array::DefaultVersion>
// B is std::collections::BTreeMap<std::vec::Vec<u8>, backend::nodes::Node<std::vec::Vec<u8>, u32, backend::encoded_array::EncodedArray<'_, std::vec::Vec<u8>, backend::encoded_array::DefaultVersion>, backend::nodes::test::MetaSize>>
impl<D, M, B> EncodedArrayValue for Head<Vec<u8>, u32, D, M, B>
	where
		D: EncodedArrayValue,
{
	fn from_slice(_slice: &[u8]) -> Self {
		// requires passing around the init item (the key need to be derived): this implementation is needed when we
		// EncodeArrayValue a head that refers to multiple head (those one needs to be instantiated)
		// from_slice & backend + base key. TODO start  by changing from_slice to use a init from
		// param.
		unimplemented!("Require a backend : similar to switch from default to init from, also required to parse meta: using specific size of version would allow fix length meta encode")
	}
}

impl<D, M, B> AsRef<[u8]> for Head<Vec<u8>, u32, D, M, B>
	where
		D: AsRef<[u8]>,
{
	fn as_ref(&self) -> &[u8] {
		self.inner.data.as_ref()
	}
}

impl<D, M, B> AsMut<[u8]> for Head<Vec<u8>, u32, D, M, B>
	where
		D: AsMut<[u8]>,
{
	fn as_mut(&mut self) -> &mut [u8] {
		self.inner.data.as_mut()
	}
}

impl<V, S, D, M, B> EstimateSize for Head<V, S, D, M, B> {
	fn estimate_size(&self) -> usize {
		self.inner.reference_len
	}
}

impl<V, S, D, M> EstimateSize for Node<V, S, D, M> {
	fn estimate_size(&self) -> usize {
		self.reference_len
	}
}

#[cfg(test)]
pub(crate) mod test {
	use super::*;

	use crate::backend::in_memory::MemoryOnly;
	use crate::backend::encoded_array::{EncodedArray, DefaultVersion};

	#[derive(Clone)]
	pub(crate) struct MetaSize;
	impl NodesMeta for MetaSize {
		const APPLY_SIZE_LIMIT: bool = true;
		const MAX_NODE_LEN: usize = 25;
		const MAX_NODE_ITEMS: usize = 0;
		const MAX_INDEX_ITEMS: usize = 5;
		const STORAGE_PREFIX: &'static [u8] = b"nodes1";
	}
	#[derive(Clone)]
	pub(crate) struct MetaNb;
	impl NodesMeta for MetaNb {
		const APPLY_SIZE_LIMIT: bool = false;
		const MAX_NODE_LEN: usize = 0;
		const MAX_NODE_ITEMS: usize = 3;
		const MAX_INDEX_ITEMS: usize = 5;
		const STORAGE_PREFIX: &'static [u8] = b"nodes2";
	}

	#[test]
	fn nodes_push_and_query() {
		nodes_push_and_query_inner::<MemoryOnly<Vec<u8>, u32>, MetaSize>();
		nodes_push_and_query_inner::<MemoryOnly<Vec<u8>, u32>, MetaNb>();
		nodes_push_and_query_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaSize>();
		nodes_push_and_query_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaNb>();
	}

	fn nodes_push_and_query_inner<D, M>()
		where
			D: InitFrom<Init = ()> + LinearStorage<Vec<u8>, u32> + Clone,
			M: NodesMeta + Clone,
	{
		let init_head = InitHead {
			backend: BTreeMap::<Vec<u8>, Node<Vec<u8>, u32, D, M>>::new(),
			key: b"any".to_vec(),
		};
		let mut head = Head::<Vec<u8>, u32, D, M, _>::init_from(init_head);
		assert_eq!(head.get_state_lookup(0), None);
		for i in 0usize..30 {
			let modu = i % 3;
			head.push(HistoriedValue {
				value: vec![i as u8; 2 + modu],
				state: i as u32,
			});
			for j in 0..i + 1 {
				assert_eq!(head.get_state_lookup(j), Some(j as u32));
			}
			assert_eq!(head.get_state_lookup(i + 1), None);
		}
	}

	#[test]
	fn test_linear_storage() {
		test_linear_storage_inner::<MemoryOnly<Vec<u8>, u32>, MetaSize>();
		test_linear_storage_inner::<MemoryOnly<Vec<u8>, u32>, MetaNb>();
		test_linear_storage_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaSize>();
		test_linear_storage_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaNb>();
	}
	fn test_linear_storage_inner<D, M>()
		where
			D: InitFrom<Init = ()> + LinearStorage<Vec<u8>, u32> + Clone,
			M: NodesMeta + Clone,
	{
		use crate::backend::test::{Value, State};
		let init_head = InitHead {
			backend: BTreeMap::<Vec<u8>, Node<Vec<u8>, u32, D, M>>::new(),
			key: b"any".to_vec(),
		};
		let mut head = Head::<Vec<u8>, u32, D, M, _>::init_from(init_head);
		crate::backend::test::test_linear_storage(&mut head);
	}
}
