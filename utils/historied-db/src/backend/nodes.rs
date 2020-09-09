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
use crate::rstd::cell::{RefCell, Ref, RefMut};
use crate::rstd::rc::Rc;
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
/// TODO use associated constant
/// TODO make byte size version an associated constant as
/// it has a tech cost.
pub trait NodesMeta: Sized {
	fn max_head_len() -> usize;
	/// for imbrincated nodes we can limit
	/// by number of head items instead of
	/// max_head_len.
	fn max_head_items() -> Option<usize>;
	fn max_node_len() -> usize;
	fn max_node_items() -> Option<usize>;
	fn max_index_len() -> usize;
	fn storage_prefix() -> &'static [u8];
}

/// Backend storing nodes.
pub trait NodeStorage<V, S, D, M: NodesMeta>: Clone {
	fn get_node(&self, reference_key: &[u8], relative_index: u32) -> Option<Node<V, S, D, M>>;

	/// a default addressing scheme for storage that natively works
	/// as a simple key value storage.
	fn vec_address(reference_key: &[u8], relative_index: u32) -> Vec<u8> {
		let storage_prefix = M::storage_prefix();
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
	fn len(&self) -> usize {
		self.len
	}
	// TODO notice that it sequentially fetch from the end (some variant of S could go the over way).
	fn st_get(&self, index: usize) -> Option<HistoriedValue<V, S>> {
		match self.fetch_node(index) {
			Some((i, ix)) if i == self.end_node_index as usize =>  {
				self.inner.data.st_get(ix)
			},
			Some((i, ix)) => {
				if let Some(node) = self.fetched.borrow().get(i) {
					node.data.st_get(ix)
				} else {
					unreachable!("fetch node returns existing index");
				}
			},
			None => {
				None
			},
		}
	}
	fn get_state(&self, index: usize) -> Option<S> {
		match self.fetch_node(index) {
			Some((i, ix)) if i == self.end_node_index as usize =>  {
				self.inner.data.get_state(ix)
			},
			Some((i, ix)) => {
				if let Some(node) = self.fetched.borrow().get(i) {
					node.data.get_state(ix)
				} else {
					unreachable!("fetch node returns existing index");
				}
			},
			None => {
				None
			},
		}
	}
	fn truncate_until(&mut self, split_off: usize) {
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
			let mut add_size = 0;
			for i in 0..ix {
				node.data.st_get(i)
					.map(|h| add_size += h.value.estimate_size() + h.state.estimate_size());
			}
			node.reference_len -= add_size;
			node.changed = true;
			node.data.truncate_until(ix)
		}
		self.start_node_index = i as u32;
		if self.len > split_off {
			self.len -= split_off;
		} else {
			self.len = 0;
		}
		// reversed ordered.
		self.fetched.borrow_mut().truncate(i + 1);
	}
	fn push(&mut self, value: HistoriedValue<V, S>) {
		self.len += 1;
		let mut additional_size: Option<usize> = None;
		
		if let Some(nb) = M::max_head_items() {
			if self.inner.data.len() < nb {
				self.inner.data.push(value);
				return;
			}
		} else {
			let add_size = value.value.estimate_size() + value.state.estimate_size(); 
			additional_size = Some(add_size);
			if self.inner.reference_len + add_size < M::max_head_len() {
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
	fn insert(&mut self, index: usize, h: HistoriedValue<V, S>) {
		let mut fetched_mut;
		let (node, ix) = match self.fetch_node(index) {
			Some((i, ix)) if i == self.end_node_index as usize =>  {
				(&mut self.inner, ix)
			},
			Some((i, ix)) => {
				fetched_mut = self.fetched.borrow_mut();
				if let Some(node) = fetched_mut.get_mut(i) {
					(node, ix)
				} else {
					unreachable!("fetch node returns existing index");
				}
			},
			None => {
				self.push(h);
				return;
			},
		};

		node.reference_len += h.value.estimate_size() + h.state.estimate_size();
		node.changed = true;
		self.len += 1;
		node.data.insert(ix, h);
	}
	fn remove(&mut self, index: usize) {
		let mut fetched_mut;
		let (node, ix) = match self.fetch_node(index) {
			Some((i, ix)) if i == self.end_node_index as usize =>  {
				(&mut self.inner, ix)
			},
			Some((i, ix)) => {
				fetched_mut = self.fetched.borrow_mut();
				if let Some(node) = fetched_mut.get_mut(i) {
					(node, ix)
				} else {
					unreachable!("fetch node returns existing index");
				}
			},
			None => {
				return;
			},
		};

		node.changed = true;
		self.len -= 1;
		node.data.st_get(ix)
			.map(|h| node.reference_len -= h.value.estimate_size() + h.state.estimate_size());
		node.data.remove(ix);
	}
	fn pop(&mut self) -> Option<HistoriedValue<V, S>> {
		if self.len == 0 {
			return None;
		}

		if let Some(h) = self.inner.data.pop() {
			self.len -= 1;
			if self.inner.data.len() > 0 {
				self.inner.reference_len -= h.value.estimate_size() + h.state.estimate_size();
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
			let mut add_size = 0;
			for i in ix..node.data.len() {
				node.data.st_get(i)
					.map(|h| add_size += h.value.estimate_size() + h.state.estimate_size());
			}
			node.reference_len -= add_size;
			node.changed = true;
			node.data.truncate(ix)
		}
		if !in_head {
			self.end_node_index = i as u32;
			if self.len > at {
				self.len = at;
			}
			let mut fetched_mut = self.fetched.borrow_mut();
			// reversed ordered.
			for i in 0..self.end_node_index + 1 {
				let removed = fetched_mut.remove(0);
				if i == self.end_node_index {
					self.inner = removed;
				}
			}
			self.inner.changed = true;
		}
	}
	fn emplace(&mut self, at: usize, h: HistoriedValue<V, S>) {
		let mut fetched_mut;
		let (node, ix) = match self.fetch_node(at) {
			Some((i, ix)) if i == self.end_node_index as usize =>  {
				(&mut self.inner, ix)
			},
			Some((i, ix)) => {
				fetched_mut = self.fetched.borrow_mut();
				if let Some(node) = fetched_mut.get_mut(i) {
					(node, ix)
				} else {
					unreachable!("fetch node returns existing index");
				}
			},
			None => {
				return;
			},
		};

		node.changed = true;
		node.data.st_get(ix)
			.map(|h| node.reference_len -= h.value.estimate_size() + h.state.estimate_size());
		node.reference_len += h.value.estimate_size() + h.state.estimate_size();
		node.data.emplace(ix, h);
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
		fn max_head_len() -> usize { 25 }
		fn max_head_items() -> Option<usize> { None }
		fn max_node_len() -> usize { 30 }
		fn max_node_items() -> Option<usize> { None }
		fn max_index_len() -> usize {
			unimplemented!("no index");
		}
		fn storage_prefix() -> &'static [u8] { b"nodes1" }
	}
	#[derive(Clone)]
	pub(crate) struct MetaNb;
	impl NodesMeta for MetaNb {
		fn max_head_len() -> usize { 25 }
		fn max_head_items() -> Option<usize> { Some(3) }
		fn max_node_len() -> usize { 30 }
		fn max_node_items() -> Option<usize> { Some(3) }
		fn max_index_len() -> usize {
			unimplemented!("no index");
		}
		fn storage_prefix() -> &'static [u8] { b"nodes2" }
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
		assert_eq!(head.get_state(0), None);
		for i in 0usize..30 {
			let modu = i % 3;
			head.push(HistoriedValue {
				value: vec![i as u8; 2 + modu],
				state: i as u32,
			});
			for j in 0..i + 1 {
				assert_eq!(head.get_state(j), Some(j as u32));
			}
			assert_eq!(head.get_state(i + 1), None);
		}
	}
}
