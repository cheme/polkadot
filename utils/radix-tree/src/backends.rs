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

//! Node backends for storing tree nodes.

use crate::{TreeConf, PositionFor, KeyIndexFor,
	NodeBox, RadixConf,
	PrefixKeyConf, Node, PrefixKey, AlignmentFor,
	ValueState};
use crate::radix::{MaskFor, MaskKeyByte};
use crate::children::NodeIndex;
use alloc::vec::Vec;
use alloc::rc::Rc;
use alloc::boxed::Box;
use alloc::vec;
use codec::{Encode, Decode, Input};
use core::cell::RefCell;

/// Node backend management.
pub trait Backend: Clone {
	type Index;

	/// Get a root node from the backend.
	fn get_root(&self) -> Option<(Vec<u8>, Self::Index)>;

	fn get_node(&self, index: Self::Index) -> Option<Vec<u8>>;

	fn update_node(&self, index: Self::Index, node: Vec<u8>) -> Option<Self::Index>;

	fn remove_node(&self, index: Self::Index);

	fn set_new_node(&self, node: Vec<u8>) -> Self::Index;

	/// Root call back.
	fn set_root(&self, root: Self::Index);
}

impl Backend for () {
	type Index = ();
	fn get_root(&self) -> Option<(Vec<u8>, Self::Index)> { None }

	fn get_node(&self, _index: Self::Index) -> Option<Vec<u8>> { None }

	fn update_node(&self, _index: Self::Index, _node: Vec<u8>) -> Option<Self::Index> { None }

	fn remove_node(&self, _index: Self::Index) { }

	fn set_new_node(&self, _node: Vec<u8>) -> Self::Index { () }

	fn set_root(&self, _root: Self::Index) { }
}

/// Node backend management.
pub trait TreeBackend<N: TreeConf>: Clone {
	const ACTIVE: bool = true;
	// fuse node only on commit allows making change
	// without querying additional nodes, but also
	// creates empty node until commit.
	const FUSE_ON_COMMIT: bool = false;
	/// Always use () if inactive or ChildState if active
	/// TODO consider moving to Tree (leaks node type in this crate)
	type ChildState: crate::WithChildState<crate::Node<N>>;

	/// Inner backend used.
	type Backend: Backend<Index = Self::Index>;
	type Index;

	/// TODO consider keeping backend out of node.
	fn backend(&self) -> &Self::Backend;

	/// Get a root node from the backend.
	/// TODO specialize return node to commit recursively on drop.
	fn get_root(init: &Self::Backend) -> Option<NodeBox<N>>;

	/// Get next defined node.
	fn get_next_child_index(&self, from: Option<KeyIndexFor<N>>) -> Option<KeyIndexFor<N>>;
	// TODO usefull ? fetch children?
	fn get_node(&self, index: Self::Index) -> Option<NodeBox<N>>;

	// TODO replace by backend_hash_index -> bool ?
	fn fetch_children_index(&self, at: KeyIndexFor<N>) -> Option<Self::Index>;
	/// Get a child node from the backend.
	/// TODO use Self::Index instead of usize??
	fn fetch_children(&mut self, at: KeyIndexFor<N>) -> Option<Option<NodeBox<N>>>;

	fn fetch_children_no_cache(&self, at: KeyIndexFor<N>) -> Option<NodeBox<N>>;

//	fn resolve_parent(&self) -> Option<NodeBox<N>>;

	// TODO this is not really good, probably need to be updated
	// redundant with node -> children method
	// -> new nb_children for node-children to set size and have
	// update from fetch not changing it.
	/// Original number of children stored in backend.
	fn fetch_nb_children(&mut self) -> Option<usize>;

	// TODO replace by backend_hash_value -> bool ?
	fn fetch_value_index (&self) -> Option<Self::Index>;

	fn fetch_value(&mut self) -> Option<Option<N::Value>>;

	fn fetch_value_no_cache(&self) -> Option<N::Value>;

	/// Indicate a child node was change.
	/// TODO could consider adding position to avoid iterating on all child
	/// TODO remove
	fn set_change(&mut self);

	fn set_children_change(&mut self) {
		self.set_change()
	}

	fn set_prefix_change(&mut self);
	
	/// Delete a node.
	/// Does flush change immediatly.
	fn delete(self);

	/// Flush changes that happens to a node.
	/// return new backend index if changed.
	fn commit_change(node: &mut NodeBox<N>, remove_node: &mut Vec<N::Backend>) -> Option<Self::Index>;

	fn commit_change_fuse(node: &mut NodeBox<N>, remove_node: &mut Vec<N::Backend>) -> Option<Self::Index> {
		if Self::FUSE_ON_COMMIT
			&& node.number_child() == 1
			&& !node.has_value()
		{
			Node::<N>::fuse_child(node, remove_node);
		}
		Self::commit_change(node, remove_node)
	}

	fn new_node_backend(backend: &Self::Backend) -> Self;

	/// Value state is stored in backend.
	fn value_state(&self) -> ValueState;

	/// Value state is stored in backend.
	fn set_value_state(&mut self, state: ValueState);

	/// Clear content to allow rewriting a different node instead.
	fn clear_content(&mut self);
}


impl<N: TreeConf> TreeBackend<N> for () {
	const ACTIVE: bool = false;
	type ChildState = Box<Node<N>>;

	type Backend = ();
	type Index = ();

	fn backend(&self) -> &Self::Backend { self }

	fn get_root(_init: &Self::Backend) -> Option<NodeBox<N>> { None }

	fn get_node(&self, _index: Self::Index) -> Option<NodeBox<N>> {
		None
	}
	fn get_next_child_index(&self, _index: Option<KeyIndexFor<N>>) -> Option<KeyIndexFor<N>> {
		None
	}
	fn fetch_children(&mut self, _at: KeyIndexFor<N>) -> Option<Option<NodeBox<N>>> {
		None
	}

	fn fetch_children_index(&self, _at: KeyIndexFor<N>) -> Option<Self::Index> {
		None
	}

	fn fetch_children_no_cache(&self, _at: KeyIndexFor<N>) -> Option<NodeBox<N>> {
		None
	}

	fn fetch_nb_children(&mut self) -> Option<usize> {
		None
	}

	fn fetch_value_index (&self) -> Option<Self::Index> {
		None
	}

	fn fetch_value(&mut self) -> Option<Option<N::Value>> {
		None
	}

	fn fetch_value_no_cache(&self) -> Option<N::Value> {
		None
	}

	fn set_change(&mut self) {
	}
	
	fn set_prefix_change(&mut self) {
	}

	fn delete(self) {
	}

	fn commit_change(_node: &mut NodeBox<N>, _remove_node: &mut Vec<N::Backend>) -> Option<Self::Index> {
		None
	}

	fn new_node_backend(_backend: &Self::Backend) -> Self {
		()
	}
	fn value_state(&self) -> ValueState {
		ValueState::Resolved
	}
	fn set_value_state(&mut self, _state: ValueState) {
		()
	}

	fn clear_content(&mut self) { }
}

/// Backend containing encoded nodes.
#[derive(Clone, Debug)]
pub struct TestBackend {
	encoded_nodes: Vec<(Vec<u8>, Option<usize>)>,
	free_node: usize,
	new_node_on_update: bool,
	root_index: usize,
}

impl Default for TestBackend {
	fn default() -> Self {
		TestBackend {
			encoded_nodes: Vec::new(),
			free_node: 0,
			new_node_on_update: true,
			root_index: 0,
		}
	}
}

impl TestBackend {
	fn remove(&mut self, index: usize) {
		if let Some(node) = self.encoded_nodes.get_mut(index) {
			if node.1.is_none() {
				node.1 = Some(self.free_node);
				self.free_node = index;
			}
		}
	}
	fn get(&self, index: usize) -> Option<Vec<u8>> {
		if let Some(node) = self.encoded_nodes.get(index) {
			if node.1.is_none() {
				return Some(node.0.clone())
			}
		}
		None
	}
	fn insert(&mut self, content: Vec<u8>) -> usize {
		let result = self.free_node;
		if self.free_node == self.encoded_nodes.len() {
			self.encoded_nodes.push((content, None));
			self.free_node = self.encoded_nodes.len();
		} else {
			let node = self.encoded_nodes.get_mut(self.free_node).expect("Free node oversized.");
			self.free_node = node.1.take().expect("free node contains pointer");
			node.0 = content;
		}
		result
	}
}

impl Backend for Rc<RefCell<TestBackend>> {
	type Index = usize;

	fn get_root(&self) -> Option<(Vec<u8>, usize)> {
		let s = self.borrow();
		s.get(s.root_index).map(|v| (v, s.root_index))
	}

	fn get_node(&self, index: Self::Index) -> Option<Vec<u8>> {
		self.borrow().get(index)
	}

	fn update_node(&self, index: Self::Index, node: Vec<u8>) -> Option<Self::Index> {
		let mut s = self.borrow_mut();
		if s.new_node_on_update {
			let result = s.insert(node);
			s.remove(index);
			Some(result)
		} else {
			s.encoded_nodes[index].0 = node;
			debug_assert!(s.encoded_nodes[index].1.is_none());
			None
		}
	}

	fn remove_node(&self, index: Self::Index) {
		self.borrow_mut().remove(index)
	}

	fn set_new_node(&self, node: Vec<u8>) -> Self::Index {
		self.borrow_mut().insert(node)
	}

	fn set_root(&self, root: Self::Index) {
		self.borrow_mut().root_index = root;
	}
}

/// Test only backend with lazy access.
#[derive(Clone, Debug)]
pub struct NodeTestBackend<N: TreeConf> {
	// None for new node only.
	index: Option<usize>,
	encoded: Vec<u8>,
	// bool indicate if fetched TODO move is fetched in node children struct (as associated type).
	child_index: Vec<(Option<usize>, bool)>,
	nb_children: usize,
	value: Option<N::Value>,
	value_state: ValueState,
	backend: Rc<RefCell<TestBackend>>,
	children_changed: bool,
	prefix_changed: bool,
}

// TODO replace backend by N::Backend when attached
fn decode<N>(
	encoded: Vec<u8>,
	backend: &Rc<RefCell<TestBackend>>,
	index: usize,
) -> (NodeTestBackend<N>, PrefixKey<Vec<u8>, AlignmentFor<N>>)
	where
		N: TreeConf,
		N::Value: Decode,
{

	let input = &mut encoded.as_slice();
	let value: Option<N::Value> = Decode::decode(input).unwrap();
	let mut child_index = Vec::new();
	let mut nb_children = 0;
	for _ in 0..<<N as TreeConf>::Radix as RadixConf>::CHILDREN_CAPACITY {
		let child: Option<u64> = Decode::decode(input).unwrap();
		if child.is_some() {
			nb_children += 1;
		}
		child_index.push((child.map(|v| v as usize), false));
	}

	let start_mask = if let Some(mask) = <N::Radix as RadixConf>::Alignment::DEFAULT {
		mask
	} else {
		let b = input.read_byte().unwrap();
		<N::Radix as RadixConf>::Alignment::decode_mask(b)
	};
	let start = PositionFor::<N> {
		index: 0,
		mask: start_mask,
	};
	let end_mask = if let Some(mask) = <N::Radix as RadixConf>::Alignment::DEFAULT {
		mask
	} else {
		let b = input.read_byte().unwrap();
		<N::Radix as RadixConf>::Alignment::decode_mask(b)
	};
	let prefix: Vec<u8> = Decode::decode(input).unwrap();
	let end = if end_mask == MaskFor::<N::Radix>::FIRST {
		PositionFor::<N>  {
			index: prefix.len(),
			mask: end_mask,
		}
	} else {
		PositionFor::<N>  {
			index: prefix.len() - 1,
			mask: end_mask,
		}
	};
	let prefix = PrefixKey::new_offset(prefix, start, end);

	(NodeTestBackend {
		index: Some(index),
		encoded,
		child_index,
		value,
		value_state: ValueState::Unfetched,
		nb_children,
		backend: backend.clone(),
		children_changed: false,
		prefix_changed: false,
	}, prefix)
}

fn encode_node<N>(node: &Node<N>) -> Vec<u8>
where
		N: TreeConf<Backend = NodeTestBackend<N>>,
		N::Value: Encode,
{
	let mut result = Vec::new();

	/*if node.backend.value_state == ValueState::Modified
		|| node.backend.value_state == ValueState::Deleted {
		node.value.encode_to(&mut result);
	} else {*/
	node.backend.value.encode_to(&mut result);
	//}

	for i in 0..<<N as TreeConf>::Radix as RadixConf>::CHILDREN_CAPACITY {
		let (ref_index, _fetched) = node.backend.child_index[i];
		/*let ref_index: Option<usize> = if fetched {
			if let Some(child) = node.get_child(KeyIndexFor::<N>::from_usize(i)) {
				child.backend.index
			} else {
				unreachable!("was fetched");
			}
		} else {
			ref_index
		};*/
		ref_index.map(|i| i as u64).encode_to(&mut result);
	}
	if let Some(_) = <N::Radix as RadixConf>::Alignment::DEFAULT {
	} else {
		result.push(<N::Radix as RadixConf>::Alignment::encode_mask(node.key.start));
	};
	node.key.data.encode_to(&mut result);
	if let Some(_) = <N::Radix as RadixConf>::Alignment::DEFAULT {
	} else {
		result.push(<N::Radix as RadixConf>::Alignment::encode_mask(node.key.end));
	};
	
	result
}


impl<N> TreeBackend<N> for NodeTestBackend<N>
	where
		N: TreeConf<Backend = Self>,
		N::Value: Decode + Encode,
{
	const ACTIVE: bool = true;
	const FUSE_ON_COMMIT: bool = true;
	type ChildState = crate::Child<Node<N>>;
	//type ChildState = Box<Node<N>>;

	type Backend = Rc<RefCell<TestBackend>>;
	type Index = usize;

	fn backend(&self) -> &Self::Backend {
		&self.backend
	}

	fn get_root(init: &Self::Backend) -> Option<NodeBox<N>> {
		if let Some((encoded, index)) = init.get_root() {
			let (backend, prefix) = decode::<N>(encoded, init, index);
			Some(Node::<N>::new_box_unfetched(
				prefix,
				backend,
			))
		} else {
			None
		}
	}
	fn get_node(&self, index: Self::Index) -> Option<NodeBox<N>> {
		if let Some(encoded) = self.backend.get_node(index) {
			let (backend, prefix) = decode::<N>(encoded, &self.backend, index);
			Some(Node::<N>::new_box_unfetched(
				prefix,
				backend,
			))
		} else {
			None
		}
	}

	fn get_next_child_index(&self, mut index: Option<KeyIndexFor<N>>) -> Option<KeyIndexFor<N>> {
		while let Some(i) = match index {
			Some(i) => i.next(),
			None => Some(KeyIndexFor::<N>::zero()),
		} {
			if let Some((Some(_), _)) = self.child_index.get(i.to_usize()) {
				return Some(i);
			}
			index = Some(i);
		}
		None
	}

	fn fetch_children_index(&self, at: KeyIndexFor<N>) -> Option<Self::Index> {
		if let Some((Some(ix), _)) = self.child_index.get(at.to_usize()) {
			Some(ix.clone())
		} else {
			None
		}
	}

	fn fetch_children(&mut self, at: KeyIndexFor<N>) -> Option<Option<NodeBox<N>>> {
		if let Some(child) = self.child_index.get_mut(at.to_usize()) {
			if !child.1 {
				child.1 = true;
				if let Some(index) = child.0.clone() {
					return Some(self.get_node(index));
				} else {
					return Some(None);
				}
			}
		}
		None
	}

	fn fetch_children_no_cache(&self, at: KeyIndexFor<N>) -> Option<NodeBox<N>> {
		if let Some(child) = self.child_index.get(at.to_usize()) {
			if let Some(index) = child.0.clone() {
				return self.get_node(index);
			}
		}
		None
	}

	fn fetch_nb_children(&mut self) -> Option<usize> {
		Some(self.nb_children)
	}

	fn fetch_value_index (&self) -> Option<Self::Index> {
		debug_assert!(self.value_state == ValueState::Unfetched);
		// dummy index just for testing purpose
		self.value.as_ref().map(|_| Default::default())
	}

	fn fetch_value(&mut self) -> Option<Option<N::Value>> {
		if self.value_state != ValueState::Unfetched {
			None
		} else {
			self.value_state = ValueState::Resolved;
			Some(self.value.clone())
		}
	}
	fn fetch_value_no_cache(&self) -> Option<N::Value> {
		self.value.clone()
	}
	fn set_change(&mut self) {
		self.children_changed = true;
	}
	fn set_prefix_change(&mut self) {
		self.prefix_changed = true;
	}

	fn delete(self) {
		if let Some(index) = self.index {
			self.backend.remove_node(index);
		}
	}

	fn new_node_backend(backend: &Self::Backend) -> Self {
		NodeTestBackend {
			index: None,
			encoded: Vec::new(),
			child_index: vec![(None, true); <<N as TreeConf>::Radix as RadixConf>::CHILDREN_CAPACITY],
			value: None,
			nb_children: 0,
			backend: backend.clone(),
			children_changed: false,
			prefix_changed: true, // new node need update
			value_state: ValueState::Resolved,
		}
	}

	fn commit_change(node: &mut NodeBox<N>, remove_node: &mut Vec<N::Backend>) -> Option<Self::Index> {
		let changed = node.backend.children_changed
			|| node.backend.prefix_changed
			|| node.backend.value_state == ValueState::Modified
			|| node.backend.value_state == ValueState::Deleted;
		if !changed {
			return None;
		}
		if node.backend.children_changed {
			// recurse commit of resolved children and update backend indexes.
			let mut index = None;
			let mut backend_ix = 0;
			while let Some(i) = node.get_next_child_index(index) {
				while backend_ix < i.to_usize() {
					node.backend.child_index[backend_ix] = (None, true);
					backend_ix += 1;
				}
				use crate::children::Children;
				use crate::WithChildState;
				if let Some(mut child) = node.children.get_child_mut(i).and_then(|c| c.node_mut()) {
					if let Some(ix) = Self::commit_change_fuse(&mut child, remove_node) {
						node.backend.child_index[backend_ix] = (Some(ix), true);
					} else {
						node.backend.child_index[backend_ix].1 = true;
					}
				}
				backend_ix = i.to_usize() + 1;
				index = Some(i);
			}
			while backend_ix < <<N as TreeConf>::Radix as RadixConf>::CHILDREN_CAPACITY {
				node.backend.child_index[backend_ix] = (None, true);
				backend_ix += 1;
			}
		}
		if node.backend.value_state == ValueState::Modified
			|| node.backend.value_state == ValueState::Deleted {
			node.backend.value = node.value.clone();
			node.backend.value_state = ValueState::Resolved;
		}

		node.backend.children_changed = false;
		node.backend.prefix_changed = false;

		let encoded = encode_node::<N>(node);
		if let Some(i) = node.backend.index {
			node.backend.backend.update_node(i, encoded)
		} else {
			Some(node.backend.backend.set_new_node(encoded))
		}
	}

	fn value_state(&self) -> ValueState {
		self.value_state
	}

	fn set_value_state(&mut self, state: ValueState) {
		self.value_state = state
	}

	fn clear_content(&mut self) {
		self.encoded.clear();
		self.child_index.clear();
		// Note here if value is stored in different node, we would need to remove it.
		self.value = None;
		self.nb_children = 0;
		self.children_changed = false;
		self.prefix_changed = true; // to ensure update
		self.value_state = ValueState::Resolved;
	}
}
