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
	Position, NodeBox, RadixConf, BackendFor,
	PrefixKeyConf, Node, Key};
use crate::radix::{MaskFor, MaskKeyByte};
use crate::children::{Children, NodeIndex};
use alloc::vec::Vec;
use alloc::rc::Rc;
use alloc::boxed::Box;
use hashbrown::HashMap;
use codec::{Codec, Encode, Decode, Error as CodecError, Input};
use core::cell::RefCell;
use derivative::Derivative;
#[cfg(feature = "std")]
pub use arc_backend::ArcBackend;

/// Node backend management.
pub trait TreeBackend<N: TreeConf>: Clone {
	/// Inner backend used.
	type Backend: Clone;
	/// Default value for inactive implementation.
	/// Active implementation needs input parameters and
	/// default to `None`.
	const DEFAULT: Option<Self> = None;
	/// Indicate if we display the whole tree on format.
	const DO_DEBUG: bool = true;

	/// Instantiate backend to store in an existing node.
	fn existing_node(init: &Self::Backend, key: Key) -> Self;

	/// Create a new root backend.
	fn new_root(init: &Self::Backend) -> Self;

	/// Create a new node from an existing node.
	/// Node reference ('self') is the parent node.
	/// Note that the reference to a node is only here
	/// to clone the backend (see 'backend_key').
	fn new_node(&self, key: Key) -> Self;

	/// Get a root node from the backend.
	fn get_root(init: &Self::Backend) -> Option<NodeBox<N>>;

	/// Get a child node from the backend.
	/// Node reference ('self') is the parent node.
	/// Note that the reference to a node is only here
	/// to clone the backend (see 'backend_key').
	fn fetch_node(&self, key: &[u8], position: PositionFor<N>) -> NodeBox<N>;

	/// Build a backend key
	fn backend_key(key: &[u8], position: PositionFor<N>) -> Key;

	/// Inverse of 'backend_key'.
	/// This is not strictly mandatory, but seems like a good
	/// way to inspect a backend and ensure the key scheme
	/// is conflict free.
	fn from_backend_key(key: &Key) -> (&[u8], PositionFor<N>);

	/// Resolve the data for a node before access.
	fn resolve(node: &Node<N>);

	/// Resolve the data for a node before access.
	fn resolve_mut(node: &mut Node<N>);

	/// Indicate a node was change.
	/// Does not flush change immediately.
	fn set_change(&mut self);
	
	/// Delete a node.
	/// Does flush change immediatly.
	fn delete(node: NodeBox<N>);

	/// Flush changes that happens to a node.
	fn commit_change(node: &mut Node<N>, recursive: bool);
}



impl<N: TreeConf<Backend = ()>> TreeBackend<N> for () {
	type Backend = ();
	const DEFAULT: Option<Self> = Some(());
	fn existing_node(_init: &Self::Backend, _key: Key) -> Self {
		()
	}
	fn new_root(_init: &Self::Backend) -> Self {
		()
	}
	fn new_node(&self, _key: Key) -> Self {
		()
	}
	fn get_root(_init: &Self::Backend) -> Option<NodeBox<N>> {
		unreachable!("Inactive implementation");
	}
	fn fetch_node(&self, _key: &[u8], _position: PositionFor<N>) -> NodeBox<N> {
		unreachable!("Inactive implementation");
	}
	fn backend_key(_key: &[u8], _position: PositionFor<N>) -> Key {
		unreachable!("Inactive implementation");
	}
	fn from_backend_key(_key: &Key) -> (&[u8], PositionFor<N>) {
		unreachable!("Inactive implementation");
	}
	fn resolve(_node: &Node<N>) { }
	fn resolve_mut(_node: &mut Node<N>) { }
	fn set_change(&mut self) { }
	fn delete(_node: NodeBox<N>) { }
	fn commit_change(_node: &mut Node<N>, _recursive: bool) { }
}

/// In memory hash map backend (mainly for testing).
pub type MapBackend = HashMap<Key, Vec<u8>>;

/// Read only backend to use with a tree.
pub trait ReadBackend {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>>;
}

impl<'a, B: ReadBackend> ReadBackend for &'a B {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		(*self).read(k)
	}
}

/// The backend to use for a tree.
pub trait BackendInner: ReadBackend {
	fn write(&mut self, k: Key, v: Vec<u8>);
	fn remove(&mut self, k: &[u8]);
}

/// The backend to use for a tree.
pub trait Backend: BackendInner + Clone { }

/*
/// The backend to use for a tree.
pub trait BackendSync: Backend + Send + Sync {
	fn write(&self, k: Key, v: Vec<u8>);
	fn remove(&self, k: &[u8]);
}
*/

impl ReadBackend for MapBackend {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.get(k).cloned()
	}
}

impl BackendInner for MapBackend {
	fn write(&mut self, k: Key, v: Vec<u8>) {
		self.insert(k, v);
	}
	fn remove(&mut self, k: &[u8]) {
		self.remove(k);
	}
}

/// Non Send and Sync backend.
#[derive(Derivative)]
#[derivative(Clone(bound=""))]
#[derivative(Default)]
pub struct RcBackend<B>(Rc<RefCell<B>>);

impl<B> RcBackend<B> {
	pub fn new(inner: B) -> Self {
		RcBackend(Rc::new(RefCell::new(inner)))
	}
}

fn key_addressed<N: TreeConf>(
	key: &[u8],
	start_postion: PositionFor<N>,
) -> Key {
	if <N::Radix as RadixConf>::Alignment::ALIGNED {
		key[..start_postion.index].into()
	} else {
		if start_postion.mask == MaskFor::<N::Radix>::FIRST {
			let mut result: Key = key[..start_postion.index - 1].into();
			result.push(255);
			result
		} else {
			let mut result: Key = key[..start_postion.index].into();
			if start_postion.index != 0 {
				result[start_postion.index - 1] = start_postion.mask.mask_end_incl(result[start_postion.index - 1]);
			};
			// first encode to 0 so we -1 to keep ordering
			result.push(<N::Radix as RadixConf>::Alignment::encode_mask(start_postion.mask) - 1);
			result
		}
	}
}

fn key_from_addressed<N: TreeConf>(
	key: &[u8],
) -> (&[u8], PositionFor<N>) {
	if <N::Radix as RadixConf>::Alignment::ALIGNED || key.len() == 0 {
		(key, PositionFor::<N>::zero())
	} else {
		let len = key.len();
		let encoded_mask = key[len - 1];
		if encoded_mask == 255 {
			(&key[..len - 1], Position {
				index: len,
				mask: MaskFor::<N::Radix>::FIRST,
			})
		} else {
			let mask = <N::Radix as RadixConf>::Alignment::decode_mask(encoded_mask + 1);
			(&key[..len - 1], Position {
				index: len - 2,
				mask,
			})
		}
	}
}

fn fetch_and_decode_node<N>(
	key: &[u8],
	start: PositionFor<N>,
	backend: &BackendFor<N>,
) -> core::result::Result<Node<N>, CodecError>
	where
		N: TreeConf,
		N::Value: Decode,
		BackendFor<N>: Backend,
{
	let node_key = N::Backend::backend_key(&key[..], start);
	let encoded = if let Some(encoded) = backend.read(node_key.as_slice()) {
		encoded
	} else {
		return Err("Missing node from backend".into());
	};
	let input = &mut encoded.as_slice();
	/*let start_mask = if let Some(mask) = <N::Radix as RadixConf>::Alignment::DEFAULT {
		mask
	} else {
		let b = input.read_byte()?;
		<N::Radix as RadixConf>::Alignment::decode_mask(b)
	};
	let start = PositionFor::<N> {
		index: 0,
		mask: start_mask,
	};*/
	let end_mask = if let Some(mask) = <N::Radix as RadixConf>::Alignment::DEFAULT {
		mask
	} else {
		let b = input.read_byte()?;
		<N::Radix as RadixConf>::Alignment::decode_mask(b)
	};
	let prefix: Vec<u8> = Decode::decode(input)?;
	let mut end = if end_mask == MaskFor::<N::Radix>::FIRST {
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

	let value: Option<N::Value> = Decode::decode(input)?;
	let mut node = Node::<N>::new(
		prefix.as_slice(),
		PositionFor::<N> {
			index: 0,
			mask: start.mask,
		},
		end,
		value,
		(),
		N::Backend::existing_node(&backend, node_key),
	);

	end.index += start.index;
	let mut key_index = KeyIndexFor::<N>::zero();
	let mut byte_index = 0;
	let mut input_index = 0;
	let mut child_key = key.into();
	node.new_end(&mut child_key, start);
	let child_position = end.next::<N::Radix>();
	loop {
		if let Some(children_mask) = input.get(input_index) {
			if children_mask & 0b1000_0000 >> byte_index != 0 {
				end.set_index::<N::Radix>(&mut child_key, key_index);
				let child = node.backend().fetch_node(&child_key[..], child_position);
				node.set_child(key_index, child);
			}

			if byte_index == 7 {
				byte_index = 0;
				input_index += 1;
			} else {
				byte_index += 1;
			}
			if let Some(i) = key_index.next() {
				key_index = i;
			} else {
				break;
			}
		} else {
			return Err("Incomplete node".into());
		}
	}

	Ok(node)
}

fn encode_node<N>(node: &Node<N>) -> Vec<u8>
	where
		N: TreeConf,
		N::Value: Encode,
{
	let mut result = Vec::new();
	/*if <N::Radix as RadixConf>::Alignment::DEFAULT.is_none() {
		let mask = <N::Radix as RadixConf>::Alignment::encode_mask(node.key.start);
		result.push(mask);
	}*/
	if <N::Radix as RadixConf>::Alignment::DEFAULT.is_none() {
		let mask = <N::Radix as RadixConf>::Alignment::encode_mask(node.key.end);
		result.push(mask);
	}
	use alloc::borrow::Borrow;
	node.key.data.borrow().encode_to(&mut result);
	node.value.encode_to(&mut result);

	let mut key_index = KeyIndexFor::<N>::zero();
	let mut byte_index = 0;
	let mut mask = 0u8;
	loop {
		if node.has_child(key_index) {
			mask |= 0b1000_0000 >> byte_index;
		}

		if let Some(i) = key_index.next() {
			key_index = i;
		} else {
			break;
		}
		if byte_index == 7 {
			result.push(mask);
			mask = 0;
			byte_index = 0;
		} else {
			byte_index += 1;
		}
	}
	result.push(mask);
	result
}

impl<B: BackendInner> ReadBackend for RcBackend<B> {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.0.borrow().read(k)
	}
}

impl<B: BackendInner> BackendInner for RcBackend<B> {
	fn write(&mut self, k: Key, v: Vec<u8>) {
		self.0.borrow_mut().write(k, v)
	}
	fn remove(&mut self, k: &[u8]) {
		self.0.borrow_mut().remove(k)
	}
}

impl<B: BackendInner> Backend for RcBackend<B> { }

#[derive(Clone)]
/// The backend to use for a tree.
pub struct TransactionBackend<B> {
	inner: B,
	changes: HashMap<Key, Option<Vec<u8>>>,
}

impl<B> TransactionBackend<B> {
	pub fn new(inner: B) -> Self {
		TransactionBackend {
			inner,
			changes: Default::default(),
		}
	}
	pub fn drain_changes(&mut self) -> HashMap<Key, Option<Vec<u8>>> {
		core::mem::replace(&mut self.changes, Default::default())
	}
}

impl<B: ReadBackend> ReadBackend for TransactionBackend<B> {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.changes.get(k).cloned()
			.flatten()
			.or_else(|| self.inner.read(k))
	}
}

impl<B: ReadBackend> BackendInner for TransactionBackend<B> {
	fn write(&mut self, k: Key, v: Vec<u8>) {
		self.changes.insert(k, Some(v));
	}
	fn remove(&mut self, k: &[u8]) {
		self.changes.insert(k.into(), None);
	}
}

#[derive(Derivative)]
#[derivative(Clone)]
/// Resolve child nodes from backend lazilly.
/// This way the whole tree do not need to be loaded on `fetch_node`,
/// but only when `resolve` or `resolve_mut` are called.
/// Please note that a tree using this cannot use `get` but
/// have to use `get_mut` for accessing its content
/// unless the node were already fetched.
pub enum LazyBackend<B> {
	Unresolved {
		/// Key for that node (including partial key).
		key: Key,
		/// Index of node start of partial key.
		/// (end position being the last byte of the key).
		start_index: usize,
		/// Mask for non aligned radix.
		start_mask: u8,
		/// Backend to fetch from.
		inner: B,
	},
	Resolved(DirectBackend<B>),
}

impl<B: Default> Default for LazyBackend<B> {
	fn default() -> Self {
		LazyBackend::Unresolved {
			key: Default::default(),
			start_index: 0,
			start_mask: 0,
			inner: Default::default(),
		}
	}
}

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Default)]
/// Backend associated to a node that has been
/// fetched.
/// When using a tree with this backend only,
/// `resolve` and `resolve_mut` are called
/// directly, so the whole tree get loaded
/// when querying the first node.
pub struct DirectBackend<B> {
	/// Backend to fetch from.
	inner: B,
	/// Key for that node (including partial key).
	key: Key,
	/// Has fetch node been modified.
	changed: bool,
}

impl<N, B: Backend> TreeBackend<N> for LazyBackend<B>
	where
		N: TreeConf<Backend = Self>,
		N::Value: Codec,
{
	/// Debug would trigger non mutable node resolution,
	/// which is not doable here.
	const DO_DEBUG: bool = false;
	type Backend = B;

	fn existing_node(init: &Self::Backend, key: Key) -> Self {
		LazyBackend::Resolved(DirectBackend {key, inner: init.clone(), changed: false})
	}

	fn new_root(init: &Self::Backend) -> Self {
		let key = <Self as TreeBackend<N>>::backend_key(&[], PositionFor::<N>::zero());
		LazyBackend::Resolved(DirectBackend {key, inner: init.clone(), changed: true})
	}

	fn new_node(&self, key: Key) -> Self {
		match self {
			LazyBackend::Unresolved {inner, ..}
				| LazyBackend::Resolved(DirectBackend {inner, ..}) => {
				LazyBackend::Resolved(DirectBackend {
					key,
					inner: inner.clone(),
					changed: true,
				})
			},
		}
	}

	fn get_root(init: &Self::Backend) -> Option<NodeBox<N>> {
		fetch_and_decode_node(&[], PositionFor::<N>::zero(), init).map(Box::new).ok()
	}

	fn fetch_node(&self, key: &[u8], position: PositionFor<N>) -> NodeBox<N> {
		match self {
			LazyBackend::Unresolved {inner, ..}
				| LazyBackend::Resolved(DirectBackend{inner, ..}) => {
				let mask = <N::Radix as RadixConf>::Alignment::encode_mask(position.mask); 
				Node::<N>::new_box(
					key,
					position,
					position,
					None,
					(),
					LazyBackend::Unresolved {
						key: key.to_vec(), 
						start_index: position.index,
						start_mask: mask,
						inner: inner.clone(),
					},
				)
			},
		}
	}

	fn backend_key(key: &[u8], position: PositionFor<N>) -> Key {
		key_addressed::<N>(key, position)
	}

	fn from_backend_key(key: &Key) -> (&[u8], PositionFor<N>) {
		key_from_addressed::<N>(key)
	}

	fn resolve(node: &Node<N>) {
		match node.backend() {
			LazyBackend::Resolved(..) => (),
			_ => unimplemented!("Lazy backend must only use mutable api."),
		}
	}

	fn resolve_mut(node: &mut Node<N>) {
		if let Some(new_node) = match node.backend_mut() {
			LazyBackend::Resolved(..) => None,
			LazyBackend::Unresolved{key, start_index, start_mask, inner} => {
				let mask = <N::Radix as RadixConf>::Alignment::decode_mask(*start_mask); 
				let position = PositionFor::<N> {
					index: *start_index,
					mask
				};
				fetch_and_decode_node(&key, position, inner).ok()
			},
		} {
			*node = new_node;
		}
	}

	fn set_change(&mut self) {
		match self {
			LazyBackend::Resolved(DirectBackend {changed, ..}) => {
				*changed = true;
			},
			LazyBackend::Unresolved {..} => panic!("Node need to be resolved first"),
		}
	}

	fn delete(mut node: NodeBox<N>) {
		match node.backend_mut() {
			LazyBackend::Resolved(DirectBackend {key, inner, ..}) => {
				inner.remove(key.as_slice());
			},
			LazyBackend::Unresolved { key, start_index, start_mask, inner } => {
				let mask = <N::Radix as RadixConf>::Alignment::decode_mask(*start_mask); 
				let start = PositionFor::<N> {
					index: *start_index,
					mask
				};
				let key = <Self as TreeBackend<N>>::backend_key(&key[..], start);
				inner.remove(key.as_slice());
			},
		}
	}

	fn commit_change(node: &mut Node<N>, recursive: bool) {
		match node.backend() {
			LazyBackend::Resolved(DirectBackend {changed: false, ..})
			| LazyBackend::Unresolved {..} => (),
			LazyBackend::Resolved(..) => {
				if recursive && node.children.number_child() > 0 {
					let mut key_index = KeyIndexFor::<N>::zero();
					loop {
						// Avoid node resolution by calling children directly.
						if let Some(child) = node.children.get_child_mut(key_index) {
							Self::commit_change(child, true);
						}
						key_index = if let Some(i) = key_index.next() {
							i
						} else {
							break;
						}
					}
				}
				let encoded = encode_node(node);
				match node.backend_mut() {
					LazyBackend::Resolved(DirectBackend {key, inner, changed}) => {
						*changed = false;
						inner.write(key.clone(), encoded)
					},
					_ => (),
				}
			},
		}
	}
}

impl<N, B: Backend> TreeBackend<N> for DirectBackend<B>
	where
		N: TreeConf<Backend = Self>,
		N::Value: Codec,
{
	type Backend = B;
	fn existing_node(init: &Self::Backend, key: Key) -> Self {
		DirectBackend {
			inner: init.clone(),
			key,
			changed: false,
		}
	}
	fn new_root(init: &Self::Backend) -> Self {
		let key = <Self as TreeBackend<N>>::backend_key(&[], PositionFor::<N>::zero());
		DirectBackend {
			inner: init.clone(),
			key,
			changed: true,
		}
	}
	fn new_node(&self, key: Key) -> Self {
		DirectBackend {
			inner: self.inner.clone(),
			key,
			changed: true,
		}
	}
	fn get_root(init: &Self::Backend) -> Option<NodeBox<N>> {
		fetch_and_decode_node(&[], PositionFor::<N>::zero(), init).map(Box::new).ok()
	}
	fn fetch_node(&self, key: &[u8], position: PositionFor<N>) -> NodeBox<N> {
		fetch_and_decode_node(&key, position, &self.inner)
			.map(Box::new)
			.expect("Corrupted backend, missing node")
	}

	fn backend_key(key: &[u8], position: PositionFor<N>) -> Key {
		key_addressed::<N>(key, position)
	}
	fn from_backend_key(key: &Key) -> (&[u8], PositionFor<N>) {
		key_from_addressed::<N>(key)
	}
	fn resolve(_node: &Node<N>) {
	}
	fn resolve_mut(_node: &mut Node<N>) {
	}
	fn set_change(&mut self) {
		self.changed = true;
	}
	fn delete(mut node: NodeBox<N>) {
		let backend = node.backend_mut();
		backend.inner.remove(backend.key.as_slice());
	}
	fn commit_change(node: &mut Node<N>, recursive: bool) {
		if node.backend().changed == true {
			if recursive && node.children.number_child() > 0 {
				let mut key_index = KeyIndexFor::<N>::zero();
				loop {
					// Avoid node resolution by calling children directly.
					if let Some(child) = node.children.get_child_mut(key_index) {
						Self::commit_change(child, true);
					}
					key_index = if let Some(i) = key_index.next() {
						i
					} else {
						break;
					}
				}
			}
			let encoded = encode_node(node);
			let backend = node.backend_mut();
			backend.changed = false;
			backend.inner.write(backend.key.clone(), encoded)
		}
	}
}

#[cfg(feature = "std")]
mod arc_backend {
	use super::*;
	use std::sync::Arc;
	use parking_lot::RwLock;

	/// 'Send' and 'Sync' backend.
	#[derive(Derivative)]
	#[derivative(Clone(bound=""))]
	#[derivative(Default)]
	pub struct ArcBackend<B>(pub Arc<RwLock<B>>);

	impl<B> ArcBackend<B> {
		pub fn new(inner: B) -> Self {
			ArcBackend(Arc::new(RwLock::new(inner)))
		}
	}

	impl<B: BackendInner> ReadBackend for ArcBackend<B> {
		fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
			self.0.read().read(k)
		}
	}

	impl<B: BackendInner> BackendInner for ArcBackend<B> {
		fn write(&mut self, k: Vec<u8>, v: Vec<u8>) {
			self.0.write().write(k, v)
		}
		fn remove(&mut self, k: &[u8]) {
			self.0.write().remove(k)
		}
	}

	impl<B: BackendInner> Backend for ArcBackend<B> { }
}
