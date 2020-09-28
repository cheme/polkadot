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

//! Use a backend for existing nodes.

use crate::{NodeConf, PositionFor, Descent, KeyIndexFor, MaskFor,
	Position, MaskKeyByte, NodeIndex, Node, Children, NodeExt, RadixConf,
	PrefixKeyConf};
use alloc::vec::Vec;
use alloc::rc::Rc;
use core::marker::PhantomData;
use hashbrown::HashMap;
use codec::{Encode, Decode, Error as CodecError, Input};
use core::cell::RefCell;
use core::fmt::Debug;
use derivative::Derivative;

pub type Key = Vec<u8>;
pub type MapBackend = HashMap<Vec<u8>, Vec<u8>>;

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
	fn write(&mut self, k: Vec<u8>, v: Vec<u8>);
	fn remove(&mut self, k: &[u8]);
}

/// The backend to use for a tree.
pub trait Backend: ReadBackend + Clone {
	fn write(&self, k: Vec<u8>, v: Vec<u8>);
	fn remove(&self, k: &[u8]);
}

impl ReadBackend for MapBackend {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.get(k).cloned()
	}
}

impl BackendInner for MapBackend {
	fn write(&mut self, k: Vec<u8>, v: Vec<u8>) {
		self.insert(k, v);
	}
	fn remove(&mut self, k: &[u8]) {
		self.remove(k);
	}
}

#[derive(Derivative)]
#[derivative(Clone(bound=""))]
#[derivative(Default)]
pub struct SingleThreadBackend<B>(Rc<RefCell<B>>);

fn key_addressed<N: NodeConf>(
	key: &[u8],
	start_postion: PositionFor<N>,
) -> Vec<u8> {
	if <N::Radix as RadixConf>::Alignment::ALIGNED {
		key[..start_postion.index].to_vec()
	} else {
		if start_postion.mask == MaskFor::<N::Radix>::first() {
			let mut result = key[..start_postion.index - 1].to_vec();
			result.push(255);
			result
		} else {
			let mut result = key[..start_postion.index].to_vec();
			if start_postion.index != 0 {
				result[start_postion.index - 1] = start_postion.mask.mask_end(result[start_postion.index - 1]);
			};
			// first encode to 0 so we -1 to keep ordering
			result.push(<N::Radix as RadixConf>::Alignment::encode_mask(start_postion.mask) - 1);
			result
		}
	}
}

fn key_from_addressed<N: NodeConf>(
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
				mask: MaskFor::<N::Radix>::first(),
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

fn decode_node<N>(
	key: &[u8],
	start: PositionFor<N>,
	backend: &<N::NodeExt as NodeExt>::INIT,
) -> core::result::Result<Node<N>, CodecError>
	where
		N: NodeConf,
		<N::NodeExt as NodeExt>::INIT: Backend,
{
	let node_key = key_addressed::<N>(&key[..], start);
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
	let mut end = if end_mask == MaskFor::<N::Radix>::first() {
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

	let value: Option<Vec<u8>> = Decode::decode(input)?;
	let mut node = Node::<N>::new(
		prefix.as_slice(),
		PositionFor::<N> {
			index: 0,
			mask: start.mask,
		},
		end,
		value,
		(),
		N::NodeExt::existing_node(&backend, node_key),
	);

	end.index += start.index;
	let mut key_index = KeyIndexFor::<N>::zero();
	let mut byte_index = 0;
	let mut input_index = 0;
	let mut child_key = key.to_vec();
	node.new_end(&mut child_key, start);
	let child_position = end.next::<N::Radix>();
	loop {
		if let Some(children_mask) = input.get(input_index) {
			if children_mask & 0b1000_0000 >> byte_index != 0 {
				end.set_index::<N::Radix>(&mut child_key, key_index);
				let child = node.ext().fetch_node(&child_key[..], child_position);
				let key = key_addressed::<N>(&child_key[..], child_position);
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

fn encode_node<N: NodeConf>(
	node: &Node<N>,
) -> Vec<u8> {
	let mut result = Vec::new();
	/*if <N::Radix as RadixConf>::Alignment::DEFAULT.is_none() {
		let mask = <N::Radix as RadixConf>::Alignment::encode_mask(node.key.start);
		result.push(mask);
	}*/
	if <N::Radix as RadixConf>::Alignment::DEFAULT.is_none() {
		let mask = <N::Radix as RadixConf>::Alignment::encode_mask(node.key.end);
		result.push(mask);
	}
	node.key.data.as_slice().encode_to(&mut result);
	node.value.encode_to(&mut result);

	let mut key_index = KeyIndexFor::<N>::zero();
	let mut byte_index = 0;
	let mut mask = 0u8;
	loop {
		if node.get_child(key_index).is_some() {
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

impl<B: BackendInner> ReadBackend for SingleThreadBackend<B> {
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.0.borrow().read(k)
	}
}

impl<B: BackendInner> Backend for SingleThreadBackend<B> {
	fn write(&self, k: Vec<u8>, v: Vec<u8>) {
		self.0.borrow_mut().write(k, v)
	}
	fn remove(&self, k: &[u8]) {
		self.0.borrow_mut().remove(k)
	}
}
/*
		self.0.borrow().read(k).and_then(|encoded| {
			decode_node(k, encoded.as_slice(), self).ok()
		})
*/
/// The backend to use for a tree.
pub struct SynchBackend<B, N> {
	nodes: B,
	_ph: PhantomData<N>,
}

/// The backend to use for a tree.
pub struct TransactionBackend<B, N> {
	inner: SynchBackend<B, N>,
	changes: HashMap<Vec<u8>, N>,
}

#[derive(Derivative)]
#[derivative(Clone)]
/// Resolved from backend on 
/// TODO rename
pub enum LazyExt<B> {
	Unresolved(Key, B),
	Resolved(Key, B, bool),
}
impl<B: Default> Default for LazyExt<B> {
	fn default() -> Self {
		LazyExt::Unresolved(Default::default(), Default::default())
	}
}
#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Default)]
pub struct DirectExt<B> {
	inner: B,
	key: Key,
	changed: bool,
}

impl<B: Backend> NodeExt for LazyExt<B> {
	type INIT = B;
	fn existing_node(init: &Self::INIT, key: Key) -> Self {
		LazyExt::Resolved(key, init.clone(), false)
	}
	fn new_node(&self, key: Key) -> Self {
		match self {
			LazyExt::Unresolved(_, backend)
				| LazyExt::Resolved(_, backend, ..) => {
				LazyExt::Resolved(key, backend.clone(), true)
			},
		}
	}
	fn get_root<N: NodeConf<NodeExt = Self>>(&self) -> Option<Node<N>> {
		match self {
			LazyExt::Unresolved(_, backend)
				| LazyExt::Resolved(_, backend, ..) => {
				decode_node(&[], PositionFor::<N>::zero(), backend).ok()
			},
		}
	}
	fn fetch_node<N: NodeConf<NodeExt = Self>>(&self, key: &[u8], position: PositionFor<N>) -> Node<N> {
		match self {
			LazyExt::Unresolved(_, backend)
				| LazyExt::Resolved(_, backend, ..) => {
				let key = key_addressed::<N>(key, position);
				Node::<N>::new(
					&[],
					position,
					position,
					None,
					(),
					LazyExt::Unresolved(key, backend.clone()),
				)
			},
		}
	}
	fn backend_key<N: NodeConf<NodeExt = Self>>(key: &[u8], position: PositionFor<N>) -> Key {
		key_addressed::<N>(key, position)
	}
	fn from_backend_key<N: NodeConf<NodeExt = Self>>(key: &Key) -> (&[u8], PositionFor<N>) {
		key_from_addressed::<N>(key)
	}
	fn resolve<N: NodeConf<NodeExt = Self>>(node: &Node<N>) {
		match node.ext() {
			LazyExt::Resolved(..) => (),
			_ => unimplemented!("Backend must be use as mutable due to lazy nature"),
		}
	}
	fn resolve_mut<N: NodeConf<NodeExt = Self>>(node: &mut Node<N>) {
		match node.ext_mut() {
			LazyExt::Resolved(..) => (),
			LazyExt::Unresolved(key, backend) => {
				unimplemented!("TODO fetch form backend and fresh unchanged resolved");
			},
		}
	}
	fn set_change(&mut self) {
		match self {
			LazyExt::Resolved(_, _, changed) => {
				*changed = true;
			},
			LazyExt::Unresolved(..) => panic!("Node need to be resolved first"),
		}
	}
	fn delete<N: NodeConf<NodeExt = Self>>(node: Node<N>) {
		unimplemented!("Call backend delete for key of ext");
	}
	fn commit_change<N: NodeConf<NodeExt = Self>>(node: &mut Node<N>) {
		match node.ext_mut() {
			LazyExt::Resolved(_, _, false)
			| LazyExt::Unresolved(..) => (),
			LazyExt::Resolved(_key, _backend, changed) => {
				*changed = false;
				unimplemented!("Encode and call backend write for key of ext");
			},
		}
	}
}

impl<B: Backend> NodeExt for DirectExt<B> {
	type INIT = B;
	fn existing_node(init: &Self::INIT, key: Key) -> Self {
		DirectExt {
			inner: init.clone(),
			key,
			changed: false,
		}
	}
	fn new_node(&self, key: Key) -> Self {
		DirectExt {
			inner: self.inner.clone(),
			key,
			changed: true,
		}
	}
	fn get_root<N: NodeConf<NodeExt = Self>>(&self) -> Option<Node<N>> {
		decode_node(&[], PositionFor::<N>::zero(), &self.inner).ok()
	}
	fn fetch_node<N: NodeConf<NodeExt = Self>>(&self, key: &[u8], position: PositionFor<N>) -> Node<N> {
		decode_node(&key, position, &self.inner)
			.expect("Corrupted backend, missing node")
	}

	fn backend_key<N: NodeConf<NodeExt = Self>>(key: &[u8], position: PositionFor<N>) -> Key {
		key_addressed::<N>(key, position)
	}
	fn from_backend_key<N: NodeConf<NodeExt = Self>>(key: &Key) -> (&[u8], PositionFor<N>) {
		key_from_addressed::<N>(key)
	}
	fn resolve<N: NodeConf<NodeExt = Self>>(_node: &Node<N>) {
	}
	fn resolve_mut<N: NodeConf<NodeExt = Self>>(_node: &mut Node<N>) {
	}
	fn set_change(&mut self) {
		self.changed = true;
	}
	fn delete<N: NodeConf<NodeExt = Self>>(mut node: Node<N>) {
		let ext = node.ext_mut();
		ext.inner.remove(ext.key.as_slice());
	}
	fn commit_change<N: NodeConf<NodeExt = Self>>(node: &mut Node<N>) {
		if node.ext().changed == true {
			let encoded = encode_node(node);
			let ext = node.ext_mut();
			ext.changed = false;
			ext.inner.write(ext.key.clone(), encoded)
		}
	}
}
