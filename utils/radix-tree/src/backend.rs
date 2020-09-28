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
use codec::{Encode, Decode, Error as CodecError};
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

pub trait ReadNodeBackend<N: NodeConf>: Clone {
	fn get_node(&self, k: &[u8]) -> Option<Node<N>>;
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

fn decode_node<N, B: Backend>(
	key: &[u8],
	mut encoded: &[u8],
	backend: &B,
) -> core::result::Result<Node<N>, CodecError>
	where
		N: NodeConf<NodeExt = LazyExt<B>>,
		MaskFor<N::Radix>: Decode,
{
	let input = &mut encoded;
	let start_mask: MaskFor<N::Radix> = Decode::decode(input)?;
	let start = PositionFor::<N> {
		index: 0,
		mask: start_mask,
	};
	let end_mask: MaskFor<N::Radix> = Decode::decode(input)?;
	let prefix: Vec<u8> = Decode::decode(input)?;
	let end = if end_mask == MaskFor::<N::Radix>::first() {
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
	let node_key = key_addressed::<N>(&key[..], start);
	let mut node = Node::<N>::new(
		prefix.as_slice(),
		start,
		end,
		value,
		(),
		LazyExt::Resolved(node_key, backend.clone(), false),
	);

	let mut key_index = KeyIndexFor::<N>::zero();
	let mut byte_index = 0;
	let mut input_index = 0;
	let mut child_key = key.to_vec();
	let child_position = end.next::<N::Radix>();
	loop {
		if let Some(children_mask) = input.get(input_index) {
			if children_mask & 0b1000_0000 >> byte_index != 0 {
				child_position.set_index::<N::Radix>(&mut child_key, key_index);
				let key = key_addressed::<N>(&child_key[..], child_position);
				node.set_child(key_index, Node::<N>::new(
					&[],
					child_position,
					child_position,
					None,
					(),
					LazyExt::Unresolved(key, backend.clone()),
				));
			}

			if byte_index == 8 {
				byte_index = 0;
				input_index += 1;
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

impl<B, N> ReadNodeBackend<N> for SingleThreadBackend<B>
	where
		B: BackendInner,
		N: NodeConf<NodeExt = LazyExt<Self>>,
		MaskFor<N::Radix>: Decode,
{
	fn get_node(&self, k: &[u8]) -> Option<Node<N>> {
		self.0.borrow().read(k).and_then(|encoded| {
			decode_node(k, encoded.as_slice(), self).ok()
		})
	}
/*	fn get_node(&self, k: &[u8]) -> Option<N> {
		self.0.borrow().read(k).and_then(|encoded| {
			decode_node(k, encoded.as_slice(), (), &self).map(|(node, children)|
				Node {
					internal: LazyExt::Resolved(BackedNode {
						inner: node,
						key: k.to_vec(),
						changed: false,
						backend: self.clone(),
					}),
					children,
				}
			).ok()
		})
	}
*/
}

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

#[derive(Derivative)]
#[derivative(Clone)]
#[derivative(Default)]
pub struct DirectExt<B> {
	inner: B,
	key: Key,
	changed: bool,
}

impl<B: Backend> NodeExt for LazyExt<B> {
	fn new_node(&self, key: Key) -> Self {
		unimplemented!("need to resolve key and from backend");
		//LazyExt::Resolved(key, )
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
		unimplemented!("Encode and call backend write for key of ext");
	}
}

impl<B: Backend> NodeExt for DirectExt<B> {
	fn new_node(&self, key: Key) -> Self {
		DirectExt {
			inner: self.inner.clone(),
			key,
			changed: true,
		}
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
	fn delete<N: NodeConf<NodeExt = Self>>(node: Node<N>) {
		unimplemented!("Call backend delete for key of ext");
	}
	fn commit_change<N: NodeConf<NodeExt = Self>>(node: &mut Node<N>) {
		if node.ext().changed == true {
			node.ext_mut().changed = false;
			unimplemented!("Encode and call backend write for key of ext");
		}
	}
}
