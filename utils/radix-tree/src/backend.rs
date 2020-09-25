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
	Position, MaskKeyByte, NodeIndex, Node, Children, NodeExt};
use alloc::vec::Vec;
use alloc::rc::Rc;
use core::marker::PhantomData;
use hashbrown::HashMap;
use codec::{Encode, Decode, Error as CodecError};
use core::cell::RefCell;
use core::fmt::Debug;
use derivative::Derivative;

type Key = Vec<u8>;

/// The backend to use for a tree.
pub trait BackendInner {
	fn write(&mut self, k: Vec<u8>, v: Vec<u8>);
	fn remove(&mut self, k: &[u8]);
	fn read(&self, k: &[u8]) -> Option<Vec<u8>>;
}

/// The backend to use for a tree.
pub trait Backend: Clone {
	fn write(&self, k: Vec<u8>, v: Vec<u8>);
	fn remove(&self, k: &[u8]);
	fn read(&self, k: &[u8]) -> Option<Vec<u8>>;
}

impl BackendInner for HashMap<Vec<u8>, Vec<u8>> {
	fn write(&mut self, k: Vec<u8>, v: Vec<u8>) {
		self.insert(k, v);
	}
	fn remove(&mut self, k: &[u8]) {
		self.remove(k);
	}
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.get(k).cloned()
	}
}

pub trait NodeBackend<N: NodeConf>: Clone {
	fn get_node(&self, k: &[u8]) -> Option<Node<N>>;
}

#[derive(Derivative)]
#[derivative(Clone(bound=""))]
struct SingleThreadBackend<B>(Rc<RefCell<B>>);

fn key_addressed<N: NodeConf>(
	key: &[u8],
	start_postion: PositionFor<N>,
) -> Vec<u8> {
	unimplemented!();
}

fn key_from_addressed<N: NodeConf>(
	key: &[u8],
) -> (&[u8], PositionFor<N>) {
	unimplemented!();
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

impl<B: BackendInner> Backend for SingleThreadBackend<B> {
	fn write(&self, k: Vec<u8>, v: Vec<u8>) {
		self.0.borrow_mut().write(k, v)
	}
	fn remove(&self, k: &[u8]) {
		self.0.borrow_mut().remove(k)
	}
	fn read(&self, k: &[u8]) -> Option<Vec<u8>> {
		self.0.borrow().read(k)
	}
}

impl<B, N> NodeBackend<N> for SingleThreadBackend<B>
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

impl<B: Backend> NodeExt for LazyExt<B> {
	fn new_node() -> Self {
		unimplemented!("need to resolve key and from backend");
		//LazyExt::Resolved(key, )
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
/*
impl<B> LazyExt<B>
	where
		B: NodeBackend<N>,
		N: Node<InitFrom = ()>,
{
	fn resolve(&mut self) {
		match self {
			LazyExt::Unresolved(..) => (),
			LazyExt::Resolved(..) => return,
			LazyExt::Deleted(..) => panic!("can't resolve a deleted node"),
		};

		*self = match *self {
			LazyExt::Unresolved(
				UnresolvedBackedNode { key, backend }
			) => {
				let inner = backend.get_node(key.as_slice())
					.expect("Backend corrupted, missing tree node");

				LazyExt::Resolved(BackedNode {
					inner,
					key,
					changed: false,
					backend,
				})
			},
			LazyExt::Resolved(..) => return,
			LazyExt::Deleted(..) => panic!("can't resolve a deleted node"),
		};
	}
	fn delete(self) {
		let (key, backend) = match self {
			LazyExt::Unresolved(
				UnresolvedBackedNode { key, backend }
			) => (key, backend),
			LazyExt::Resolved(
				BackedNode { key, backend, .. }
			) => (key, backend),
			LazyExt::Deleted(..) => return,
		};
		self = LazyExt::Deleted(DeletedBackedNode {key, backend});
	}
	fn delete_clone(self) -> Self {
		let result = self.clone();
		self.delete();
		result
	}
	fn key_addressed(
		key: &[u8],
		start_postion: PositionFor<N>,
	) -> Vec<u8> {
		unimplemented!();
	}
	fn inner(&self) -> &N {
		match self {
			LazyExt::Resolved(BackedNode { inner, .. }) => &inner,
			_ => unimplemented!("Backend must be use as mutable due to lazy nature"),
		}
	}
	fn inner_mut(&mut self) -> &mut N {
		match self {
			LazyExt::Unresolved(..) => self.resolve(),
			LazyExt::Resolved(..) => (),
			LazyExt::Deleted(..) => panic!("Trying to access a deleted node"),
		}
		match self {
			LazyExt::Resolved(BackedNode { inner, .. }) => &mut inner,
			_ => unreachable!(),
		}
	}
	fn set_changed(&mut self) {
		match self {
			LazyExt::Unresolved(..) => self.resolve(),
			LazyExt::Resolved(..) => (),
			LazyExt::Deleted(..) => panic!("Trying to access a deleted node"),
		}
		match self {
			LazyExt::Resolved(BackedNode { changed, .. }) => {
				*changed = true;
			},
			_ => unreachable!(),
		}
	}
}*/
