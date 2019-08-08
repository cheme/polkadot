// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Child trie related struct

use codec::{Encode, Decode, Compact};
use rstd::prelude::*;
use rstd::ptr;
use crate::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX;
#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;
use hash_db::Prefix;

/// `KeySpace` type contains a unique child trie identifier.
/// It is used to isolate a child trie in its backing database.
/// This is done by prefixing its key with this value.
///
/// A keyspace byte representation must not be the start of another
/// keyspace byte representation (otherwhise conflict may happen).
/// This guaranty is provided by the fact that keyspace is a scale
/// encoded representation.
///
/// From a `TrieDB` perspective, accessing a child trie content 
/// will requires both the child trie root, but also the `KeySpace`.
///
/// The `KeySpace` of a child trie must be unique for the canonical chain.
/// This unicity is currently guaranted by build from a simple counter.
///
/// If a child trie was to be moved between two chains, the underlying
/// key value would be all the keyvaluedb prefixed by this keyspace.
/// Moving those key will still need for every content to change keyspace
/// of the origin chain with a new keyspace of a destination chain.
/// Please notice that usage of keyspace on ALL data makes it possible,
/// 
/// The same thing is true for a child trie deletion, there is no need to
/// remove all historic of state child trie keypair from a multiple TrieDB
/// perspective, but simply all keyvaluedb content with a key starting with
/// this keyspace.
pub type KeySpace = Vec<u8>;


/// Keyspace to use for the parent trie key.
pub const NO_CHILD_KEYSPACE: [u8;1] = [0];


/// Produce a new keyspace from current state counter.
pub fn produce_keyspace(child_counter: u128) -> Vec<u8> {
	codec::Encode::encode(&Compact(child_counter))
}

/// Decode keyspace to original counter value.
pub fn reverse_keyspace(keyspace: &[u8]) -> Result<u128, codec::Error> {
	<Compact<u128>>::decode(&mut &keyspace[..]).map(|c| c.0)
}

// see FIXME #2741 for removal of this allocation on every operation.
// Simplest would be to put an additional optional field in prefix.
/// Utility function used for merging `KeySpace` data and `prefix` data
/// before calling key value database primitives.
pub fn keyspace_as_prefix_alloc(ks: Option<&KeySpace>, prefix: Prefix) -> (Vec<u8>, Option<u8>) {
	let ks = ks.map(|ks| ks.as_slice()).unwrap_or(&NO_CHILD_KEYSPACE[..]);
	let mut result = rstd::vec![0; ks.len() + prefix.0.len()];
	result[..ks.len()].copy_from_slice(ks);
	result[ks.len()..].copy_from_slice(prefix.0);
	(result, prefix.1)
}

/// Parent trie origin. This type contains all information
/// needed to access a child trie from a root state.
/// Currently only a single depth is supported for child trie,
/// so it only contains the top trie key to the child trie.
/// Internally this contains a full path key (including
/// `well_known_keys::CHILD_STORAGE_KEY_PREFIX`).
pub type ParentTrie = Vec<u8>;

/// `ChildTrieReadRef` contains a reference to information
/// needed to access a child trie content.
/// Generally this should not be build directly but accessed
/// through a `node_ref` function call.
/// The struct can be build directly with invalid data, so
/// its usage is limited to read only querying.
#[derive(Clone)]
pub enum ChildTrieReadRef<'a> {
	/// Subtrie path for new trie, see [`ParentTrie`] for details.
	New(&'a KeySpace),
	/// Subtrie root hash and keyspace for existing child trie.
	Existing(&'a [u8], &'a KeySpace),
}

impl<'a> ChildTrieReadRef<'a> {
	/// Keyspace accessor for the enum.
	pub fn keyspace(&self) -> &KeySpace {
		match self {
			ChildTrieReadRef::New(k) => k,
			ChildTrieReadRef::Existing(_, k) => k,
		}
	}
}
/// Current codec version of a child trie definition.
const LAST_SUBTRIE_CODEC_VERSION: u16 = 1u16;

/// `ChildTrieNode` encoder internal implementation,
/// it shall not be public.
#[derive(Encode, Clone)]
struct ChildTrieReadEncode<'a> {
	/// Current codec version
	#[codec(compact)]
	version: u16,
	/// Child trie unique keyspace
	keyspace: &'a KeySpace,
	/// Child trie root hash
	root: &'a [u8],
}

#[derive(Decode)]
struct ChildTrieReadDecode {
	#[codec(compact)]
	version: u16,
	keyspace: KeySpace,
	root: Vec<u8>,
}

#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
/// This struct contains information needed to access a child trie.
/// Mainly use for doing remote queries (after accessing a child trie
/// content).
pub struct ChildTrieRead {
	/// Child trie parent key.
	pub keyspace: KeySpace,
	/// Child trie root hash.
	pub root: Vec<u8>,
}

impl ChildTrieRead {
	/// Use `ChildTrieRead` as a `ChildTrieReadRef`,
	/// forcing root field to an existing value.
	pub fn node_ref<'a>(&'a self) -> ChildTrieReadRef<'a> {
		debug_assert!(self.root.len() > 0);
		ChildTrieReadRef::Existing(&self.root[..], &self.keyspace)
	}
}

/// Information related to a child trie.
/// This contains information needed to access a child trie
/// content but also information needed to manage child trie
/// from its parent trie (removal, move, update of root).
///
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash, PartialOrd, Ord))]
pub struct ChildTrie {
	/// `KeySpace` for this child trie, see [`KeySpace`] for details.
	keyspace: KeySpace,
	/// Child trie current root, in case of modification
	/// this is not updated.
	root: Option<Vec<u8>>,
	/// Current position of this child trie, see [`ParentTrie`] for details.
	parent: ParentTrie,
	/// Extension contains additional encoded data related to this child trie
	/// node. A trait over the content could be use,
	/// but for simplicity the encoded value is use here.
	/// Direct operation on the child trie node are doable without
	/// having to know the type of the extension content.
	extension: Vec<u8>,
}

impl ChildTrie {
	/// Primitive to build a `ParentTrie` from its
	/// key.
	pub fn prefix_parent_key(parent: &[u8]) -> ParentTrie {
		let mut key_full = CHILD_STORAGE_KEY_PREFIX.to_vec();
		key_full.extend_from_slice(parent);
		key_full
	}

	/// Function to access the current key to a child trie.
	/// This does not include `well_known_keys::CHILD_STORAGE_KEY_PREFIX`.
	pub fn parent_key_slice(p: &ParentTrie) -> &[u8] {
		&p[CHILD_STORAGE_KEY_PREFIX.len()..]
	}

	/// Method for fetching or initiating a new child trie.
	///
	/// Note that call back could do nothing, which will allow unspecified behavior,
	/// but can be useful in case we create a child trie at a known unused location,
	/// or for performance purpose (later write).
	///
	/// We also provide an encodable value specific to the creation state (block number).
	pub fn fetch_or_new(
		parent_fetcher: impl FnOnce(&[u8]) -> Option<Self>,
		child_trie_update: impl FnOnce(ChildTrie),
		parent: &[u8],
		child_trie_next_counter: impl FnOnce() -> u128,
	) -> Self {
		parent_fetcher(parent)
			.unwrap_or_else(|| {
			let parent = Self::prefix_parent_key(parent);
			let ct = ChildTrie {
				keyspace: produce_keyspace(child_trie_next_counter()),
				root: Default::default(),
				parent,
				extension: Default::default(),
			};
			child_trie_update(ct.clone());
			ct
		})
	}

	/// Get a reference to the child trie information
	/// needed for a read only query.
	pub fn node_ref(&self) -> ChildTrieReadRef {
		if let Some(root) = self.root.as_ref() {
			ChildTrieReadRef::Existing(&root[..], &self.keyspace)
		} else {
			ChildTrieReadRef::New(&self.keyspace)
		}
	}

	/// Instantiate child trie from its encoded value and location.
	/// Please do not use this function with encoded content
	/// which is not fetch from an existing child trie.
	pub fn decode_node_with_parent(
		encoded_node: &[u8],
		parent: ParentTrie,
	) -> Option<Self> {
		let input = &mut &encoded_node[..];
		ChildTrieReadDecode::decode(input).ok().map(|ChildTrieReadDecode { version, keyspace, root }| {
			debug_assert!(version == LAST_SUBTRIE_CODEC_VERSION);
			ChildTrie {
				keyspace,
				root: Some(root),
				parent,
				extension: (*input).to_vec(),
		}})
	}

	/// Return true when the child trie is new and does not contain a root.
	pub fn is_new(&self) -> bool {
		self.root.is_none()
	}

	/// See [`parent_key_slice`].
	pub fn parent_slice(&self) -> &[u8] {
		Self::parent_key_slice(&self.parent)
	}

	/// Function to access the full key buffer pointing to
	/// a child trie. This contains technical information
	/// and should only be used for backend implementation.
	pub fn parent_trie(&self) -> &ParentTrie {
		&self.parent
	}

	/// Getter function to the original root value of this
	/// child trie.
	pub fn root_initial_value(&self) -> &Option<Vec<u8>> {
		&self.root
	}

	/// Getter function for the `KeySpace` of this child trie.
	pub fn keyspace(&self) -> &KeySpace {
		&self.keyspace
	}

	/// Getter function for extension content of child trie.
	pub fn extension(&self) -> &[u8] {
		&self.extension[..]
	}

	/// Is it possible to overwrite an existing chid trie with
	/// a new one.
	pub fn is_updatable_with(&self, old_ct: &ChildTrie) -> bool {
		old_ct.root_initial_value() == self.root_initial_value()
			&& old_ct.keyspace() == self.keyspace()
			&& old_ct.parent_slice() == self.parent_slice()
	}

	/// Encoder for the child trie, with a new root value.
	/// The child trie current root value is not updated (if
	/// content is commited the child trie will need to be fetch
	/// again for update).
	pub fn encoded_with_root(&self, new_root: &[u8]) -> Vec<u8> {
		let mut enc = codec::Encode::encode(&ChildTrieReadEncode{
			version: LAST_SUBTRIE_CODEC_VERSION,
			keyspace: &self.keyspace,
			root: new_root,
		});
		enc.extend_from_slice(&self.extension[..]);
		enc
	}

	/// Function accessing all child trie fields and returning
	/// tuple of pointer and size from them.
	pub fn ptr_child_trie(&self) -> PtrChildTrie {
		(
			self.keyspace.as_ptr(),
			self.keyspace.len() as u32,
			self.root.as_ref().map(|r| r.as_ptr()).unwrap_or(ptr::null()),
			self.root.as_ref().map(|r| r.len() as u32).unwrap_or(u32::max_value()),
			self.parent.as_ptr(),
			self.parent.len() as u32,
			self.extension.as_ptr(),
			self.extension.len() as u32,
		)
	}
	/// Function to access all child trie fields.
	pub fn to_ptr_vec(&self) -> (&[u8], Option<&[u8]>, &[u8], &[u8]) {
		(
			self.keyspace.as_ref(),
			self.root.as_ref().map(|r| r.as_ref()),
			self.parent.as_ref(),
			self.extension.as_ref(),
		)
	}

	/// Function to rebuild child trie accessed from.
	/// This is unsafe to use because it allows to build invalid
	/// child trie object: duplicate keyspace or invalid root.
	pub fn unsafe_from_ptr_child_trie(
		keyspace: *mut u8,
		keyspace_length: u32,
		root: *mut u8,
		root_length: u32,
		parent: *mut u8,
		parent_length: u32,
		extension: *mut u8,
		extension_length: u32,
	) -> Self {
		unsafe {
			let keyspace = from_raw_parts(keyspace, keyspace_length).expect("non optional; qed");
			let root = from_raw_parts(root, root_length);
			let parent = from_raw_parts(parent, parent_length).expect("non optional; qed");
			let extension = from_raw_parts(extension, extension_length).expect("non optional; qed");
			ChildTrie { keyspace, root, parent, extension }
		}
	}

	/// Function to rebuild child trie accessed from mem copied field.
	/// This is unsafe to use because it allows to build invalid
	/// child trie object: duplicate keyspace or invalid root.
	pub fn unsafe_from_ptr_vecs(
		keyspace: Vec<u8>,
		root: Option<Vec<u8>>,
		parent: Vec<u8>,
		extension: Vec<u8>,
	) -> Self {
		ChildTrie { keyspace, root, parent, extension }
	}

}

unsafe fn from_raw_parts(ptr: *mut u8, len: u32) -> Option<Vec<u8>> {
	if len == u32::max_value() {
		None
	} else {
		Some(<Vec<u8>>::from_raw_parts(ptr, len as usize, len as usize))
	}
}

/// Pointers repersentation of ChildTrie
type PtrChildTrie = (
	*const u8,
	u32,
	*const u8,
	u32,
	*const u8,
	u32,
	*const u8,
	u32,
);

impl AsRef<ChildTrie> for ChildTrie {
	fn as_ref(&self) -> &ChildTrie {
		self
	}
}

#[test]
fn encode_empty_prefix() {
	let empty = produce_keyspace(0);

	assert_eq!(&NO_CHILD_KEYSPACE[..], &empty[..]);
}

#[test]
fn keyspace_codec() {
	let sample: [u128; 3] = [0, 1, 1_000_000];
	for s in sample.iter() {
		let keyspace = produce_keyspace(*s);
		let dec_keyspace = reverse_keyspace(keyspace.as_slice()).unwrap();
		assert_eq!(*s, dec_keyspace);
	}
}

