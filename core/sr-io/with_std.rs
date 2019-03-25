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

#[doc(hidden)]
pub use parity_codec as codec;
// re-export hashing functions.
pub use primitives::{
	blake2_256, twox_128, twox_256, ed25519, Blake2Hasher, sr25519,
	Pair
};
pub use tiny_keccak::keccak256 as keccak_256;
// Switch to this after PoC-3
// pub use primitives::BlakeHasher;
pub use substrate_state_machine::{Externalities, BasicExternalities, TestExternalities};

use environmental::environmental;
use primitives::{hexdisplay::HexDisplay, H256, SubTrie};
use hash_db::Hasher;

#[cfg(feature = "std")]
use std::collections::HashMap;

environmental!(ext: trait Externalities<Blake2Hasher>);

/// A set of key value pairs for storage.
pub type StorageOverlay = HashMap<Vec<u8>, Vec<u8>>;

/// A set of key value pairs for children storage;
pub type ChildrenStorageOverlay = HashMap<Vec<u8>, StorageOverlay>;

/// Get `key` from storage and return a `Vec`, empty if there's a problem.
pub fn storage(key: &[u8]) -> Option<Vec<u8>> {
	ext::with(|ext| ext.storage(key).map(|s| s.to_vec()))
		.expect("storage cannot be called outside of an Externalities-provided environment.")
}

/// Get `key` from child storage and return a `Vec`, empty if there's a problem.
pub fn child_storage(subtrie: &SubTrie, key: &[u8]) -> Option<Vec<u8>> {
	ext::with(|ext| ext.child_storage(subtrie, key).map(|s| s.to_vec()))
		.expect("storage cannot be called outside of an Externalities-provided environment.")
}

/// Get `key` from storage, placing the value into `value_out` (as much of it as possible) and return
/// the number of bytes that the entry in storage had beyond the offset or None if the storage entry
/// doesn't exist at all. Note that if the buffer is smaller than the storage entry length, the returned
/// number of bytes is not equal to the number of bytes written to the `value_out`.
pub fn read_storage(key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
	ext::with(|ext| ext.storage(key).map(|value| {
		let value = &value[value_offset..];
		let written = ::std::cmp::min(value.len(), value_out.len());
		value_out[..written].copy_from_slice(&value[..written]);
		value.len()
	})).expect("read_storage cannot be called outside of an Externalities-provided environment.")
}

/// Get `key` from child storage, placing the value into `value_out` (as much of it as possible) and return
/// the number of bytes that the entry in storage had beyond the offset or None if the storage entry
/// doesn't exist at all. Note that if the buffer is smaller than the storage entry length, the returned
/// number of bytes is not equal to the number of bytes written to the `value_out`.
pub fn read_child_storage(subtrie: &SubTrie, key: &[u8], value_out: &mut [u8], value_offset: usize) -> Option<usize> {
	ext::with(|ext| ext.child_storage(subtrie, key).map(|value| {
		let value = &value[value_offset..];
		let written = ::std::cmp::min(value.len(), value_out.len());
		value_out[..written].copy_from_slice(&value[..written]);
		value.len()
	})).expect("read_storage cannot be called outside of an Externalities-provided environment.")
}

/// Set the storage of a key to some value.
pub fn set_storage(key: &[u8], value: &[u8]) {
	ext::with(|ext|
		ext.set_storage(key.to_vec(), value.to_vec())
	);
}

/// Set the child storage of a key to some value.
pub fn set_child_storage(subtrie: &SubTrie, key: &[u8], value: &[u8]) {
	ext::with(|ext|
		ext.set_child_storage(subtrie, key.to_vec(), value.to_vec())
	);
}

/// Clear the storage of a key.
pub fn clear_storage(key: &[u8]) {
	ext::with(|ext|
		ext.clear_storage(key)
	);
}

/// Clear the storage of a key.
pub fn clear_child_storage(subtrie: &SubTrie, key: &[u8]) {
	ext::with(|ext|
		ext.clear_child_storage(subtrie, key)
	);
}

/// Check whether a given `key` exists in storage.
pub fn exists_storage(key: &[u8]) -> bool {
	ext::with(|ext|
		ext.exists_storage(key)
	).unwrap_or(false)
}

/// Check whether a given `key` exists in storage.
pub fn exists_child_storage(subtrie: &SubTrie, key: &[u8]) -> bool {
	ext::with(|ext|
		ext.exists_child_storage(subtrie, key)
	).unwrap_or(false)
}

/// Clear the storage entries with a key that starts with the given prefix.
pub fn clear_prefix(prefix: &[u8]) {
	ext::with(|ext|
		ext.clear_prefix(prefix)
	);
}

/// Clear an entire child storage.
pub fn kill_child_storage(subtrie: &SubTrie) {
	ext::with(|ext|
		ext.kill_child_storage(subtrie)
	);
}

/// The current relay chain identifier.
pub fn chain_id() -> u64 {
	ext::with(|ext|
		ext.chain_id()
	).unwrap_or(0)
}

/// "Commit" all existing operations and compute the resultant storage root.
pub fn storage_root() -> H256 {
	ext::with(|ext|
		ext.storage_root()
	).unwrap_or(H256::zero())
}

/// "Commit" all existing operations and compute the resultant child storage root.
pub fn child_storage_root(subtrie: &SubTrie) -> Option<Vec<u8>> {
	ext::with(|ext|
		ext.child_storage_root(subtrie)
	).unwrap_or(None)
}

/// "Commit" all existing operations and get the resultant storage change root.
pub fn storage_changes_root(parent_hash: [u8; 32], parent_num: u64) -> Option<H256> {
	ext::with(|ext|
		ext.storage_changes_root(parent_hash.into(), parent_num)
	).unwrap_or(None)
}

/// A trie root formed from the enumerated items.
// TODO: remove (just use `ordered_trie_root`)
pub fn enumerated_trie_root<H>(input: &[&[u8]]) -> H::Out
where
	H: Hasher,
	H::Out: Ord,
{
	trie::ordered_trie_root::<H, _, _>(input.iter())
}

/// A trie root formed from the iterated items.
pub fn trie_root<H, I, A, B>(input: I) -> H::Out
where
	I: IntoIterator<Item = (A, B)>,
	A: AsRef<[u8]> + Ord,
	B: AsRef<[u8]>,
	H: Hasher,
	<H as Hasher>::Out: Ord,
{
	trie::trie_root::<H, _, _, _>(input)
}

/// A trie root formed from the enumerated items.
pub fn ordered_trie_root<H, I, A>(input: I) -> H::Out
where
	I: IntoIterator<Item = A> + Iterator<Item = A>,
	A: AsRef<[u8]>,
	H: Hasher,
	<H as Hasher>::Out: Ord,
{
	trie::ordered_trie_root::<H, _, _>(input)
}

/// Verify a ed25519 signature.
pub fn ed25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
	ed25519::Pair::verify_weak(sig, msg, pubkey)
}

/// Verify an sr25519 signature.
pub fn sr25519_verify<P: AsRef<[u8]>>(sig: &[u8; 64], msg: &[u8], pubkey: P) -> bool {
	sr25519::Pair::verify_weak(sig, msg, pubkey)
}

/// Verify and recover a SECP256k1 ECDSA signature.
/// - `sig` is passed in RSV format. V should be either 0/1 or 27/28.
/// - returns `Err` if the signature is bad, otherwise the 64-byte pubkey (doesn't include the 0x04 prefix).
pub fn secp256k1_ecdsa_recover(sig: &[u8; 65], msg: &[u8; 32]) -> Result<[u8; 64], EcdsaVerifyError> {
	let rs = secp256k1::Signature::parse_slice(&sig[0..64]).map_err(|_| EcdsaVerifyError::BadRS)?;
	let v = secp256k1::RecoveryId::parse(if sig[64] > 26 { sig[64] - 27 } else { sig[64] } as u8).map_err(|_| EcdsaVerifyError::BadV)?;
	let pubkey = secp256k1::recover(&secp256k1::Message::parse(msg), &rs, &v).map_err(|_| EcdsaVerifyError::BadSignature)?;
	let mut res = [0u8; 64];
	res.copy_from_slice(&pubkey.serialize()[1..65]);
	Ok(res)
}

/// Execute the given closure with global function available whose functionality routes into the
/// externalities `ext`. Forwards the value that the closure returns.
// NOTE: need a concrete hasher here due to limitations of the `environmental!` macro, otherwise a type param would have been fine I think.
pub fn with_externalities<R, F: FnOnce() -> R>(ext: &mut Externalities<Blake2Hasher>, f: F) -> R {
	ext::using(ext, f)
}

/// Execute the given closure with global functions available whose functionality routes into
/// externalities that draw from and populate `storage`. Forwards the value that the closure returns.
pub fn with_storage<R, F: FnOnce() -> R>(storage: &mut StorageOverlay, f: F) -> R {
	let mut alt_storage = Default::default();
	rstd::mem::swap(&mut alt_storage, storage);
	let mut ext: BasicExternalities = alt_storage.into();
	let r = ext::using(&mut ext, f);
	*storage = ext.into();
	r
}

/// Trait for things which can be printed.
pub trait Printable {
	fn print(self);
}

impl<'a> Printable for &'a [u8] {
	fn print(self) {
		println!("Runtime: {}", HexDisplay::from(&self));
	}
}

impl<'a> Printable for &'a str {
	fn print(self) {
		println!("Runtime: {}", self);
	}
}

impl Printable for u64 {
	fn print(self) {
		println!("Runtime: {}", self);
	}
}

/// Print a printable value.
pub fn print<T: Printable + Sized>(value: T) {
	value.print();
}

/// opaque subtrie pointer
pub struct SubTrieHandle(*mut u8);

impl SubTrieHandle {
	pub fn new(inner: *mut u8) -> Self { SubTrieHandle(inner) }
	pub fn ptr(&self) -> *mut u8 { self.0 }
}

impl Drop for SubTrieHandle {
	fn drop(&mut self) {
		drop_subtrie(self);
	}
}


/// Drop subtrie handler
pub fn drop_subtrie(subtrie: &mut SubTrieHandle) {
	// TODO switch to unreachable ?? (subtriehandle is for wasm side)
	unsafe {
		std::mem::drop(unsafe { Box::from_raw(subtrie) }); // calling drop just in case
	}
}

#[cfg(test)]
mod std_tests {
	use super::*;
	use primitives::map;

	#[test]
	fn storage_works() {
		let mut t = BasicExternalities::default();
		assert!(with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			set_storage(b"hello", b"world");
			assert_eq!(storage(b"hello"), Some(b"world".to_vec()));
			assert_eq!(storage(b"foo"), None);
			set_storage(b"foo", &[1, 2, 3][..]);
			true
		}));

		t = BasicExternalities::new(map![b"foo".to_vec() => b"bar".to_vec()]);

		assert!(!with_externalities(&mut t, || {
			assert_eq!(storage(b"hello"), None);
			assert_eq!(storage(b"foo"), Some(b"bar".to_vec()));
			false
		}));
	}

	#[test]
	fn read_storage_works() {
		let mut t = BasicExternalities::new(map![
			b":test".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		]);

		with_externalities(&mut t, || {
			let mut v = [0u8; 4];
			assert!(read_storage(b":test", &mut v[..], 0).unwrap() >= 4);
			assert_eq!(v, [11u8, 0, 0, 0]);
			let mut w = [0u8; 11];
			assert!(read_storage(b":test", &mut w[..], 4).unwrap() >= 11);
			assert_eq!(&w, b"Hello world");
		});
	}

	#[test]
	fn clear_prefix_works() {
		let mut t = BasicExternalities::new(map![
			b":a".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abcd".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abc".to_vec() => b"\x0b\0\0\0Hello world".to_vec(),
			b":abdd".to_vec() => b"\x0b\0\0\0Hello world".to_vec()
		]);

		with_externalities(&mut t, || {
			clear_prefix(b":abc");

			assert!(storage(b":a").is_some());
			assert!(storage(b":abdd").is_some());
			assert!(storage(b":abcd").is_none());
			assert!(storage(b":abc").is_none());
		});
	}
}
