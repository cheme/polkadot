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

//! Stuff to do with the runtime's storage.

use crate::rstd::prelude::*;
use crate::rstd::borrow::Borrow;
use substrate_primitives::Hasher;
use codec::{Codec, Encode, Decode, KeyedVec, EncodeAppend};
use hashed::generator::{HashedStorage, StorageHasher};
use unhashed::generator::UnhashedStorage;
use crate::rstd::marker::PhantomData;

#[macro_use]
pub mod storage_items;
pub mod unhashed;
pub mod hashed;

/// The underlying runtime storage.
pub struct RuntimeStorage<H>(pub PhantomData<H>);

impl<H> Default for RuntimeStorage<H> {
	fn default() -> Self {
		RuntimeStorage(PhantomData)
	}
}

impl<R, H> HashedStorage<H> for RuntimeStorage<R> 
	where 
		R: Hasher,
		R::Out: Ord,
		H: StorageHasher
{
	fn exists(&self, key: &[u8]) -> bool {
		hashed::exists::<R, _, _>(&H::hash, key)
	}

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: Decode>(&self, key: &[u8]) -> Option<T> {
		hashed::get::<R, _, _, _>(&H::hash, key)
	}

	/// Put a value in under a key.
	fn put<T: Encode>(&mut self, key: &[u8], val: &T) {
		hashed::put::<R, _, _, _>(&H::hash, key, val)
	}

	/// Remove the bytes of a key from storage.
	fn kill(&mut self, key: &[u8]) {
		hashed::kill::<R, _, _>(&H::hash, key)
	}

	/// Take a value from storage, deleting it after reading.
	fn take<T: Decode>(&mut self, key: &[u8]) -> Option<T> {
		hashed::take::<R, _, _, _>(&H::hash, key)
	}

	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>> {
		hashed::get_raw::<R, _, _>(&H::hash, key)
	}

	fn put_raw(&mut self, key: &[u8], value: &[u8]) {
		hashed::put_raw::<R, _, _>(&H::hash, key, value)
	}
}

impl<R> UnhashedStorage for RuntimeStorage<R>
	where 
		R: Hasher,
		R::Out: Ord,
{
	fn exists(&self, key: &[u8]) -> bool {
		unhashed::exists::<R>(key)
	}

	/// Load the bytes of a key from storage. Can panic if the type is incorrect.
	fn get<T: Decode>(&self, key: &[u8]) -> Option<T> {
		unhashed::get::<R, _>(key)
	}

	/// Put a value in under a key.
	fn put<T: Encode + ?Sized>(&mut self, key: &[u8], val: &T) {
		unhashed::put::<R, T>(key, val)
	}

	/// Remove the bytes of a key from storage.
	fn kill(&mut self, key: &[u8]) {
		unhashed::kill::<R>(key)
	}

	/// Remove the bytes of a key from storage.
	fn kill_prefix(&mut self, prefix: &[u8]) {
		unhashed::kill_prefix::<R>(prefix)
	}

	/// Take a value from storage, deleting it after reading.
	fn take<T: Decode>(&mut self, key: &[u8]) -> Option<T> {
		unhashed::take::<R, T>(key)
	}

	fn get_raw(&self, key: &[u8]) -> Option<Vec<u8>> {
		unhashed::get_raw::<R>(key)
	}

	fn put_raw(&mut self, key: &[u8], value: &[u8]) {
		unhashed::put_raw::<R>(key, value)
	}
}

/// A trait for working with macro-generated storage values under the substrate storage API.
pub trait StorageValue<H, T>
	where 
		H: Hasher,
		H::Out: Ord,
		T: Codec,
{
	/// The type that get/take return.
	type Query;

	/// Get the storage key.
	fn key() -> &'static [u8];

	/// Does the value (explicitly) exist in storage?
	fn exists() -> bool;

	/// Load the value from the provided storage instance.
	fn get() -> Self::Query;

	/// Store a value under this key into the provided storage instance.
	fn put<Arg: Borrow<T>>(val: Arg);

	/// Store a value under this key into the provided storage instance; this can take any reference
	/// type that derefs to `T` (and has `Encode` implemented).
	fn put_ref<Arg: ?Sized + Encode>(val: &Arg) where T: AsRef<Arg>;

	/// Mutate the value
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R;

	/// Clear the storage value.
	fn kill();

	/// Take a value from storage, removing it afterwards.
	fn take() -> Self::Query;

	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>;
}

impl<H, T, U> StorageValue<H, T> for U
	where
		T: Codec,
		H: Hasher,
		H::Out: Ord,
		U: hashed::generator::StorageValue<T>,
{
	type Query = U::Query;

	fn key() -> &'static [u8] {
		<U as hashed::generator::StorageValue<T>>::key()
	}
	fn exists() -> bool {
		U::exists(&RuntimeStorage::<H>::default())
	}
	fn get() -> Self::Query {
		U::get(&RuntimeStorage::<H>::default())
	}
	fn put<Arg: Borrow<T>>(val: Arg) {
		U::put(val.borrow(), &mut RuntimeStorage::<H>::default())
	}
	fn put_ref<Arg: ?Sized + Encode>(val: &Arg) where T: AsRef<Arg> {
		U::put_ref(val, &mut RuntimeStorage::<H>::default())
	}
	fn mutate<R, F: FnOnce(&mut Self::Query) -> R>(f: F) -> R {
		U::mutate(f, &mut RuntimeStorage::<H>::default())
	}
	fn kill() {
		U::kill(&mut RuntimeStorage::<H>::default())
	}
	fn take() -> Self::Query {
		U::take(&mut RuntimeStorage::<H>::default())
	}
	fn append<I: Encode>(items: &[I]) -> Result<(), &'static str>
		where T: EncodeAppend<Item=I>
	{
		U::append(items, &mut RuntimeStorage::<H>::default())
	}
}

/// A strongly-typed map in storage.
pub trait StorageMap<H, K: Codec, V: Codec> {
	/// The type that get/take return.
	type Query;

	/// Get the prefix key in storage.
	fn prefix() -> &'static [u8];

	/// Get the storage key used to fetch a value corresponding to a specific key.
	fn key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8>;

	/// Does the value (explicitly) exist in storage?
	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool;

	/// Load the value associated with the given key from the map.
	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;

	/// Store a value to be associated with the given key from the map.
	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg);

	/// Store a value under this key into the provided storage instance; this can take any reference
	/// type that derefs to `T` (and has `Encode` implemented).
	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg) where V: AsRef<ValArg>;

	/// Remove the value under a key.
	fn remove<KeyArg: Borrow<K>>(key: KeyArg);

	/// Mutate the value under a key.
	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R;

	/// Take the value under a key.
	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query;
}

impl<H, K, V, U> StorageMap<H, K, V> for U
	where
		K: Codec,
		V: Codec,
		H: Hasher,
		H::Out: Ord,
		U: hashed::generator::StorageMap<K, V>,
{

	type Query = U::Query;

	fn prefix() -> &'static [u8] {
		<U as hashed::generator::StorageMap<K, V>>::prefix()
	}

	fn key_for<KeyArg: Borrow<K>>(key: KeyArg) -> Vec<u8> {
		<U as hashed::generator::StorageMap<K, V>>::key_for(key.borrow())
	}

	fn exists<KeyArg: Borrow<K>>(key: KeyArg) -> bool {
		U::exists(key.borrow(), &RuntimeStorage::<H>::default())
	}

	fn get<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		U::get(key.borrow(), &RuntimeStorage::<H>::default())
	}

	fn insert<KeyArg: Borrow<K>, ValArg: Borrow<V>>(key: KeyArg, val: ValArg) {
		U::insert(key.borrow(), val.borrow(), &mut RuntimeStorage::<H>::default())
	}

	fn insert_ref<KeyArg: Borrow<K>, ValArg: ?Sized + Encode>(key: KeyArg, val: &ValArg) where V: AsRef<ValArg> {
		U::insert_ref(key.borrow(), val, &mut RuntimeStorage::<H>::default())
	}

	fn remove<KeyArg: Borrow<K>>(key: KeyArg) {
		U::remove(key.borrow(), &mut RuntimeStorage::<H>::default())
	}

	fn mutate<KeyArg: Borrow<K>, R, F: FnOnce(&mut Self::Query) -> R>(key: KeyArg, f: F) -> R {
		U::mutate(key.borrow(), f, &mut RuntimeStorage::<H>::default())
	}

	fn take<KeyArg: Borrow<K>>(key: KeyArg) -> Self::Query {
		U::take(key.borrow(), &mut RuntimeStorage::<H>::default())
	}
}

/// A storage map with values that can be appended to.
pub trait AppendableStorageMap<H, K: Codec, V: Codec>: StorageMap<H, K, V> {
	/// Append the given item to the value in the storage.
	///
	/// `T` is required to implement `codec::EncodeAppend`.
	fn append<KeyArg: Borrow<K>, I: Encode>(key: KeyArg, items: &[I]) -> Result<(), &'static str>
		where V: EncodeAppend<Item=I>;
}

impl<H, K, V, U> AppendableStorageMap<H, K, V> for U
	where
		K: Codec,
		V: Codec,
		H: Hasher,
		H::Out: Ord,
		U: hashed::generator::AppendableStorageMap<K, V>,
{
	fn append<KeyArg: Borrow<K>, I: Encode>(key: KeyArg, items: &[I]) -> Result<(), &'static str>
		where V: EncodeAppend<Item=I>
	{
		U::append(key.borrow(), items, &mut RuntimeStorage::<H>::default())
	}
}

/// A storage map that can be enumerated.
///
/// Primarily useful for off-chain computations.
/// Runtime implementors should avoid enumerating storage entries on-chain.
pub trait EnumerableStorageMap<H, K: Codec, V: Codec>: StorageMap<H, K, V> {
	/// Return current head element.
	fn head() -> Option<K>;

	/// Enumerate all elements in the map.
	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static, H: 'static;
}

impl<H, K, V, U> EnumerableStorageMap<H, K, V> for U
	where
		K: Codec,
		V: Codec,
		H: Hasher,
		H::Out: Ord,
		U: hashed::generator::EnumerableStorageMap<K, V>,
{

	fn head() -> Option<K> {
		<U as hashed::generator::EnumerableStorageMap<K, V>>::head(&RuntimeStorage::<H>::default())
	}

	fn enumerate() -> Box<dyn Iterator<Item = (K, V)>> where K: 'static, V: 'static, H: 'static {
		<U as hashed::generator::EnumerableStorageMap<K, V>>::enumerate(RuntimeStorage::<H>::default())
	}
}

/// An implementation of a map with a two keys.
///
/// It provides an important ability to efficiently remove all entries
/// that have a common first key.
///
/// # Mapping of keys to a storage path
///
/// The storage key (i.e. the key under which the `Value` will be stored) is created from two parts.
/// The first part is a hash of a concatenation of the `PREFIX` and `Key1`. And the second part
/// is a hash of a `Key2`.
///
/// /!\ be careful while choosing the Hash, indeed malicious could craft second keys to lower the trie.
pub trait StorageDoubleMap<H, K1: Encode, K2: Encode, V: Codec> {

	/// The type that get/take returns.
	type Query;

	fn prefix() -> &'static [u8];

	fn key_for<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Vec<u8>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn prefix_for<KArg1>(k1: &KArg1) -> Vec<u8> where KArg1: ?Sized + Encode, K1: Borrow<KArg1>;

	fn exists<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> bool
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn get<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn take<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn insert<KArg1, KArg2, VArg>(k1: &KArg1, k2: &KArg2, val: &VArg)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		V: Borrow<VArg>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		VArg: ?Sized + Encode;

	fn remove<KArg1, KArg2>(k1: &KArg1, k2: &KArg2)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode;

	fn remove_prefix<KArg1>(k1: &KArg1) where KArg1: ?Sized + Encode, K1: Borrow<KArg1>;

	fn mutate<KArg1, KArg2, R, F>(k1: &KArg1, k2: &KArg2, f: F) -> R
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		F: FnOnce(&mut Self::Query) -> R;

	fn append<KArg1, KArg2, I>(
		k1: &KArg1,
		k2: &KArg2,
		items: &[I],
	) -> Result<(), &'static str>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		I: codec::Encode,
		V: EncodeAppend<Item=I>;
}

impl<H, K1, K2, V, U> StorageDoubleMap<H, K1, K2, V> for U
	where
		K1: Encode,
		K2: Encode,
		V: Codec,
		H: Hasher,
		H::Out: Ord,
		U: unhashed::generator::StorageDoubleMap<K1, K2, V>,
{
	type Query = U::Query;

	fn prefix() -> &'static [u8] {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::prefix()
	}

	fn key_for<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Vec<u8>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::key_for(k1, k2)
	}

	fn prefix_for<KArg1>(k1: &KArg1) -> Vec<u8> where KArg1: ?Sized + Encode, K1: Borrow<KArg1> {
		<U as unhashed::generator::StorageDoubleMap<K1, K2, V>>::prefix_for(k1)
	}

	fn exists<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> bool
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::exists(k1, k2, &RuntimeStorage::<H>::default())
	}

	fn get<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::get(k1, k2, &RuntimeStorage::<H>::default())
	}

	fn take<KArg1, KArg2>(k1: &KArg1, k2: &KArg2) -> Self::Query
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::take(k1.borrow(), k2.borrow(), &mut RuntimeStorage::<H>::default())
	}

	fn insert<KArg1, KArg2, VArg>(k1: &KArg1, k2: &KArg2, val: &VArg)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		V: Borrow<VArg>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		VArg: ?Sized + Encode,
	{
		U::insert(k1, k2, val, &mut RuntimeStorage::<H>::default())
	}

	fn remove<KArg1, KArg2>(k1: &KArg1, k2: &KArg2)
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
	{
		U::remove(k1, k2, &mut RuntimeStorage::<H>::default())
	}

	fn remove_prefix<KArg1>(k1: &KArg1) where KArg1: ?Sized + Encode, K1: Borrow<KArg1> {
		U::remove_prefix(k1, &mut RuntimeStorage::<H>::default())
	}

	fn mutate<KArg1, KArg2, R, F>(k1: &KArg1, k2: &KArg2, f: F) -> R
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		F: FnOnce(&mut Self::Query) -> R
	{
		U::mutate(k1, k2, f, &mut RuntimeStorage::<H>::default())
	}

	fn append<KArg1, KArg2, I>(
		k1: &KArg1,
		k2: &KArg2,
		items: &[I],
	) -> Result<(), &'static str>
	where
		K1: Borrow<KArg1>,
		K2: Borrow<KArg2>,
		KArg1: ?Sized + Encode,
		KArg2: ?Sized + Encode,
		I: codec::Encode,
		V: EncodeAppend<Item=I>,
	{
		U::append(k1, k2, items, &mut RuntimeStorage::<H>::default())
	}
}

/// child storage NOTE could replace unhashed by having only one kind of storage (root being null storage
/// key (storage_key can become Option<&[u8]>).
/// This module is a currently only a variant of unhashed with additional `storage_key`.
/// Note that `storage_key` must be unique and strong (strong in the sense of being long enough to
/// avoid collision from a resistant hash function (which unique implies)).
pub mod child {
	use super::{Codec, Decode, Vec, Hasher};

	/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
	pub fn get<H, T>(storage_key: &[u8], key: &[u8]) -> Option<T>
		where
			T: Codec + Sized,
			H: Hasher,
			H::Out: Ord,
	{
		runtime_io::child_storage::<H>(storage_key, key).map(|v| {
			Decode::decode(&mut &v[..]).expect("storage is not null, therefore must be a valid type")
		})
	}

	/// Return the value of the item in storage under `key`, or the type's default if there is no
	/// explicit entry.
	pub fn get_or_default<H, T>(storage_key: &[u8], key: &[u8]) -> T
		where
			T: Codec + Sized + Default,
			H: Hasher,
			H::Out: Ord,
	{
 		get::<H, T>(storage_key, key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry.
	pub fn get_or<H, T>(storage_key: &[u8], key: &[u8], default_value: T) -> T
		where
			T: Codec + Sized,
			H: Hasher,
			H::Out: Ord,
	{
		get::<H, T>(storage_key, key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry.
	pub fn get_or_else<H, T, F>(storage_key: &[u8], key: &[u8], default_value: F) -> T
		where
			T: Codec + Sized,
			H: Hasher,
			H::Out: Ord,
			F: FnOnce() -> T,
	{
		get::<H, T>(storage_key, key).unwrap_or_else(default_value)
	}

	/// Put `value` in storage under `key`.
	pub fn put<H, T>(storage_key: &[u8], key: &[u8], value: &T)
		where
			T: Codec,
			H: Hasher,
			H::Out: Ord,
	{
		value.using_encoded(|slice| runtime_io::set_child_storage::<H>(storage_key, key, slice));
	}

	/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
	pub fn take<H, T>(storage_key: &[u8], key: &[u8]) -> Option<T>
		where
			T: Codec + Sized,
			H: Hasher,
			H::Out: Ord,
	{
		let r = get::<H, T>(storage_key, key);
		if r.is_some() {
			kill::<H>(storage_key, key);
		}
		r
	}

	/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
	/// the default for its type.
	pub fn take_or_default<H, T>(storage_key: &[u8], key: &[u8]) -> T
		where
			T: Codec + Sized + Default,
			H: Hasher,
			H::Out: Ord,
	{
		take::<H, T>(storage_key, key).unwrap_or_else(Default::default)
	}

	/// Return the value of the item in storage under `key`, or `default_value` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or<H, T>(storage_key: &[u8],key: &[u8], default_value: T) -> T
		where
			T: Codec + Sized,
			H: Hasher,
			H::Out: Ord,
	{
		take::<H, T>(storage_key, key).unwrap_or(default_value)
	}

	/// Return the value of the item in storage under `key`, or `default_value()` if there is no
	/// explicit entry. Ensure there is no explicit entry on return.
	pub fn take_or_else<H, T, F>(storage_key: &[u8], key: &[u8], default_value: F) -> T
		where
			T: Codec + Sized,
			H: Hasher,
			H::Out: Ord,
			F: FnOnce() -> T,
	{
		take::<H, T>(storage_key, key).unwrap_or_else(default_value)
	}

	/// Check to see if `key` has an explicit entry in storage.
	pub fn exists<H>(storage_key: &[u8], key: &[u8]) -> bool
		where
			H: Hasher,
			H::Out: Ord,
	{
		runtime_io::read_child_storage::<H>(storage_key, key, &mut [0;0][..], 0).is_some()
	}

	/// Remove all `storage_key` key/values
	pub fn kill_storage<H>(storage_key: &[u8])
		where
			H: Hasher,
			H::Out: Ord,
	{
		runtime_io::kill_child_storage::<H>(storage_key)
	}

	/// Ensure `key` has no explicit entry in storage.
	pub fn kill<H>(storage_key: &[u8], key: &[u8])
		where
			H: Hasher,
			H::Out: Ord,
	{
		runtime_io::clear_child_storage::<H>(storage_key, key);
	}

	/// Get a Vec of bytes from storage.
	pub fn get_raw<H>(storage_key: &[u8], key: &[u8]) -> Option<Vec<u8>>
			where
			H: Hasher,
			H::Out: Ord,
	{
		runtime_io::child_storage::<H>(storage_key, key)
	}

	/// Put a raw byte slice into storage.
	pub fn put_raw<H>(storage_key: &[u8], key: &[u8], value: &[u8])
			where
			H: Hasher,
			H::Out: Ord,
	{
		runtime_io::set_child_storage::<H>(storage_key, key, value)
	}

	pub use super::unhashed::StorageVec;
}
