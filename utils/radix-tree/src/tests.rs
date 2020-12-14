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

//! Tests an fuzzing base code.

#[cfg(any(test, feature = "fuzzer"))]
use crate::{Node256NoBackend, Node256NoBackendART, Node256HashBackend,
	Node256TxBackend, Node256LazyHashBackend};

macro_rules! test_for {
	($module_name: ident, $backend_conf: ident, $check_backend_ser: expr) => {


#[cfg(any(test, feature = "fuzzer"))]
pub mod $module_name {
	use crate::*;
	use alloc::collections::btree_map::BTreeMap;
	#[cfg(test)]
	use alloc::vec;

	#[cfg(test)]
	const CHECK_BACKEND: bool = $check_backend_ser;
	type TreeConf = super::$backend_conf<Vec<u8>>;

	fn new_backend() -> BackendFor<TreeConf> {
		BackendFor::<TreeConf>::default()
	}

	#[test]
	fn empty_are_equals() {
		let backend = new_backend();
		let t1 = Tree::<TreeConf>::new(backend.clone());
		let t2 = Tree::<TreeConf>::new(backend.clone());
		assert!(compare_tree(&t1, &t2));
	}

	#[test]
	fn inserts_are_equals() {
		let backend = new_backend();
		let mut t1 = Tree::<TreeConf>::new(backend.clone());
		let mut t2 = Tree::<TreeConf>::new(backend.clone());
		let value1 = b"value1".to_vec();
		assert_eq!(None, t1.insert(b"key1", value1.clone()));
		assert_eq!(None, t2.insert(b"key1", value1.clone()));
		assert!(compare_tree(&t1, &t2));
		assert_eq!(Some(value1.clone()), t1.insert(b"key1", b"value2".to_vec()));
		assert_eq!(Some(value1.clone()), t2.insert(b"key1", b"value2".to_vec()));
		assert!(compare_tree(&t1, &t2));
		assert_eq!(None, t1.insert(b"key2", value1.clone()));
		assert_eq!(None, t2.insert(b"key2", value1.clone()));
		assert!(compare_tree(&t1, &t2));
		assert_eq!(None, t2.insert(b"key3", value1.clone()));
		assert!(!compare_tree(&t1, &t2));
	}

	#[cfg(test)]
	fn compare_tree(left: &Tree::<TreeConf>, right: &Tree::<TreeConf>) -> bool {
		let left_node = left.iter();
		let left = left_node.value_iter();
		let right_node = right.iter();
		let mut right = right_node.value_iter();
		for l in left {
			if let Some(r) = right.next() {
				if &l.0[..] != &r.0[..] {
					return false;
				}
				if &l.1[..] != &r.1[..] {
					return false;
				}
			} else {
				return false;
			}
		}
		if right.next().is_some() {
			return false;
		}
		true
	}

	fn compare_iter<K: Borrow<[u8]>>(left: &Tree::<TreeConf>, right: &BTreeMap<K, Vec<u8>>) -> bool {
		let left_node = left.iter();
		let left = left_node.value_iter();
		let mut right = right.iter();
		for l in left {
			if let Some(r) = right.next() {
				if &l.0[..] != &r.0.borrow()[..] {
					return false;
				}
				if &l.1[..] != &r.1[..] {
					return false;
				}
			} else {
				return false;
			}
		}
		if right.next().is_some() {
			return false;
		}
		true
	}

	#[test]
	fn compare_btree() {
		let backend = new_backend();
		let mut t1 = Tree::<TreeConf>::new(backend.clone());
		let mut t2 = BTreeMap::<&'static [u8], Vec<u8>>::new();
		let value1 = b"value1".to_vec();
		assert_eq!(None, t1.insert(b"key1", value1.clone()));
		assert_eq!(None, t2.insert(b"key1", value1.clone()));
		assert!(compare_iter(&t1, &t2));
		assert_eq!(Some(value1.clone()), t1.insert(b"key1", b"value2".to_vec()));
		assert_eq!(Some(value1.clone()), t2.insert(b"key1", b"value2".to_vec()));
		assert!(compare_iter(&t1, &t2));
		assert_eq!(None, t1.insert(b"key2", value1.clone()));
		assert_eq!(None, t2.insert(b"key2", value1.clone()));
		assert!(compare_iter(&t1, &t2));
		assert_eq!(None, t1.insert(b"key3", value1.clone()));
		assert!(!compare_iter(&t1, &t2));
		core::mem::drop(t1);
		if CHECK_BACKEND {
			assert_eq!(None, t2.insert(b"key3", value1.clone()));
			let mut t3 = Tree::<TreeConf>::from_backend(backend.clone());
			assert!(compare_iter(&mut t3, &mut t2));
		}
	}

	fn fuzz_to_data(input: &[u8]) -> Vec<(Vec<u8>,Vec<u8>)> {
		let mut result = Vec::new();
		// enc = (minkeylen, maxkeylen (min max up to 32), datas)
		// fix data len 2 bytes
		let mut minkeylen = if let Some(v) = input.get(0) {
			let mut v = *v & 31u8;
			v = v + 1;
			v
		} else { return result; };
		let mut maxkeylen = if let Some(v) = input.get(1) {
			let mut v = *v & 31u8;
			v = v + 1;
			v
		} else { return result; };

		if maxkeylen < minkeylen {
			let v = minkeylen;
			minkeylen = maxkeylen;
			maxkeylen = v;
		}
		let mut ix = 2;
		loop {
			let keylen = if let Some(v) = input.get(ix) {
				let mut v = *v & 31u8;
				v = v + 1;
				v = core::cmp::max(minkeylen, v);
				v = core::cmp::min(maxkeylen, v);
				v as usize
			} else { break };
			let key = if input.len() > ix + keylen {
				input[ix..ix+keylen].to_vec()
			} else { break };
			ix += keylen;
			let val = if input.len() > ix + 2 {
				input[ix..ix+2].to_vec()
			} else { break };
			result.push((key,val));
		}
		result
	}

	fn fuzz_removal(data: Vec<(Vec<u8>,Vec<u8>)>) -> Vec<(bool, Vec<u8>,Vec<u8>)> {
		let mut res = Vec::new();
		let mut existing = None;
		for (a, d) in data.into_iter().enumerate() {
			if existing == None {
				existing = Some(a%2);
			}
			if existing.unwrap() == 0 {
				if a % 9 == 6
				|| a % 9 == 7
				|| a % 9 == 8 {
					// a random removal some time
					res.push((true, d.0, d.1));
					continue;
				}
			}
			res.push((false, d.0, d.1));
		}
		res
	}

	pub fn fuzz_insert_remove(input: &[u8], check_backend: bool) {
		let data = fuzz_to_data(input);
		let data = fuzz_removal(data);
		let backend = new_backend();
		let mut a = 0;
		let mut t1 = Tree::<TreeConf>::new(backend.clone());
		let mut t2 = BTreeMap::<Vec<u8>, Vec<u8>>::new();
		while a < data.len() {
			if data[a].0 {
				// remove
				t1.remove(&data[a].1[..]);
				t2.remove(&data[a].1[..]);
			} else {
				// add
				t1.insert(&data[a].1[..], data[a].2.clone());
				t2.insert(data[a].1.clone(), data[a].2.clone());
			}
			a += 1;
		}
		assert!(compare_iter(&mut t1, &mut t2));
		core::mem::drop(t1);
		if check_backend {
			let mut t3 = Tree::<TreeConf>::from_backend(backend.clone());
			assert!(compare_iter(&mut t3, &mut t2));
		}
	}

	#[test]
	fn replay_insert_remove_fuzzing() {
		let datas = [
			vec![0x0,0x0,0x6a,0x6a,0x41,0xa,0xff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x6a,0x6a,0x41,0xa,0xff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,],
			vec![0x0,0x40,0x3f,0x81,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x7e,0x60,0x0,0xa0,0xef,0x8,0xd1,0x72,0x1,0x75,0xd,0xfa,0xea,0x10,0x7,0x4a,0xff,0xf7,0xff,0xff,0x8d,0xd9,0xe2,0xd9,0xff,0xff,0x8d,0xd9,0xd9,0x1,0x2,0xf5,0xfc,0x21,0x0,0x0,0x46,0xff,0xf8,0x0,0xfe,0xc5,0xfe,0xff,0xa5,0x32,0x48,0x41,0x7d,0x1,0x2d,0x40,0x0,0x48,0x41,0x7d,0x1,0xa8,0xa8,0xa8,0xa8,0xa9,0xa8,0xa4,0xfe,0xd6,0xff,0xc5,0xa5,0x0,0x1,0x74,0x72,0xff,0xff,0x9e,0x0,0x0,0x42,0x42,0x42,0x42,0x42,0x42,0x42,0x42,0x0,0xf8,0x10,0x93,0x0,0x0,0x3d,0x4,0xfb,0x0,0x2b,0x4,0x0,0x7,0xff,0x1,0x3a,0xff,0x1,0x2,0xf5,0xfc,0x21,0x0,0x0,0xbf,0x0,0x7,0xff,0x1,0x3a,0x1,0x0,0x36,0xa5,0x32,0x48,0x41,0x7d,0x1,0x2d,0x0,0x0,0xb8,0xbe,0x82,0xfe,0xd2,0xbf,0xff,0x0,0x63,0x22,0x9c,0x3f,0x31,0x35,0x84,0x0,0x3,0xff,0x1,0x2,0xf5,0x0,0x0,0x0,],
			vec![0x0,0x0,0x3b,0x60,0x32,0xff,0xff,0xff,0x60,0x0,0x3b,0x60,0x32,0xae,],
			vec![100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 121, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 0, 0, 0, 0, 0, 251, 0, 0, 0, 4],
			vec![0, 1, 0, 45, 0, 0, 0, 0, 0, 0, 0, 0, 75, 0],
			vec![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 96, 0, 16, 96],
			vec![0, 0, 0, 0, 0, 0, 0, 195, 0, 0, 195, 0, 0, 0],
			vec![0, 0, 5, 75, 9, 1, 48, 58, 17, 9, 17, 9, 0],
			vec![0, 0, 8, 0, 0, 0, 0, 0],
			vec![0, 0, 70, 0, 3, 61, 0, 0],
			vec![0u8, 202, 1, 4, 64, 49, 0, 0],
		];
		for data in datas.iter() {
			fuzz_insert_remove(&data[..], CHECK_BACKEND);
		}
	}
}


}
}

test_for!(test_256, Node256NoBackend, false);
test_for!(test_256_art, Node256NoBackendART, false);
test_for!(test_256_hash, Node256HashBackend, true);
test_for!(test_256_hash_tx, Node256TxBackend, true);
test_for!(test_256_lazy_hash, Node256LazyHashBackend, false);

#[cfg(test)]
mod lazy_test {
	use crate::*;
	use alloc::collections::btree_map::BTreeMap;

	type Value = Vec<u8>;
	type TreeConf = super::Node256LazyHashBackend<Value>;

	fn new_backend() -> BackendFor<Node256LazyHashBackend<Value>> {
		BackendFor::<Node256LazyHashBackend<Value>>::default()
	}

	fn compare_iter_mut<K: Borrow<[u8]>>(left: &mut Tree::<TreeConf>, right: &BTreeMap<K, Vec<u8>>) -> bool {
		let left_node = left.iter_mut();
		let left = left_node.value_iter_mut();
		let mut right = right.iter();
		for l in left {
			if let Some(r) = right.next() {
				if &l.0[..] != &r.0.borrow()[..] {
					return false;
				}
				if &l.1[..] != &r.1[..] {
					return false;
				}
			} else {
				return false;
			}
		}
		if right.next().is_some() {
			return false;
		}
		true
	}

	#[test]
	fn compare_btree() {
		fn test(drop: bool) {
			let backend = new_backend();
			let mut t1 = Tree::<TreeConf>::new(backend.clone());
			let mut t2 = BTreeMap::<&'static [u8], Vec<u8>>::new();
			let mut value1 = b"value1".to_vec();
			assert_eq!(None, t1.insert(b"key1", value1.clone()));
			assert_eq!(None, t2.insert(b"key1", value1.clone()));
			assert_eq!(Some(value1.clone()), t1.insert(b"key1", b"value2".to_vec()));
			assert_eq!(Some(value1.clone()), t2.insert(b"key1", b"value2".to_vec()));
			assert_eq!(None, t1.insert(b"key2", value1.clone()));
			assert_eq!(None, t2.insert(b"key2", value1.clone()));
			assert_eq!(None, t1.insert(b"key3", value1.clone()));
			assert_eq!(None, t2.insert(b"key3", value1.clone()));
			// Shouldn't call get on a lazy tree, but here we got all in memory.
			assert_eq!(t1.get(&b"key3"[..]), Some(&value1));
			assert_eq!(t1.get_mut(&b"key3"[..]), Some(&mut value1));
			if drop {
				core::mem::drop(t1);
			} else {
				t1.commit();
			}
			let mut t3 = Tree::<TreeConf>::from_backend(backend.clone());
			assert_eq!(t3.get_mut(&b"key3"[..]), Some(&mut value1));
			assert!(compare_iter_mut(&mut t3, &mut t2));
		}
		test(true);
		test(false);
	}
}
