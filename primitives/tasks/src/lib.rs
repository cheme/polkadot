// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Runtime tasks.
//!
//! Contains runtime-usable functions for spawning parallel purely computational tasks.
//!
//! NOTE: This is experimental API.
//! NOTE: When using in actual runtime, make sure you don't produce unbounded parallelism.
//! So this is bad example to use it:
//! ```rust
//!    use sp_tasks::AsyncStateType;
//!    fn my_parallel_computator(data: Vec<u8>) -> Vec<u8> {
//!        unimplemented!()
//!    }
//!    fn test(dynamic_variable: i32) {
//!       for _ in 0..dynamic_variable {
//!					sp_tasks::spawn(my_parallel_computator, vec![], AsyncStateType::Stateless);
//!				}
//!    }
//! ```
//!
//! While this is a good example:
//! ```rust
//!    use codec::Encode;
//!    use sp_tasks::AsyncStateType;
//!    static STATIC_VARIABLE: i32 = 4;
//!
//!    fn my_parallel_computator(data: Vec<u8>) -> Vec<u8> {
//!        unimplemented!()
//!    }
//!
//!    fn test(computation_payload: Vec<u8>) {
//!        let parallel_tasks = (0..STATIC_VARIABLE).map(|idx| sp_tasks::spawn(
//!            my_parallel_computator,
//!            computation_payload.chunks(10).nth(idx as _).encode(),
//!            AsyncStateType::Stateless,
//!        ));
//!    }
//! ```
//!
//! When allowing unbounded parallelism, malicious transactions can exploit it and partition
//! network consensus based on how much resources nodes have.
//!

#![cfg_attr(not(feature = "std"), no_std)]

mod async_externalities;
pub mod inline_spawn;

#[cfg(feature = "std")]
pub use async_externalities::new_async_externalities;
pub use async_externalities::{new_inline_only_externalities, AsyncExternalities, AsyncExt};

use sp_std::vec::Vec;

/// Type for `AsyncState`.
/// TODO rename to stick with doc for all ASyncExt builders.
#[derive(Debug)]
#[repr(u8)]
pub enum AsyncStateType {
	Stateless = 0,
	ReadLastBlock = 1,
	ReadAtSpawn = 2,
}

impl Default for AsyncStateType {
	fn default() -> Self {
		AsyncStateType::Stateless
	}
}

impl AsyncStateType {
	/// Similar purpose as `TryFrom<u8>`.
	pub fn from_u8(kind: u8) -> Option<AsyncStateType> {
		Some(match kind {
			0 => AsyncStateType::Stateless,
			1 => AsyncStateType::ReadLastBlock,
			2 => AsyncStateType::ReadAtSpawn,
			_ => return None,
		})
	}

	/// Depending on concurrency management strategy
	/// we may need to resolve the result against
	/// parent externalities.
	pub fn need_resolve(&self) -> bool {
		match *self {
			AsyncStateType::Stateless => false,
			AsyncStateType::ReadLastBlock => false,
			AsyncStateType::ReadAtSpawn => false,
		}
	}
}

/// Task handle.
///
/// This can be `join`-ed to get (blocking) the result of
/// the spawned task execution.
///
/// TODO this need to switch to an enum with a possible inline
/// variant for RuntimeSpawn implemnetation that do not support threads.
#[must_use]
pub struct DataJoinHandle {
	handle: u64,
}

impl DataJoinHandle {
	/// Join handle returned by `spawn` function
	pub fn join(self) -> Option<Vec<u8>> {
		sp_io::runtime_tasks::join(self.handle)
	}

	/// TODO doc
	pub fn dismiss(self) {
		sp_io::runtime_tasks::dismiss(self.handle)
	}
}

/// TODO doc
pub fn set_capacity(capacity: u32) {
	sp_io::runtime_tasks::set_capacity(capacity)
}

#[cfg(feature = "std")]
mod inner {
	use std::panic::AssertUnwindSafe;
	use std::sync::{mpsc, Arc, atomic::{AtomicU64, Ordering}};
	use std::collections::HashMap;
	use sp_externalities::{Externalities, ExternalitiesExt as _};
	use sp_core::traits::RuntimeSpawnExt;
	use crate::{AsyncExt, AsyncStateType};
	use super::DataJoinHandle;

	/// Spawn new runtime task (native).
	/// TODO factor this code with the runtime spawn one
	pub fn spawn(
		entry_point: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		kind: AsyncStateType,
	) -> DataJoinHandle {
		let handle = sp_externalities::with_externalities(|mut ext|{
			let ext_unsafe = ext as *mut dyn Externalities;
			let runtime_spawn = ext.extension::<RuntimeSpawnExt>()
				.expect("Cannot spawn without dynamic runtime dispatcher (RuntimeSpawnExt)");
			// Unsafe usage here means that `spawn_call` shall never attempt to access
			// or deregister this `RuntimeSpawnExt` from the unchecked ext2.
			let ext_unsafe: &mut _  = unsafe { &mut *ext_unsafe };
			// TODO could wrap ext_unsafe in a ext struct that filter calls to extension of
			// a given id, to make this safer.
			let result = runtime_spawn.spawn_call_native(entry_point, data, kind as u8, ext_unsafe);
			std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::AcqRel);
			// Not necessary (same lifetime as runtime_spawn), but shows intent to keep
			// ext alive as long as ext_unsafe is in scope.
			drop(ext);
			result
		}).expect("`RuntimeTasks::spawn`: called outside of externalities context");

		DataJoinHandle { handle }
	}
}

#[cfg(not(feature = "std"))]
mod inner {
	use core::mem;
	use sp_std::prelude::*;
	use crate::AsyncStateType;
	use super::DataJoinHandle;

	/// Dispatch wrapper for wasm blob.
	///
	/// Serves as trampoline to call any rust function with (Vec<u8>) -> Vec<u8> compiled
	/// into the runtime.
	///
	/// Function item should be provided with `func_ref`. Argument for the call
	/// will be generated from bytes at `payload_ptr` with `payload_len`.
	///
	/// NOTE: Since this dynamic dispatch function and the invoked function are compiled with
	/// the same compiler, there should be no problem with ABI incompatibility.
	extern "C" fn dispatch_wrapper(func_ref: *const u8, payload_ptr: *mut u8, payload_len: u32) -> u64 {
		let payload_len = payload_len as usize;
		let output = unsafe {
			let payload = Vec::from_raw_parts(payload_ptr, payload_len, payload_len);
			let ptr: fn(Vec<u8>) -> Vec<u8> = mem::transmute(func_ref);
			(ptr)(payload)
		};
		sp_runtime_interface::pack_ptr_and_len(output.as_ptr() as usize as _, output.len() as _)
	}

	/// Spawn new runtime task (wasm).
	pub fn spawn(
		entry_point: fn(Vec<u8>) -> Vec<u8>,
		payload: Vec<u8>,
		kind: AsyncStateType,
	) -> DataJoinHandle {
		let func_ptr: usize = unsafe { mem::transmute(entry_point) };

		let handle = sp_io::runtime_tasks::spawn(
			dispatch_wrapper as usize as _,
			func_ptr as u32,
			payload,
			kind as u8,
		);
		DataJoinHandle { handle }
	}
}

pub use inner::spawn;

#[cfg(test)]
mod tests {

	use super::*;

	fn async_runner(mut data: Vec<u8>) -> Vec<u8> {
		data.sort();
		data
	}

	fn async_panicker(_data: Vec<u8>) -> Vec<u8> {
		panic!("panic in async panicker!")
	}

	#[test]
	fn basic() {
		sp_io::TestExternalities::default().execute_with(|| {
			let a1 = spawn(async_runner, vec![5, 2, 1], AsyncStateType::Stateless).join();
			assert_eq!(a1, Some(vec![1, 2, 5]));
		})
	}

	#[test]
	fn panicking() {
		let res = sp_io::TestExternalities::default().execute_with_safe(||{
			spawn(async_panicker, vec![5, 2, 1], AsyncStateType::Stateless).join();
		});

		assert!(res.unwrap_err().contains("Closure panicked"));
	}

	#[test]
	fn many_joins() {
		sp_io::TestExternalities::default().execute_with_safe(|| {
			// converges to 1 only after 1000+ steps
			let mut running_val = 9780657630u64;
			let mut data = vec![];
			let handles = (0..1024).map(
				|_| {
					running_val = if running_val % 2 == 0 {
						running_val / 2
					} else {
						3 * running_val + 1
					};
					data.push(running_val as u8);
					(spawn(async_runner, data.clone(), AsyncStateType::Stateless), data.clone())
				}
			).collect::<Vec<_>>();

			for (handle, mut data) in handles {
				let result = handle.join();
				data.sort();

				assert_eq!(result, Some(data));
			}
		}).expect("Failed to run with externalities");
	}
}
