// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Shareable Substrate traits.

#[cfg(feature = "std")]
use std::{
	fmt::{Debug, Display},
	panic::UnwindSafe,
};
use sp_std::{
	borrow::Cow,
	boxed::Box,
	vec::Vec,
};
use dyn_clone::DynClone;

pub use sp_externalities::{Externalities, ExternalitiesExt, AsyncExternalities, WorkerResult};

/// Code execution engine.
#[cfg(feature = "std")]
pub trait CodeExecutor: Sized + Send + Sync + CallInWasm + Clone + 'static {
	/// Externalities error type.
	type Error: Display + Debug + Send + Sync + 'static;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<
		R: codec::Codec + PartialEq,
		NC: FnOnce() -> Result<R, Box<dyn std::error::Error + Send + Sync>> + UnwindSafe,
	>(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<crate::NativeOrEncoded<R>, Self::Error>, bool);
}

/// Something that can fetch the runtime `:code`.
pub trait FetchRuntimeCode {
	/// Fetch the runtime `:code`.
	///
	/// If the `:code` could not be found/not available, `None` should be returned.
	fn fetch_runtime_code<'a>(&'a self) -> Option<Cow<'a, [u8]>>;
}

/// Wrapper to use a `u8` slice or `Vec` as [`FetchRuntimeCode`].
pub struct WrappedRuntimeCode<'a>(pub Cow<'a, [u8]>);

impl<'a> FetchRuntimeCode for WrappedRuntimeCode<'a> {
	fn fetch_runtime_code<'b>(&'b self) -> Option<Cow<'b, [u8]>> {
		Some(self.0.as_ref().into())
	}
}

/// Type that implements [`FetchRuntimeCode`] and always returns `None`.
pub struct NoneFetchRuntimeCode;

impl FetchRuntimeCode for NoneFetchRuntimeCode {
	fn fetch_runtime_code<'a>(&'a self) -> Option<Cow<'a, [u8]>> {
		None
	}
}

/// The Wasm code of a Substrate runtime.
#[derive(Clone)]
pub struct RuntimeCode<'a> {
	/// The code fetcher that can be used to lazily fetch the code.
	pub code_fetcher: &'a dyn FetchRuntimeCode,
	/// The optional heap pages this `code` should be executed with.
	///
	/// If `None` are given, the default value of the executor will be used.
	pub heap_pages: Option<u64>,
	/// The SCALE encoded hash of `code`.
	///
	/// The hashing algorithm isn't that important, as long as all runtime
	/// code instances use the same.
	pub hash: Vec<u8>,
}

impl<'a> PartialEq for RuntimeCode<'a> {
	fn eq(&self, other: &Self) -> bool {
		self.hash == other.hash
	}
}

impl<'a> RuntimeCode<'a> {
	/// Create an empty instance.
	///
	/// This is only useful for tests that don't want to execute any code.
	pub fn empty() -> Self {
		Self {
			code_fetcher: &NoneFetchRuntimeCode,
			hash: Vec::new(),
			heap_pages: None,
		}
	}
}

impl<'a> FetchRuntimeCode for RuntimeCode<'a> {
	fn fetch_runtime_code<'b>(&'b self) -> Option<Cow<'b, [u8]>> {
		self.code_fetcher.fetch_runtime_code()
	}
}

/// Could not find the `:code` in the externalities while initializing the [`RuntimeCode`].
#[cfg(feature = "std")]
#[derive(Debug)]
pub struct CodeNotFound;

#[cfg(feature = "std")]
impl std::fmt::Display for CodeNotFound {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
		write!(f, "the storage entry `:code` doesn't have any code")
	}
}

/// `Allow` or `Disallow` missing host functions when instantiating a WASM blob.
#[derive(Clone, Copy, Debug)]
pub enum MissingHostFunctions {
	/// Any missing host function will be replaced by a stub that returns an error when
	/// being called.
	Allow,
	/// Any missing host function will result in an error while instantiating the WASM blob,
	Disallow,
}

impl MissingHostFunctions {
	/// Are missing host functions allowed?
	pub fn allowed(self) -> bool {
		matches!(self, Self::Allow)
	}
}

/// Something that can call a method in a WASM blob.
#[cfg(feature = "std")]
pub trait CallInWasm: Send + Sync {
	/// Call the given `method` in the given `wasm_blob` using `call_data` (SCALE encoded arguments)
	/// to decode the arguments for the method.
	///
	/// Returns the SCALE encoded return value of the method.
	///
	/// # Note
	///
	/// If `code_hash` is `Some(_)` the `wasm_code` module and instance will be cached internally,
	/// otherwise it is thrown away after the call.
	fn call_in_wasm(
		&self,
		wasm_code: &[u8],
		code_hash: Option<Vec<u8>>,
		method: &str,
		call_data: &[u8],
		ext: &mut dyn Externalities,
		missing_host_functions: MissingHostFunctions,
	) -> Result<Vec<u8>, String>;
}

#[cfg(feature = "std")]
sp_externalities::decl_extension! {
	/// The call-in-wasm extension to register/retrieve from the externalities.
	pub struct CallInWasmExt(Box<dyn CallInWasm>);
}

#[cfg(feature = "std")]
impl CallInWasmExt {
	/// Creates a new instance of `Self`.
	pub fn new<T: CallInWasm + 'static>(inner: T) -> Self {
		Self(Box::new(inner))
	}
}

sp_externalities::decl_extension! {
	/// Task executor extension.
	pub struct TaskExecutorExt(Box<dyn SpawnNamed>);
}

impl TaskExecutorExt {
	/// New instance of task executor extension.
	pub fn new(spawn_handle: impl SpawnNamed + Send + 'static) -> Self {
		Self(Box::new(spawn_handle))
	}
}

/// Runtime spawn extension.
pub trait RuntimeSpawn: Send {
	/// Run a call as native.
	///
	/// Returns handle of the spawned task.
	fn spawn_call_native(
		&self,
		func: fn(Vec<u8>) -> Vec<u8>,
		data: Vec<u8>,
		calling_ext: &mut dyn Externalities,
	) -> u64;

	/// Create new runtime instance and use dynamic dispatch to invoke with specified payload.
	///
	/// Returns handle of the spawned task.
	///
	/// Function pointers (`dispatcher_ref`, `func`) are WASM pointer types.
	fn spawn_call(&self,
		dispatcher_ref: u32,
		func: u32,
		payload: Vec<u8>,
		ext: &mut dyn Externalities,
	) -> u64;

	/// Join the result of previously created runtime instance invocation.
	fn join(&self, handle: u64, calling_ext: &mut dyn Externalities) -> Option<Vec<u8>>;

	/// Stop the previous created runtime instance invocation.
	///
	/// This only guarantee that next call to join with this handle
	/// will return `None`.
	/// Client can handle this as he can (for instance worker
	/// can not always be stopped).
	fn dismiss(&self, handle: u64, calling_ext: &mut dyn Externalities);

	/// Possibly change the number of runtime runing in the pool.
	/// Note that this should only increase capacity (default value
	/// being 0).
	/// This capacity increase is optional from the client side, and
	/// client can limit the number of concurrent threads, as this is
	/// not consensus critical.
	fn set_capacity(&self, capacity: u32);
}

sp_externalities::decl_extension! {
	/// Extension that supports spawning extra runtime instances in externalities.
	pub struct RuntimeSpawnExt(Box<dyn RuntimeSpawn>);
}

/// Remote handle for a future.
pub type TaskHandle = Box<dyn TaskHandleTrait>;

/// Alias of the future type to use with `SpawnedNamed` trait.
pub type BoxFuture = futures::future::BoxFuture<'static, ()>;

/// Something that can spawn tasks (blocking and non-blocking) with an assigned name.
pub trait SpawnNamed: SpawnLimit + DynClone + Send + Sync {
	/// Spawn the given blocking future.
	///
	/// The given `name` is used to identify the future in tracing.
	fn spawn_blocking(&self, name: &'static str, future: BoxFuture);

	/// Spawn the given non-blocking future.
	/// The handle optionally allows to signal that the task can be dismiss.
	///
	/// The given `name` is used to identify the future in tracing.
	fn spawn(
		&self,
		name: &'static str,
		future: BoxFuture,
	) -> Option<TaskHandle>;
}
dyn_clone::clone_trait_object!(SpawnNamed);

/// This can be use to implement shared pool.
pub trait SpawnLimit: DynClone + Send + Sync {
	/// Ask for a given number of tasks, return the
	/// actual number reserved.
	fn try_reserve(&self, number_of_tasks: usize) -> usize;

	/// Release a given number of task.
	fn release(&self, number_of_tasks: usize);
}
dyn_clone::clone_trait_object!(SpawnLimit);

/// Handle over a spawn named future.
pub trait TaskHandleTrait: Send {
	/// Indicate to the scheduler that task can
	/// be dropped.
	fn dismiss(&mut self);
}


impl SpawnNamed for Box<dyn SpawnNamed> {
	fn spawn_blocking(&self, name: &'static str, future: BoxFuture) {
		(**self).spawn_blocking(name, future)
	}

	fn spawn(
		&self,
		name: &'static str,
		future: BoxFuture,
	) -> Option<TaskHandle> {
		(**self).spawn(name, future)
	}
}

impl SpawnLimit for Box<dyn SpawnNamed> {
	fn try_reserve(&self, number_of_tasks: usize) -> usize {
		(**self).try_reserve(number_of_tasks)
	}

	fn release(&self, number_of_tasks: usize) {
		(**self).release(number_of_tasks)
	}
}

/// Something that can spawn essential tasks (blocking and non-blocking) with an assigned name.
///
/// Essential tasks are special tasks that should take down the node when they end.
pub trait SpawnEssentialNamed: DynClone + Send + Sync {
	/// Spawn the given blocking future.
	///
	/// The given `name` is used to identify the future in tracing.
	fn spawn_essential_blocking(&self, name: &'static str, future: futures::future::BoxFuture<'static, ()>);
	/// Spawn the given non-blocking future.
	///
	/// The given `name` is used to identify the future in tracing.
	fn spawn_essential(&self, name: &'static str, future: futures::future::BoxFuture<'static, ()>);
}
dyn_clone::clone_trait_object!(SpawnEssentialNamed);

#[cfg(feature = "std")]
impl SpawnEssentialNamed for Box<dyn SpawnEssentialNamed> {
	fn spawn_essential_blocking(&self, name: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		(**self).spawn_essential_blocking(name, future)
	}

	fn spawn_essential(&self, name: &'static str, future: futures::future::BoxFuture<'static, ()>) {
		(**self).spawn_essential(name, future)
	}
}
