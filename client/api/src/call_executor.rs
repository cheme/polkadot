// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
//! A method call executor interface.

use std::{panic::UnwindSafe, result, cell::RefCell};
use codec::{Encode, Decode};
use sp_runtime::{
	generic::BlockId, traits::{Block as BlockT, HashFor},
};
use sp_state_machine::{
	OverlayedChanges, ExecutionManager, ExecutionStrategy, backend::ProofRegStateFor,
};
use sc_executor::{RuntimeVersion, NativeVersion};
use sp_externalities::Extensions;
use sp_core::{NativeOrEncoded,offchain::storage::OffchainOverlayedChanges};

use sp_api::{InitializeBlock, StorageTransactionCache};
use crate::execution_extensions::ExecutionExtensions;

/// Executor Provider
pub trait ExecutorProvider<Block: BlockT> {
	/// executor instance
	type Executor: CallExecutor<Block>;

	/// Get call executor reference.
	fn executor(&self) -> &Self::Executor;

	/// Get a reference to the execution extensions.
	fn execution_extensions(&self) -> &ExecutionExtensions<Block>;
}

/// Method call executor.
pub trait CallExecutor<B: BlockT> {
	/// Externalities error type.
	type Error: sp_state_machine::Error;

	/// The backend used by the node.
	type Backend: crate::backend::Backend<B>;

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	fn call(
		&self,
		id: &BlockId<B>,
		method: &str,
		call_data: &[u8],
		strategy: ExecutionStrategy,
		extensions: Option<Extensions>,
	) -> Result<Vec<u8>, sp_blockchain::Error>;

	/// Execute a contextual call on top of state in a block of a given hash.
	///
	/// No changes are made.
	/// Before executing the method, passed header is installed as the current header
	/// of the execution context.
	fn contextual_call<
		'a,
		IB: Fn() -> sp_blockchain::Result<()>,
		EM: Fn(
			Result<NativeOrEncoded<R>, Self::Error>,
			Result<NativeOrEncoded<R>, Self::Error>
		) -> Result<NativeOrEncoded<R>, Self::Error>,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
	>(
		&self,
		initialize_block_fn: IB,
		at: &BlockId<B>,
		method: &str,
		call_data: &[u8],
		changes: &RefCell<OverlayedChanges>,
		offchain_changes: &RefCell<OffchainOverlayedChanges>,
		storage_transaction_cache: Option<&RefCell<
			StorageTransactionCache<B, <Self::Backend as crate::backend::Backend<B>>::State>,
		>>,
		initialize_block: InitializeBlock<'a, B>,
		execution_manager: ExecutionManager<EM>,
		native_call: Option<NC>,
		recorder: Option<ProofRegStateFor<<Self::Backend as crate::backend::Backend<B>>::State, HashFor<B>>>,
		extensions: Option<Extensions>,
	) -> sp_blockchain::Result<NativeOrEncoded<R>> where ExecutionManager<EM>: Clone;

	/// Extract RuntimeVersion of given block
	///
	/// No changes are made.
	fn runtime_version(&self, id: &BlockId<B>) -> Result<RuntimeVersion, sp_blockchain::Error>;

	/// Execute a call to a contract on top of given state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_state<S: sp_state_machine::backend::Backend<HashFor<B>>>(
		&self,
		state: S,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, S::StorageProof), sp_blockchain::Error> {
		let proof_state = state.as_proof_backend()
			.ok_or_else(||
				Box::new(sp_state_machine::ExecutionError::UnableToGenerateProof)
					as Box<dyn sp_state_machine::Error>
			)?;
		self.prove_at_proof_backend_state(&proof_state, overlay, method, call_data)
	}

	/// Execute a call to a contract on top of given trie state, gathering execution proof.
	///
	/// No changes are made.
	fn prove_at_proof_backend_state<P: sp_state_machine::backend::ProofRegBackend<HashFor<B>>>(
		&self,
		proof_backend: &P,
		overlay: &mut OverlayedChanges,
		method: &str,
		call_data: &[u8]
	) -> Result<(Vec<u8>, P::StorageProof), sp_blockchain::Error>;

	/// Get runtime version if supported.
	fn native_runtime_version(&self) -> Option<&NativeVersion>;
}
