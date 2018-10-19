// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Substrate Client and associated logic.

#![warn(missing_docs)]
#![recursion_limit="128"]

pub mod error;
pub mod blockchain;
pub mod backend;
pub mod cht;
pub mod in_mem;
pub mod genesis;
pub mod block_builder;
pub mod light;
mod leaves;
mod call_executor;
mod client;
mod notifications;

pub use crate::blockchain::Info as ChainInfo;
pub use crate::call_executor::{CallResult, CallExecutor, LocalCallExecutor};
pub use crate::client::{
	new_with_backend,
	new_in_mem,
	BlockBody, BlockStatus, BlockOrigin, ImportNotifications, FinalityNotifications, BlockchainEvents,
	Client, ClientInfo, ChainHead, ImportResult, ImportBlock,
};
pub use crate::notifications::{StorageEventStream, StorageChangeSet};
pub use state_machine::ExecutionStrategy;
pub use crate::leaves::LeafSet;

/// Traits for interfacing with the runtime from the client.
pub mod runtime_api {
	pub use runtime_api::*;
}
