// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Substrate offchain workers.
//!
//! The offchain workers is a special function of the runtime that
//! gets executed after block is imported. During execution
//! it's able to asynchronously submit extrinsics that will either
//! be propagated to other nodes or added to the next block
//! produced by the node as unsigned transactions.
//!
//! Offchain workers can be used for computation-heavy tasks
//! that are not feasible for execution during regular block processing.
//! It can either be tasks that no consensus is required for,
//! or some form of consensus over the data can be built on-chain
//! for instance via:
//! 1. Challenge period for incorrect computations
//! 2. Majority voting for results
//! 3. etc

#![warn(missing_docs)]

use std::{
	fmt, marker::PhantomData, sync::Arc,
	collections::HashSet,
};

use parking_lot::Mutex;
use threadpool::ThreadPool;
use sp_api::{ApiExt, ProvideRuntimeApi, Hasher};
use futures::future::Future;
use log::{debug, warn};
use sc_network::{ExHashT, NetworkService, NetworkStateInfo, PeerId};
use sp_core::{offchain::{self, OffchainStorage, BlockChainOffchainStorage, OffchainLocksRequirement},
	ExecutionContext, traits::SpawnNamed};
use sp_runtime::{generic::BlockId, traits::{self, Header, HashFor}};
use futures::{prelude::*, future::ready};

mod api;
use api::SharedClient;

pub use sp_offchain::{OffchainWorkerApi, STORAGE_PREFIX, LOCAL_STORAGE_PREFIX};

/// NetworkProvider provides [`OffchainWorkers`] with all necessary hooks into the
/// underlying Substrate networking.
pub trait NetworkProvider: NetworkStateInfo {
	/// Set the authorized peers.
	fn set_authorized_peers(&self, peers: HashSet<PeerId>);
	
	/// Set the authorized only flag.
	fn set_authorized_only(&self, reserved_only: bool);
}

impl<B, H> NetworkProvider for NetworkService<B, H>
where
	B: traits::Block + 'static,
	H: ExHashT,
{
	fn set_authorized_peers(&self, peers: HashSet<PeerId>) {
		self.set_authorized_peers(peers)
	}

	fn set_authorized_only(&self, reserved_only: bool) {
		self.set_authorized_only(reserved_only)
	}
}

/// An offchain workers manager.
pub struct OffchainWorkers<Client, PersistentStorage, LocalStorage, Block: traits::Block> {
	client: Arc<Client>,
	db: PersistentStorage,
	local_db: LocalStorage,
	_block: PhantomData<Block>,
	thread_pool: Mutex<ThreadPool>,
	shared_client: SharedClient,
}

impl<
	Client,
	PersistentStorage,
	LocalStorage,
	Block: traits::Block,
> OffchainWorkers<Client, PersistentStorage, LocalStorage, Block> {
	/// Creates new `OffchainWorkers`.
	pub fn new(client: Arc<Client>, db: PersistentStorage, local_db: LocalStorage) -> Self {
		let shared_client = SharedClient::new();
		Self {
			client,
			db,
			local_db,
			_block: PhantomData,
			thread_pool: Mutex::new(ThreadPool::new(num_cpus::get())),
			shared_client,
		}
	}
}

impl<Client, PersistentStorage, LocalStorage, Block: traits::Block> fmt::Debug for OffchainWorkers<
	Client,
	PersistentStorage,
	LocalStorage,
	Block,
> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("OffchainWorkers").finish()
	}
}

impl<Client, PersistentStorage, LocalStorage, Block> OffchainWorkers<
	Client,
	PersistentStorage,
	LocalStorage,
	Block,
> where
	Block: traits::Block,
	Client: ProvideRuntimeApi<Block> + Send + Sync + 'static,
	Client::Api: OffchainWorkerApi<Block>,
	PersistentStorage: OffchainStorage + 'static,
	LocalStorage: BlockChainOffchainStorage<BlockId = <HashFor<Block> as Hasher>::Out> + 'static,
{
	/// Start the offchain workers after given block.
	#[must_use]
	pub fn on_block_imported(
		&self,
		header: &Block::Header,
		network_provider: Arc<dyn NetworkProvider + Send + Sync>,
		is_validator: bool,
		is_new_best: bool,
	) -> impl Future<Output = ()> {
		let runtime = self.client.runtime_api();
		let at = BlockId::hash(header.hash());
		let has_api_v3 = runtime.has_api_with::<dyn OffchainWorkerApi<Block, Error = ()>, _>(
			&at, |v| v == 3
		);
		// early test to avoid a spawn (before api v 3 no process did run
		// on non new best nodes).
		if let Ok(false) = has_api_v3 {
			if !is_new_best {
				log::debug!(
					target: "sc_offchain",
					"Skipping offchain workers for non-canon block: {:?}",
					header,
				);
				return futures::future::Either::Right(futures::future::ready(()));
			}
		}
		let has_api_v2 = runtime.has_api_with::<dyn OffchainWorkerApi<Block, Error = ()>, _>(
			&at, |v| v == 2
		);
		let has_api_v1 = runtime.has_api_with::<dyn OffchainWorkerApi<Block, Error = ()>, _>(
			&at, |v| v == 1
		);
		let version = match (has_api_v1, has_api_v2, has_api_v3) {
			(_, _, Ok(true)) => 2,
			(_, Ok(true), _) => 2,
			(Ok(true), _, _) => 1,
			err => {
				let help = "Consider turning off offchain workers if they are not part of your runtime.";
				log::error!("Unsupported Offchain Worker API version: {:?}. {}.", err, help);
				0
			}
		};
		debug!("Checking offchain workers at {:?}: version:{}", at, version);
		if version > 0 {
			let local_lock_reqirements = if version > 2 {
				match runtime.offchain_worker_local_locks(&at) {
					Ok(locks) => locks,
					Err(error) => {
						log::error!("Error getting local offchain locks {:?}, pursuing with no access.", error);
						Default::default()
					},
				}
			} else {
				OffchainLocksRequirement::default()
			};
			let local_db_at = if let Some(local_db_at) = self.local_db.at(header.hash(), local_lock_reqirements) {
				local_db_at
			} else {
				log::error!("Error no chain state for offchain local db at {:?}", at);
				return futures::future::Either::Right(futures::future::ready(()));
			};
			let (api, runner) = api::AsyncApi::new(
				self.db.clone(),
				local_db_at.clone(),
				network_provider,
				is_validator,
				is_new_best,
				self.shared_client.clone(),
			);
			debug!("Spawning offchain workers at {:?}", at);
			let header = header.clone();
			let client = self.client.clone();
			self.spawn_worker(move || {
				let runtime = client.runtime_api();
				let api = Box::new(api);
				debug!("Running offchain workers at {:?}", at);
				let context = ExecutionContext::OffchainCall(Some(
					(api, offchain::Capabilities::all())
				));
				let run = if version > 1 {
					runtime.offchain_worker_with_context(&at, context, &header)
				} else {
					#[allow(deprecated)]
					runtime.offchain_worker_before_version_2_with_context(
						&at, context, *header.number()
					)
				};
				if let Err(e) =	run {
					log::error!("Error running offchain workers at {:?}: {:?}", at, e);
				}
			});
			futures::future::Either::Left(runner.process())
		} else {
			futures::future::Either::Right(futures::future::ready(()))
		}
	}

	/// Spawns a new offchain worker.
	///
	/// We spawn offchain workers for each block in a separate thread,
	/// since they can run for a significant amount of time
	/// in a blocking fashion and we don't want to block the runtime.
	///
	/// Note that we should avoid that if we switch to future-based runtime in the future,
	/// alternatively:
	fn spawn_worker(&self, f: impl FnOnce() -> () + Send + 'static) {
		self.thread_pool.lock().execute(f);
	}
}

/// Inform the offchain worker about new imported blocks
pub async fn notification_future<Client, PersistentStorage, LocalStorage, Block, Spawner>(
	is_validator: bool,
	client: Arc<Client>,
	offchain: Arc<OffchainWorkers<Client, PersistentStorage, LocalStorage, Block>>,
	spawner: Spawner,
	network_provider: Arc<dyn NetworkProvider + Send + Sync>,
)
	where
		Block: traits::Block,
		Client: ProvideRuntimeApi<Block> + sc_client_api::BlockchainEvents<Block> + Send + Sync + 'static,
		Client::Api: OffchainWorkerApi<Block>,
		PersistentStorage: OffchainStorage + 'static,
		LocalStorage: BlockChainOffchainStorage<BlockId = <HashFor<Block> as Hasher>::Out> + 'static,
		Spawner: SpawnNamed
{
	client.import_notification_stream().for_each(move |n| {
		// Update branch tip
		offchain.local_db.new_imported_block(
			&n.header.hash(),
			n.header.parent_hash(),
		);
		spawner.spawn(
			"offchain-on-block",
			offchain.on_block_imported(
				&n.header,
				network_provider.clone(),
				is_validator,
				n.is_new_best,
			).boxed(),
		);

		ready(())
	}).await;
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::sync::Arc;
	use sc_network::{Multiaddr, PeerId};
	use substrate_test_runtime_client::{TestClient, runtime::Block};
	use sc_transaction_pool::{BasicPool, FullChainApi};
	use sp_transaction_pool::{TransactionPool, InPoolTransaction};

	struct TestNetwork();

	impl NetworkStateInfo for TestNetwork {
		fn external_addresses(&self) -> Vec<Multiaddr> {
			Vec::new()
		}

		fn local_peer_id(&self) -> PeerId {
			PeerId::random()
		}
	}

	impl NetworkProvider for TestNetwork {
		fn set_authorized_peers(&self, _peers: HashSet<PeerId>) {
			unimplemented!()
		}

		fn set_authorized_only(&self, _reserved_only: bool) {
			unimplemented!()
		}
	}

	struct TestPool(
		Arc<BasicPool<FullChainApi<TestClient, Block>, Block>>
	);

	impl sp_transaction_pool::OffchainSubmitTransaction<Block> for TestPool {
		fn submit_at(
			&self,
			at: &BlockId<Block>,
			extrinsic: <Block as traits::Block>::Extrinsic,
		) -> Result<(), ()> {
			let source = sp_transaction_pool::TransactionSource::Local;
			futures::executor::block_on(self.0.submit_one(&at, source, extrinsic))
				.map(|_| ())
				.map_err(|_| ())
		}
	}

	#[test]
	fn should_call_into_runtime_and_produce_extrinsic() {
		use sc_client_api::Backend;
		use substrate_test_runtime_client::{
			TestClientBuilder,
			DefaultTestClientBuilderExt,
			TestClientBuilderExt,
		};
		sp_tracing::try_init_simple();
		let builder = TestClientBuilder::new();
		let local_db = builder.backend().offchain_local_storage().unwrap();
		let client = Arc::new(builder.build());
		let spawner = sp_core::testing::TaskExecutor::new();
		let pool = TestPool(BasicPool::new_full(
			Default::default(),
			None,
			spawner,
			client.clone(),
		));
		let db = sc_client_db::offchain::LocalStorage::new_test();
		
		let network = Arc::new(TestNetwork());
		let header = client.header(&BlockId::number(0)).unwrap().unwrap();

		// when
		let offchain = OffchainWorkers::new(client, db, local_db);
		futures::executor::block_on(
			offchain.on_block_imported(&header, network, false, true)
		);

		// then
		assert_eq!(pool.0.status().ready, 1);
		assert_eq!(pool.0.ready().next().unwrap().is_propagable(), false);
	}
}
