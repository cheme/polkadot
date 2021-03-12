// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
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

//! Snapshot export and import implementation.

use log::info;
use sc_client_api::{
	backend::{SnapshotSyncRoot, RangeSnapshot},
	utils::StateVisitorImpl, DatabaseError,
};
use sp_blockchain::{
	Error as ClientError,
};
use codec::{Decode, Encode, Compact, IoReader};
use sp_database::{SnapshotDbConf};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, One
};
use sp_state_machine::{
	StorageCollection,
	StateMachineStats,
};
use crate::utils::meta_keys;
use sp_blockchain::HeaderBackend;
use sp_database::Database;
use crate::{utils, columns, Backend};

/// Component of client needed to do snapshot import and export.
pub struct ClientSnapshotSync<Block: BlockT> {
	pub(crate) backend: Backend<Block>,
}

/// First byte of snapshot define
/// its mode.
#[repr(u8)]
enum SnapshotMode {
	/// Flat variant, no compression, and obviously no diff.
	Flat = 0,
}

struct HeaderRanges<N> {
	inner: Vec<(N, N)>,
}

impl<N: Ord> HeaderRanges<N> {
	fn new() -> Self {
		HeaderRanges {
			inner: Vec::new()
		}
	}

	fn insert(&mut self, item: (N, N)) {
		// unoptimized but we should not have to many components
		// declaration to merge.
		let mut i = 0;
		for range in self.inner.iter_mut() {
			if item.1 < range.0 {
				break;
			}
			if item.1 <= range.1 {
				if item.0 < range.0 {
					range.0 = item.0;
				}
				return;
			}
			if item.0 <= range.1 {
				range.1 = item.1;
				return;
			}
			i += 1;
		}
		self.inner.insert(i, item)
	}

	fn insert_all(&mut self, items: impl Iterator<Item = (N, N)>) {
		for item in items {
			self.insert(item);
		}
	}
}

impl<Block: BlockT> SnapshotSyncRoot<Block> for ClientSnapshotSync<Block> {
	fn export_sync(
		&self,
		mut out_dyn: &mut dyn std::io::Write,
		range: RangeSnapshot<Block>,
	) -> sp_blockchain::Result<()> {

		let chain_info = self.backend.blockchain.info();
		let finalized_hash = chain_info.finalized_hash;
		let finalized_number = chain_info.finalized_number;
		// dyn to impl
		let out = &mut out_dyn;
		// version
		out.write(&[0u8]).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot export error: {:?}", e)),
		)?;
		// info to init 'Meta' (need to allow read_meta and all pointing to to)
		//let to_hash = self.hash(to)?;
		range.to.encode_to(out);
		//to_hash.encode_to(out);
		// get range
		let nb = range.to - range.from;
		nb.encode_to(out);
		let mut header_ranges = HeaderRanges::<NumberFor<Block>>::new();
		header_ranges.insert((range.from, range.to));
		// registered components
		let registered_snapshot_sync = self.backend.blockchain.registered_snapshot_sync.read();
		let nb = registered_snapshot_sync.len();
		Compact(nb as u32).encode_to(out);
		for i in 0..nb {
			println!("Start H export {:?}", i);
			let mut ranges = registered_snapshot_sync[i].export_sync_meta(
				out_dyn,
				&range,
			)?;
			header_ranges.insert_all(ranges.additional_headers.drain(..));
		}

		// dyn to impl
		let out = &mut out_dyn;

		for range in header_ranges.inner.into_iter() {
			// headers (TODO consider removing digest??)
			// need to feed LeafSet::read_from_db (just insert in order)
			// and headers/blockids mapping (same)
			let mut i = range.0;
			while i <= range.1 {
				let header: Block::Header = self.backend.blockchain.header(BlockId::Number(i))?
					.ok_or_else(|| sp_blockchain::Error::Backend(
						format!("Header missing at {:?}", i),
					))?;
				header.encode_to(out);
				i += One::one();
			}
		}

		use sc_client_api::SnapshotDb;
		let state_visitor = StateVisitorImpl(&self.backend, &range.to_hash);
		out_dyn.write(&[SnapshotMode::Flat as u8])
			.map_err(|e| DatabaseError(Box::new(e)))?;


		// TOOD use plain range as param
		self.backend.snapshot_db.export_snapshot(
			out_dyn,
			finalized_number,
			range.from,
			range.to,
			range.flat,
			range.mode,
			state_visitor,
		)?;

		Ok(())
	}

	fn import_sync(
		&self,
		encoded: &mut dyn std::io::Read,
		dest_config: SnapshotDbConf,
	) -> sp_blockchain::Result<RangeSnapshot<Block>> {
		let mut buf = [0];
		// version
		encoded.read_exact(&mut buf[..1]).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;
		match buf[0] {
			b if b == 0 => (),
			_ => return Err(sp_blockchain::Error::Backend("Invalid snapshot version.".into())),
		}
		let mut reader = IoReader(encoded);
		let to: NumberFor<Block> = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;
		/*let to_hash: Block::Hash = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;*/
		let nb: NumberFor<Block> = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;
		let from = to - nb;

		let mut range = RangeSnapshot::<Block> {
			from,
			from_hash: Default::default(),
			to,
			to_hash: Default::default(),
			flat: false,
			mode: sp_database::SnapshotDBMode::NoDiff,
		};

		// registered components
		let registered_snapshot_sync = self.backend.blockchain.registered_snapshot_sync.read();
		let expected = registered_snapshot_sync.len();
		let nb: Compact<u32> = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;

		if nb.0 as usize != expected {
			return Err(sp_blockchain::Error::Backend("Invalid registerd component count.".into()));
		}

		let mut header_ranges = HeaderRanges::<NumberFor<Block>>::new();
		header_ranges.insert((range.from.clone(), range.to.clone()));
		for i in 0..expected {
			println!("Start H import {:?}", i);
			let mut ranges = registered_snapshot_sync[i].import_sync_meta(
				reader.0,
				&range,
			)?;
			header_ranges.insert_all(ranges.additional_headers.drain(..));
		}

		let from = range.from;
		for header_range in header_ranges.inner.into_iter() {

			let mut i = header_range.0;
			while i <= header_range.1 {
				let mut transaction = Default::default();
				let header: Block::Header = Decode::decode(&mut reader).map_err(|e|
					sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
				)?;
				let hash = header.hash();
				let parent_hash = header.parent_hash().clone();
				let number = header.number().clone();
				let lookup_key = utils::number_and_hash_to_lookup_key(number, hash)?;

				utils::insert_hash_to_key_mapping(
					&mut transaction,
					columns::KEY_LOOKUP,
					number,
					hash,
				)?;

				transaction.set_from_vec(columns::HEADER, &lookup_key, header.encode());

				if i == range.to {
					range.to_hash = header.hash().clone();
				}

				if i == range.from {
					// add parent of i as best and finalize (next steps would be to import this block.
					let number = i - One::one();
					range.from_hash = header.hash().clone();
					let hash = header.parent_hash().clone();
					let lookup_key = utils::number_and_hash_to_lookup_key(number, hash)?;
					utils::insert_hash_to_key_mapping(
						&mut transaction,
						columns::KEY_LOOKUP,
						number,
						hash,
					)?;

					self.backend.blockchain.update_meta(hash.clone(), number.clone(), true, true);
					transaction.set_from_vec(columns::META, meta_keys::BEST_BLOCK, lookup_key.clone());
					transaction.set_from_vec(columns::META, meta_keys::FINALIZED_BLOCK, lookup_key);
				}
				i += One::one();
				let mut leaves = self.backend.blockchain.leaves.write();
				let _displaced_leaf = leaves.import(hash, number, parent_hash);
				leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);

				self.backend.blockchain.db.commit(transaction)?;
			}
		}

		let mut buf = [0];
		reader.0.read_exact(&mut buf[..1])
			.map_err(|e| DatabaseError(Box::new(e)))?;
		range.flat = match buf[0] {
			u if u == SnapshotMode::Flat as u8 => true,
			_ => {
				let e = ClientError::StateDatabase("Unknown snapshot mode.".into());
				return Err(e);
			},
		};


		let mut config = dest_config.clone();
		// import default values will be reverted: tod can move to import_snapshot_db function
		// (revert too)
		config.enabled = true;
		config.pruning = None;
		config.lazy_pruning = None;
		config.primary_source = true; // needed to access historied-db
		config.debug_assert = false; // not really useful

		if range.flat {
			debug_assert!(range.from_hash == range.to_hash);
			let state_hash = range.to_hash.clone();

			// init snapshot db
			use sp_database::SnapshotDb; // TODO does this trait function still makes sense.
			self.backend.snapshot_db.import_snapshot_db(&mut reader.0, &config, range.flat, &state_hash)?;

			// header is imported by 'import_sync_meta'.
			let header = self.backend.blockchain.header(BlockId::Hash(state_hash.clone()))?
				.expect("Missing header");
			let expected_root = header.state_root().clone();
			use sc_client_api::backend::{Backend, BlockImportOperation};
			let mut op = self.backend.begin_operation()?;
			self.backend.begin_state_operation(&mut op, BlockId::Hash(Default::default()))?;
			info!("Initializing import block/state (header-hash: {})",
				state_hash,
			);
			let data = self.backend.snapshot_db.state_iter_at(&state_hash, Some(&config))?;
			let state_root = op.inject_finalized_state(&state_hash, data)
				.map_err(|e| DatabaseError(Box::new(e)))?;
			// TODO get state root from header and pass as param
			if expected_root != state_root {
				panic!("Unexpected root {:?}, in header {:?}.", state_root, expected_root);
			}
			// only state import, but need to have pending block to commit actual data.
			op.set_block_data(
				header,
				None,
				None,
				sc_client_api::NewBlockState::Final,
			).map_err(|e| DatabaseError(Box::new(e)))?;
			self.backend.commit_operation(op)
				.map_err(|e| DatabaseError(Box::new(e)))?;

			if !dest_config.enabled {
				// clear snapshot db
				self.backend.snapshot_db.clear_snapshot_db()?;
			} else {
				self.backend.snapshot_db.update_running_conf(
					Some(dest_config.primary_source),
					Some(dest_config.debug_assert),
					dest_config.pruning,
					dest_config.lazy_pruning,
					Some(dest_config.cache_size),
				)?;
				if dest_config.pruning.is_some() {
					// run pruning now
					unimplemented!();
				}
			}
		} else {
			unimplemented!();
		}

		Ok(range)
	}
}


