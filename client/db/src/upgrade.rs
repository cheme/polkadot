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

//! Database upgrade logic.

use std::fs;
use std::io::{Read, Write, ErrorKind};
use std::path::{Path, PathBuf};
use log::warn;
use std::marker::PhantomData;
use std::time::{Duration, Instant};

use sp_runtime::traits::{Block as BlockT, HashFor, NumberFor, Header as HeaderT};
use crate::HValue;
use crate::utils::DatabaseType;
use crate::{StateDb, PruningMode, StateMetaDb};
use historied_db::historied::tree_management::TreeManagement;
use historied_db::{
	StateDBRef, InMemoryStateDBRef, StateDB, ManagementRef, Management,
	ForkableManagement, Latest, UpdateResult,
	historied::{InMemoryValue, InMemoryValueSlice, Value},
	historied::tree::Tree,
	historied::tree_management::{Tree as TreeMgmt, ForkPlan},
};
use codec::{Decode, Encode};

use std::sync::Arc;

/// Version file name.
const VERSION_FILE_NAME: &'static str = "db_version";

/// Current db version.
const CURRENT_VERSION: u32 = 2;

/// Upgrade database to current version.
pub fn upgrade_db<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	let is_empty = db_path.read_dir().map_or(true, |mut d| d.next().is_none());
	if !is_empty {
		let db_version = current_version(db_path)?;
		match db_version {
			0 => Err(sp_blockchain::Error::Backend(format!("Unsupported database version: {}", db_version)))?,
			1 => migrate_1_to_2::<Block>(db_path, db_type)?,
			2 => (),
			42 => {
				delete_historied::<Block>(db_path, db_type)?;
				let now = Instant::now();
				let hash_for_root = inject_non_canonical::<Block>(db_path, db_type)?;
				println!("inject non canonnical in {}", now.elapsed().as_millis());
				compare_latest_roots::<Block>(db_path, db_type, hash_for_root)?;
			},
			_ => Err(sp_blockchain::Error::Backend(format!("Future database version: {}", db_version)))?,
		}
	}

	update_version(db_path)
}

/// Migration from version1 to version2:
/// the number of columns has changed from 11 to 15;
fn migrate_1_to_2<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
	// Number of columns in v0.
	const V1_NUM_COLUMNS: u32 = 11;
	{
		let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(V1_NUM_COLUMNS);
		let path = db_path.to_str()
			.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
		let db = kvdb_rocksdb::Database::open(&db_config, &path)
			.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
		db.add_column().map_err(db_err)?;
	}

	Ok(())
}

fn delete_non_canonical<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {
		let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
		let path = db_path.to_str()
			.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
		let db_read = kvdb_rocksdb::Database::open(&db_config, &path)
			.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;

		let non_canon = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::FINALIZED_BLOCK).unwrap().unwrap();
		let latest = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK).unwrap().unwrap();
		println!("non_can: {:?} latest : {:?}", non_canon, latest);
		let mut tx = db_read.transaction();
		tx.put(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK, non_canon.as_slice());
		db_read.write(tx).expect("dtdt");
		println!("replaced best block by finalized block value");
		

		let db = sp_database::as_database(db_read);

		let meta = crate::read_meta::<Block>(&*db, crate::columns::HEADER)?;
		let leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::read_from_db(&*db, crate::columns::META, crate::meta_keys::LEAF_PREFIX)?;
		println!("previous leaf set: {:?}", leaves);

		let mut leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::new();
		leaves.import(meta.finalized_hash, meta.finalized_number, Default::default());

		println!("new leaf set: {:?}", leaves);
		let mut tx = sp_database::Transaction::new();

		leaves.prepare_transaction(&mut tx, crate::columns::META, crate::meta_keys::LEAF_PREFIX);
		// second call on purpose
		leaves.prepare_transaction(&mut tx, crate::columns::META, crate::meta_keys::LEAF_PREFIX);
		db.commit(tx);


		let state_db: StateDb<Block::Hash, Vec<u8>> = StateDb::new(
			PruningMode::Constrained(sc_state_db::Constraints {
				max_blocks: None, // may require info in the future, in fact we should fetch it
				max_mem: None,
			}),
			true, // Rc or not does not matter in this case
			&StateMetaDb(&*db),
		).expect("TODO err");

		state_db.clear_non_canonical();
		Ok(())
/*		let storage_db = crate::StorageDb {
			db: db.clone(),
			state_db,
			prefix_keys: true,
		};
	
		let storage: Arc<crate::StorageDb<Block>> = Arc::new(storage_db);*/
}

fn inject_non_canonical<Block: BlockT>(
	db_path: &Path,
	db_type: DatabaseType,
) -> sp_blockchain::Result<Block::Hash> {
	let path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;

	let journals = {
		let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
		let db_read = kvdb_rocksdb::Database::open(&db_config, &path)
			.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;

		let non_canon = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::FINALIZED_BLOCK).unwrap().unwrap();
		let latest = db_read.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK).unwrap().unwrap();
		println!("non_can: {:?} latest : {:?}", non_canon, latest);
		
		let db = sp_database::as_database(db_read);
		let meta = crate::read_meta::<Block>(&*db, crate::columns::HEADER)?;
		let leaves = crate::LeafSet::<Block::Hash, NumberFor<Block>>::read_from_db(&*db, crate::columns::META, crate::meta_keys::LEAF_PREFIX)?;
		println!("previous leaf set: {:?}", leaves);

		let meta = StateMetaDb(&*db);
		let state_db: StateDb<Block::Hash, Vec<u8>> = StateDb::new(
			PruningMode::Constrained(sc_state_db::Constraints {
				max_blocks: None, // may require info in the future, in fact we should fetch it
				max_mem: None,
			}),
			true, // Rc or not does not matter in this case
			&meta,
		).expect("TODO err");

		state_db.get_non_cannonical_journals(meta).expect("aib")
	};

	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
	let db_histo = Arc::new(kvdb_rocksdb::Database::open(&db_config, &path)
		.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?);

	let historied_persistence = crate::RocksdbStorage(db_histo.clone());
	let mut management = TreeManagement::<
		<HashFor<Block> as hash_db::Hasher>::Out,
		u32,
		u32,
		Vec<u8>,
		crate::TreeManagementPersistence,
	>::from_ser(historied_persistence);
	
	let mut last_hash = Default::default();
		for journal in journals {
			if let Some(state) = management.get_db_state_for_fork(&journal.parent_hash) {
				management.append_external_state(journal.hash, &state);
				last_hash = journal.hash;
				let state = management.latest_state();
				println!("adding journal: {:?} parent {:?}, at {:?}", journal.hash, journal.parent_hash, state);
				let mut historied_db = crate::HistoriedDBMut {
					current_state: state,
					db: db_histo.clone(),
				};
				let mut tx = historied_db.transaction();
				let mut nb_ins = 0;
				let mut nb_del = 0;
				for (k, v) in journal.inserted {
					nb_ins += 1;
					historied_db.update_single(k.as_slice(), Some(v), &mut tx);
				}
				for k in journal.deleted {
					nb_del += 1;
					historied_db.update_single(k.as_slice(), None, &mut tx);
				}
				historied_db.write_change_set(tx);
				println!("added, ins: {}, del: {}", nb_ins, nb_del);
				break; // TODO for test remove
			} else {
				println!("warn ignoring journal: {:?} parent {:?}", journal.hash, journal.parent_hash);
			}
		}

		Ok(last_hash)
}

fn compare_latest_roots<Block: BlockT>(db_path: &Path, db_type: DatabaseType, hash_for_root: Block::Hash) -> sp_blockchain::Result<()> {
	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
	let path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
	let db = kvdb_rocksdb::Database::open(&db_config, &path)
		.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;

	let (tree_root, block_hash) = match db.get(crate::utils::COLUMN_META, crate::meta_keys::BEST_BLOCK) {
		Ok(id) => {
			let id = id.unwrap();
			let id = db.get(crate::columns::HEADER, &id).expect("s").map(|b| Block::Header::decode(&mut &b[..]).ok());
			use sp_runtime::traits::Header;
			let id = id.unwrap().expect("d");
			warn!("Head is {:?}", id);
	/*				let mut hash = <HashFor::<Block> as hash_db::Hasher>::Out::default();
				hash.as_mut().copy_from_slice(id.as_slice());*/
			(id.state_root().clone(), id.hash().clone())
		},
		Err(e) => panic!("no best block is bad sign {:?}", e),
	};
	println!("hash queryied: {:?}", tree_root);
	let db = Arc::new(db);
	let now = Instant::now();
	let historied_persistence = crate::RocksdbStorage(db.clone());
	let mut management = TreeManagement::<
		<HashFor<Block> as hash_db::Hasher>::Out,
		u32,
		u32,
		Vec<u8>,
		crate::TreeManagementPersistence,
	>::from_ser(historied_persistence);

	if hash_for_root != block_hash {
		println!("querying not best block, but {:?}", hash_for_root);
	}
	let current_state = management.get_db_state(&hash_for_root).expect("just added");
	println!("current state {:?}", current_state);
	let historied_db = crate::HistoriedDB {
		current_state,
		db: db.clone(),
		do_assert: false,
	};


	let mut root_callback = trie_db::TrieRoot::<HashFor<Block>, _>::default();
	let _state = management.get_db_state(&hash_for_root).expect("just added");
	let iter_kv = historied_db.iter();

	trie_db::trie_visit::<sp_trie::Layout<HashFor<Block>>, _, _, _, _>(iter_kv, &mut root_callback);
	let hash = root_callback.root;
	println!("hash calculated {:?} : {}", hash, now.elapsed().as_millis());

	Ok(())
}



/// Hacky migrate to trigger action on db.
/// Here drop historied state content.
fn delete_historied<Block: BlockT>(db_path: &Path, db_type: DatabaseType) -> sp_blockchain::Result<()> {

	let mut db_config = kvdb_rocksdb::DatabaseConfig::with_columns(crate::utils::NUM_COLUMNS);
   {
		let option = rocksdb::Options::default();
		 let cfs = rocksdb::DB::list_cf(&option, db_path).unwrap();
		 let db = rocksdb::DB::open_cf(&option, db_path, cfs.clone()).unwrap();
		 for cf in cfs {

			 if let Some(col) = db.cf_handle(&cf) {
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.estimate-table-readers-mem"));
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.size-all-mem-tables"));
				println!("{:?}, {:?}", cf, db.property_int_value_cf(col, "rocksdb.cur-size-all-mem-tables"));
			 }
		 }
	}

//	delete_non_canonical::<Block>(db_path, db_type)?;
	let path = db_path.to_str()
		.ok_or_else(|| sp_blockchain::Error::Backend("Invalid database path".into()))?;
	let db = kvdb_rocksdb::Database::open(&db_config, &path)
		.map_err(|err| sp_blockchain::Error::Backend(format!("{}", err)))?;
	println!("db stats : {:?}", db.get_statistics());
	log::warn!("START MIGRATE");
	log::warn!("start clean");
	let mut tx = db.transaction();
	tx.delete(2, b"tree_mgmt/touched_gc");
	tx.delete(2, b"tree_mgmt/current_gc");
	tx.delete(2, b"tree_mgmt/last_index");
	tx.delete(2, b"tree_mgmt/neutral_elt");
	tx.delete(2, b"tree_mgmt/tree_meta");
	tx.delete_prefix(11, &[]);
	tx.delete_prefix(12, &[]);
	tx.delete_prefix(13, &[]);
	tx.delete_prefix(14, &[]);
	for i in 0u8..255 {
		tx.delete_prefix(11, &[i]);
		tx.delete_prefix(12, &[i]);
		tx.delete_prefix(13, &[i]);
		tx.delete_prefix(14, &[i]);
	}
	tx.put(2, b"tree_mgmt/neutral_elt", &[0].encode()); // only for storing Vec<u8>, if changing type, change this.
	db.write(tx).map_err(db_err)?;
	warn!("end clean");
	warn!("END MIGRATE");

	// Can not use crate::meta_keys::BEST_BLOCK on non archive node: using CANNONICAL,
	// TODO EMCH would need to fetch non_cannonical overlay to complete.
	let (tree_root, block_hash) = match db.get(crate::utils::COLUMN_META, crate::meta_keys::FINALIZED_BLOCK) {
		Ok(id) => {
			let id = id.unwrap();
			let id = db.get(crate::columns::HEADER, &id).expect("s").map(|b| Block::Header::decode(&mut &b[..]).ok());
			use sp_runtime::traits::Header;
			let id = id.unwrap().expect("d");
			warn!("Head is {:?}", id);
	/*				let mut hash = <HashFor::<Block> as hash_db::Hasher>::Out::default();
				hash.as_mut().copy_from_slice(id.as_slice());*/
			(id.state_root().clone(), id.hash().clone())
		},
		Err(e) => panic!("no best block is bad sign {:?}", e),
	};


	let db = Arc::new(db);
	let storage = StorageDb::<Block>(db.clone(), PhantomData);
//		let storage: Arc::<dyn sp_state_machine::Storage<HashFor<Block>>> = Arc::new(storage);
/*		let mut root = Block::Hash::default();
		let trie_backend = sp_state_machine::TrieBackend::new(
			storage,
			tree_root,
		);*/
	let trie = sp_trie::trie_types::TrieDB::new(
		&storage,
		&tree_root,
	).expect("build trie");

	let mut iter = sp_trie::TrieDBIterator::new(&trie).expect("titer");
	let historied_persistence = crate::RocksdbStorage(db.clone());
	let mut management = TreeManagement::<
		<HashFor<Block> as hash_db::Hasher>::Out,
		u32,
		u32,
		Vec<u8>,
		crate::TreeManagementPersistence,
	>::from_ser(historied_persistence);
	let state = management.latest_state_fork();
	let test = management.get_db_state_for_fork(&Default::default());
	println!("test: {:?}", test);
	management.append_external_state(block_hash.clone(), &state);
	let state = management.latest_state();
	let mut count_tx = 0;
	let mut count = 0;

	let mut kv_db = crate::HistoriedDBMut {
		current_state: state,
		db: db.clone(),
	};
	let mut tx = kv_db.transaction();
	while let Some(Ok((k, v))) = iter.next() {
		kv_db.unchecked_new_single(k.as_slice(), v, &mut tx);
		count_tx += 1;
		if count_tx == 1000 {
			count += 1;
			warn!("write a thousand {} {:?}", count, &k[..20]);
			kv_db.write_change_set(tx).expect("write_tx");
			tx = kv_db.transaction();
			count_tx = 0;
		}
	}
	kv_db.write_change_set(tx).expect("write_tx last");

	let now = Instant::now();
	let mut iter = sp_trie::TrieDBIterator::new(&trie).expect("titer");
	let mut count = 0;
	while let Some(Ok((_k, _v))) = iter.next() {
		count += 1;
	}
	println!("iter trie state of {} in : {}", count, now.elapsed().as_millis());
	let now = Instant::now();

	let current_state = management.get_db_state(&block_hash).expect("just added");
	let historied_db = crate::HistoriedDB {
		current_state,
		db: db.clone(),
		do_assert: false,
	};
	let mut count = 0;
	for (_k, _v) in historied_db.iter() {
		count += 1;
	}
	println!("iter kvstate {} state in : {}", count, now.elapsed().as_millis());
	let now = Instant::now();


	let mut root_callback = trie_db::TrieRoot::<HashFor<Block>, _>::default();
	let _state = management.get_db_state(&block_hash).expect("just added");
	let iter_kv = historied_db.iter();

	trie_db::trie_visit::<sp_trie::Layout<HashFor<Block>>, _, _, _, _>(iter_kv, &mut root_callback);
	let hash = root_callback.root;
	println!("hash calcuated {:?} : {}", hash, now.elapsed().as_millis());

	Ok(())
}

struct StorageDb<Block>(Arc<kvdb_rocksdb::Database>, PhantomData<Block>);

impl<Block: BlockT> hash_db::HashDBRef<HashFor<Block>, Vec<u8>> for StorageDb<Block> {
	fn contains(&self, key: &<HashFor::<Block> as hash_db::Hasher>::Out, prefix: hash_db::Prefix) -> bool {
		self.get(key, prefix).is_some()
	}

	fn get(&self, key: &<HashFor::<Block> as hash_db::Hasher>::Out, prefix: hash_db::Prefix) -> Option<sp_trie::DBValue> {
		let key = sp_trie::prefixed_key::<HashFor<Block>>(key, prefix);
		self.0.get(crate::columns::STATE, key.as_slice()).expect("bad script")
	}
}


impl<Block: BlockT> sp_state_machine::Storage<HashFor<Block>> for StorageDb<Block> {
	fn get(&self, key: &Block::Hash, prefix: hash_db::Prefix) -> Result<Option<sp_trie::DBValue>, String> {
		let key = sp_trie::prefixed_key::<HashFor<Block>>(key, prefix);
		Ok(self.0.get(crate::columns::STATE_META, key.as_slice()).expect("bad script"))
	}
}


/// Reads current database version from the file at given path.
/// If the file does not exist returns 0.
fn current_version(path: &Path) -> sp_blockchain::Result<u32> {
	let unknown_version_err = || sp_blockchain::Error::Backend("Unknown database version".into());

	match fs::File::open(version_file_path(path)) {
		Err(ref err) if err.kind() == ErrorKind::NotFound => {
			warn!("version file not found");
			Ok(0)
		},
		Err(e) => {
			warn!("version file error: {:?}", e);
			Err(unknown_version_err())
		},
		Ok(mut file) => {
			let mut s = String::new();
			file.read_to_string(&mut s).map_err(|e| {
				warn!("version file error: {:?}", e);
				unknown_version_err()
			})?;
			warn!("version db : {:?}", s);
			u32::from_str_radix(&s, 10).map_err(|_| unknown_version_err())
		},
	}
}

/// Maps database error to client error
fn db_err(err: std::io::Error) -> sp_blockchain::Error {
	sp_blockchain::Error::Backend(format!("{}", err))
}

/// Writes current database version to the file.
/// Creates a new file if the version file does not exist yet.
fn update_version(path: &Path) -> sp_blockchain::Result<()> {
	fs::create_dir_all(path).map_err(db_err)?;
	let mut file = fs::File::create(version_file_path(path)).map_err(db_err)?;
	file.write_all(format!("{}", CURRENT_VERSION).as_bytes()).map_err(db_err)?;
	Ok(())
}

/// Returns the version file path.
fn version_file_path(path: &Path) -> PathBuf {
	let mut file_path = path.to_owned();
	file_path.push(VERSION_FILE_NAME);
	file_path
}

#[cfg(test)]
mod tests {
	use sc_state_db::PruningMode;
	use crate::{DatabaseSettings, DatabaseSettingsSrc};
	use crate::tests::Block;
	use super::*;

	fn create_db(db_path: &Path, version: Option<u32>) {
		if let Some(version) = version {
			fs::create_dir_all(db_path).unwrap();
			let mut file = fs::File::create(version_file_path(db_path)).unwrap();
			file.write_all(format!("{}", version).as_bytes()).unwrap();
		}
	}

	fn open_database(db_path: &Path) -> sp_blockchain::Result<()> {
		crate::utils::open_database::<Block>(&DatabaseSettings {
			state_cache_size: 0,
			state_cache_child_ratio: None,
			pruning: PruningMode::ArchiveAll,
			source: DatabaseSettingsSrc::RocksDb { path: db_path.to_owned(), cache_size: 128 },
			experimental_cache: Default::default(),
		}, DatabaseType::Full).map(|_| ())
	}

	#[test]
	fn downgrade_never_happens() {
		let db_dir = tempfile::TempDir::new().unwrap();
		create_db(db_dir.path(), Some(CURRENT_VERSION + 1));
		assert!(open_database(db_dir.path()).is_err());
	}

	#[test]
	fn open_empty_database_works() {
		let db_dir = tempfile::TempDir::new().unwrap();
		open_database(db_dir.path()).unwrap();
		open_database(db_dir.path()).unwrap();
		assert_eq!(current_version(db_dir.path()).unwrap(), CURRENT_VERSION);
	}
}
