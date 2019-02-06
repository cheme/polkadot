// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Substrate CLI library.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

pub use cli::error;
pub mod chain_spec;
mod service;

use tokio::prelude::Future;
use tokio::runtime::Runtime;
pub use cli::{VersionInfo, IntoExit, NoCustom};
use substrate_service::{ServiceFactory, Roles as ServiceRoles};
use std::ops::Deref;
use log::info;

/// The chain specification option.
#[derive(Clone, Debug)]
pub enum ChainSpec {
	/// Whatever the current runtime is, with just Alice as an auth.
	Development,
	/// Whatever the current runtime is, with simple Alice/Bob auths.
	LocalTestnet,
	/// The Charred Cherry testnet.
	CharredCherry,
	/// Whatever the current runtime is with the "global testnet" defaults.
	StagingTestnet,
}

/// Get a chain config from a spec setting.
impl ChainSpec {
	pub(crate) fn load(self) -> Result<chain_spec::ChainSpec, String> {
		Ok(match self {
			ChainSpec::CharredCherry => chain_spec::charred_cherry_config()?,
			ChainSpec::Development => chain_spec::development_config(),
			ChainSpec::LocalTestnet => chain_spec::local_testnet_config(),
			ChainSpec::StagingTestnet => chain_spec::staging_testnet_config(),
		})
	}

	pub(crate) fn from(s: &str) -> Option<Self> {
		match s {
			"dev" => Some(ChainSpec::Development),
			"local" => Some(ChainSpec::LocalTestnet),
			"" | "cherry" | "charred-cherry" => Some(ChainSpec::CharredCherry),
			"staging" => Some(ChainSpec::StagingTestnet),
			_ => None,
		}
	}
}

fn load_spec(id: &str) -> Result<Option<chain_spec::ChainSpec>, String> {
	Ok(match ChainSpec::from(id) {
		Some(spec) => Some(spec.load()?),
		None => None,
	})
}

/// Parse command line arguments into service configuration.
pub fn run<I, T, E>(args: I, exit: E, version: cli::VersionInfo) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	E: IntoExit,
{
	cli::parse_and_execute::<service::Factory, NoCustom, NoCustom, _, _, _, _, _>(
		load_spec, &version, "substrate-node", args, exit,
		|exit, _custom_args, config| {
			info!("{}", version.name);
			info!("  version {}", config.full_version());
			info!("  by Parity Technologies, 2017-2019");
			info!("Chain specification: {}", config.chain_spec.name());
			info!("Node name: {}", config.name);
			info!("Roles: {:?}", config.roles);
			let runtime = Runtime::new().map_err(|e| format!("{:?}", e))?;
			let executor = runtime.executor();
			match config.roles {
				ServiceRoles::LIGHT => run_until_exit(
					runtime,
					service::Factory::new_light(config, executor).map_err(|e| format!("{:?}", e))?,
					exit
				),
				_ => run_until_exit(
					runtime,
					service::Factory::new_full(config, executor).map_err(|e| format!("{:?}", e))?,
					exit
				),
			}.map_err(|e| format!("{:?}", e))
		}
	).map_err(Into::into).map(|_| ())
}

//#[cfg(feature = "fuzzing")]
pub fn init_fuzz<I, T, E>(args: I, exit: E, version: cli::VersionInfo, input: &[u8]) -> error::Result<()> where
	I: IntoIterator<Item = T>,
	T: Into<std::ffi::OsString> + Clone,
	E: IntoExit,
//	C: substrate_service::Components,
{
	cli::parse_and_execute_fuzz::<service::Factory, NoCustom, NoCustom, _, _, _, _, _>(
		load_spec, &version, "substrate-node", args, exit,
		|_exit, _custom_args, config| {
			let runtime = Runtime::new().map_err(|e| format!("{:?}", e))?;
			let executor = runtime.executor();
      let rpc_handle = service::Factory::new_fuzz(config, executor).map_err(|e| format!("{:?}", e))?;
      let mut ix = 0;
      // TODO move those fuzzer logi in fuzzer crate
      let size_name = if let Some(v) = input.get(ix) {
        *v as usize // 256 length only (might be not enough)
      } else {
        return Ok(());
      };
      ix += 1;
      let meth_name = if input.len() > ix + size_name {
        // go for invalid utf8 char :)
        String::from_utf8_lossy(&input[ix..ix+size_name])
      } else { return Ok(()) };
      ix += size_name;
      let params = String::from_utf8_lossy(&input[ix..]); // TODO change that
/*	    let nb_param = if let Some(v) = input.get(ix) {
        (v & 31u8 as usize;// 31 max param is maybe not enough
      } else {
        return Ok(());
      }
      ix += 1;


   TODO help param construct   let nb_param = if let Some(v) = input.get(ix) {
        (v & 31u8 as usize;// TODO allow bigger param this is super biased
      } else {
        return Ok(());
      }

      let mut params = String::new();
      for pix in 0..nb_param {
        let mut is_string = false;
	      let ty_param = if let Some(v) = input.get(ix) {
          ix += 1;
          match v % 16 {
            0 => {
              params += "true, ";
            },
            1 => {
              params += "false, ";
              continue;
            },
            2..8 => {
              // int TODO helpers for correct int ? (still need)
            },
            _ => {
              is_string = true;
              params += "\"";
            }
            // TODO specialize 0x and hex too as it is super common
          }
        } else {
        return Ok(());
        }
  
      }*/

	    let request = r#"{"jsonrpc": "2.0", "method": "#.to_string()
        + &meth_name
        +  r#"params": ["#
        + &params
        + r#"], "id": 1}"#;
      // contains session for pub sub (need to build multiple queries) -> strategie after params helpers
      let meta = Default::default();
      //let meta = substrate_rpc::metadata::Metadata::default();
      let _ = rpc_handle.handle_request_sync(&request, meta); // TODO those meta?? (second param)
      Ok(())
		}
	).map_err(Into::into).map(|_| ())
}

fn run_until_exit<T, C, E>(
	mut runtime: Runtime,
	service: T,
	e: E,
) -> error::Result<()>
	where
	    T: Deref<Target=substrate_service::Service<C>>,
		C: substrate_service::Components,
		E: IntoExit,
{
	let (exit_send, exit) = exit_future::signal();

	let executor = runtime.executor();
	cli::informant::start(&service, exit.clone(), executor.clone());

	let _ = runtime.block_on(e.into_exit());
	exit_send.fire();

	// we eagerly drop the service so that the internal exit future is fired,
	// but we need to keep holding a reference to the global telemetry guard
	let _telemetry = service.telemetry();
	drop(service);

	// TODO [andre]: timeout this future #1318
	let _ = runtime.shutdown_on_idle().wait();

	Ok(())
}
