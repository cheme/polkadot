

use node_cli::{
  init_fuzz,
  VersionInfo,
};

struct Exit;
impl node_cli::IntoExit for Exit {
	type Exit = futures::future::Ok<(),()>;
	fn into_exit(self) -> Self::Exit {
    futures::future::ok(())
	}
}

pub fn fuzz(input: &[u8]) { // -> node_cli::error::Result<()> {
	let version = VersionInfo {
		name: "Substrate Node",
		commit: "dummy",
		version: env!("CARGO_PKG_VERSION"),
		executable_name: "substrate",
		author: "Parity Technologies <admin@parity.io>",
		description: "Generic substrate node",
		support_url: "https://github.com/paritytech/substrate/issues/new",
	};
  let args = vec![String::from("--dev")];
  // TODO clean path and dest
	let _ = init_fuzz(args, Exit, version, input);
}
