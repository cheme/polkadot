#![no_main]
use libfuzzer_sys::fuzz_target;

use radix_tree::tests::test_256::fuzz_insert_remove; 
fuzz_target!(|data: &[u8]| {
	fuzz_insert_remove(data, false);
});
