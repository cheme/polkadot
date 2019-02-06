
use honggfuzz::fuzz;

fn main() {
  loop {
    fuzz!(|data: &[u8]| {
      substrate_fuzz::fuzz(data);
    });
  }
}
