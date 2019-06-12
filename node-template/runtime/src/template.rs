/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references


/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/srml/example/src/lib.rs

// Encoding library
use parity_codec::Encode;

// Enables access to store a value in runtime storage
// Imports the `Result` type that is returned from runtime functions
// Imports the `decl_module!` and `decl_storage!` macros
use support::{StorageValue, dispatch::Result, decl_module, decl_storage, decl_event};

// Traits used for interacting with Substrate's Balances module
// `Currency` gives you access to interact with the on-chain currency
// `WithdrawReason` and `ExistenceRequirement` are enums for balance functions
use support::traits::{Currency, WithdrawReason, ExistenceRequirement};

// These are traits which define behavior around math and hashing
use runtime_primitives::traits::{Zero, Hash, Saturating};

// Enables us to verify an call to our module is signed by a user account
use system::ensure_signed;

/// The module's configuration trait.
pub trait Trait: balances::Trait {
	// TODO: Add other types and constants required configure this module.

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

// This module's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as TemplateModule {
		// Just a dummy storage item.
		// Here we are declaring a StorageValue, `Something` as a Option<u32>
		// `get(something)` is the default getter which returns either the stored `u32` or `None` if nothing stored
		Something get(something): Option<u32>;
    Payment get(payment): Option<T::Balance>;
    Pot get(pot): T::Balance;
    Nonce get(nonce): u64;
	}
}

// The module's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		// Initializing events
		// this is needed only if you are using events in your module
		fn deposit_event<T>() = default;

		// Just a dummy entry point.
		// function that can be called by the external world as an extrinsics call
		// takes a parameter of the type `AccountId`, stores it and emits an event
		pub fn do_something(origin, something: u32) -> Result {
			// TODO: You only need this if you want to check it was signed.
			let who = ensure_signed(origin)?;

			// TODO: Code to execute when something calls this.
			// For example: the following line stores the passed in u32 in the storage
			<Something<T>>::put(something);

			// here we are raising the Something event
			Self::deposit_event(RawEvent::SomethingStored(something, who));
			Ok(())
		}


    fn set_payment(origin, value: T::Balance) -> Result {

      // Ensure that the function call is a signed message (i.e. a transaction)
      let _ = ensure_signed(origin)?;
      // If `payment` is not initialized with some value
      if Self::payment().is_none() {
        // Set the value of `payment`
        <Payment<T>>::put(value);
        // Initialize the `pot` with the same value
        <Pot<T>>::put(value);
      }
      // Return Ok(()) when everything happens successfully
      Ok(())
    }
    
    fn play(origin) -> Result {
      // Logic for playing the game
      // Ensure that the function call is a signed message (i.e. a transaction)
	// Additionally, derive the sender address from the signed message
	let sender = ensure_signed(origin)?;
	// Ensure that `payment` storage item has been set
	let payment = Self::payment().ok_or("Must have payment amount set")?;
	// Read our storage values, and place them in memory variables
	let mut nonce = Self::nonce();
	let mut pot = Self::pot();

	// Try to withdraw the payment from the account, making sure that it will not kill the account
	let _ = <balances::Module<T> as Currency<_>>::withdraw(&sender, payment, WithdrawReason::Reserve, ExistenceRequirement::KeepAlive)?;

	// Generate a random hash between 0-255 using a csRNG algorithm
	if (<system::Module<T>>::random_seed(), &sender, nonce)
		.using_encoded(<T as system::Trait>::Hashing::hash)
		.using_encoded(|e| e[0] < 128)
	{
		// If the user won the coin flip, deposit the pot winnings; cannot fail
		let _ = <balances::Module<T> as Currency<_>>::deposit_into_existing(&sender, pot)
		.expect("`sender` must exist since a transaction is being made and withdraw will keep alive; qed.");
		// Reduce the pot to zero
		pot = Zero::zero();
	}

	// No matter the outcome, increase the pot by the payment amount
	pot = pot.saturating_add(payment);
	// Increment the nonce
	nonce = nonce.wrapping_add(1);

	// Store the updated values for our module
	<Pot<T>>::put(pot);
	<Nonce<T>>::put(nonce);

	// Return Ok(()) when everything happens successfully
	Ok(())
    }
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as system::Trait>::AccountId {
		// Just a dummy event.
		// Event `Something` is declared with a parameter of the type `u32` and `AccountId`
		// To emit this event, we call the deposit funtion, from our runtime funtions
		SomethingStored(u32, AccountId),
	}
);

/// tests for this module
#[cfg(test)]
mod tests {
	use super::*;

	use runtime_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	use support::{impl_outer_origin, assert_ok};
	use runtime_primitives::{
		BuildStorage,
		traits::{BlakeTwo256, IdentityLookup},
		testing::{Digest, DigestItem, Header}
	};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type Log = DigestItem;
	}
	impl Trait for Test {
		type Event = ();
	}
	type TemplateModule = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		system::GenesisConfig::<Test>::default().build_storage().unwrap().0.into()
	}

	#[test]
	fn it_works_for_default_value() {
		with_externalities(&mut new_test_ext(), || {
			// Just a dummy test for the dummy funtion `do_something`
			// calling the `do_something` function with a value 42
			assert_ok!(TemplateModule::do_something(Origin::signed(1), 42));
			// asserting that the stored value is equal to what we stored
			assert_eq!(TemplateModule::something(), Some(42));
		});
	}
}
