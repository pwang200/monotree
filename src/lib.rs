
/// Size of fixed length byte-array from a `Hasher`. Equivalent to `key` length of `monotree`.
pub const HASH_LEN: usize = 32;

/// A type representing length of `Bits`.
pub type BitsLen = u16;

/// A `Result` type redefined for error handling. The same as `std::result::Result<T, Errors>`.
pub type Result<T> = core::result::Result<T, Errors>;

/// A type indicating fixed length byte-array. This has the length of `HASH_LEN`.
pub type Hash = [u8; HASH_LEN];

/// A type representing _Merkle proof_.
pub type Proof = Vec<(bool, Vec<u8>)>;

/// A type indicating database selected by default.
pub type DefaultDatabase = database::MemoryDB;

/// A type indicating hasher selected by default.
pub type DefaultHasher = hasher::Sha2;

pub use self::bits::Bits;
pub use self::database::Database;
pub use self::hasher::Hasher;
pub use self::node::{Cell, Node, Unit};
pub use self::tree::{verify_proof, Monotree};

#[derive(Debug)]
/// An `Error` type defiend for handling general errors.
pub struct Errors {
    details: String,
}

impl Errors {
    pub fn new(msg: &str) -> Errors {
        Errors {
            details: msg.to_string(),
        }
    }
}

impl core::fmt::Display for Errors {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.details)
    }
}
//
// #[feature(error_in_core)]
// impl core::error::Error for Errors {
//     fn description(&self) -> &str {
//         &self.details
//     }
// }

#[macro_use]
pub mod utils;
pub mod bits;
pub mod database;
pub mod hasher;
pub mod node;
pub mod tree;
