//! A module for implementing hash functions supporting `monotree`.
use crate::utils::*;
use crate::*;
use digest::Digest;

/// A trait defining hashers used for `monotree`
pub trait Hasher {
    fn new() -> Self;
    fn digest(&self, bytes: &[u8]) -> Hash;
}

#[derive(Clone, Debug)]
/// A hasher using `SHA2` hash function
pub struct Sha2;
impl Hasher for Sha2 {
    fn new() -> Self {
        Sha2
    }

    /// Currently supports 256-bit or 32-byte only.
    fn digest(&self, bytes: &[u8]) -> Hash {
        let mut hasher = sha2::Sha256::new();
        hasher.input(bytes);
        let hash = hasher.result();
        slice_to_hash(hash.as_slice())
    }
}
