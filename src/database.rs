//! A module for implementing database supporting `monotree`.
use crate::*;
use std::collections::HashMap;

use utils::*;

/// A trait defining databases used for `monotree`.
pub trait Database {
    fn new(dbpath: &str) -> Self;
    fn get(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>>;
    fn put(&mut self, key: &[u8], value: Vec<u8>) -> Result<()>;
    fn delete(&mut self, key: &[u8]) -> Result<()>;
    fn init_batch(&mut self) -> Result<()>;
    fn finish_batch(&mut self) -> Result<()>;
}

/// A database using `HashMap`.
pub struct MemoryDB {
    db: HashMap<Hash, Vec<u8>>,
}

impl Database for MemoryDB {
    fn new(_dbname: &str) -> Self {
        MemoryDB { db: HashMap::new() }
    }

    fn get(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        match self.db.get(key) {
            Some(v) => Ok(Some(v.to_owned())),
            None => Ok(None),
        }
    }

    fn put(&mut self, key: &[u8], value: Vec<u8>) -> Result<()> {
        self.db.insert(slice_to_hash(key), value);
        Ok(())
    }

    fn delete(&mut self, key: &[u8]) -> Result<()> {
        self.db.remove(key);
        Ok(())
    }

    fn init_batch(&mut self) -> Result<()> {
        Ok(())
    }

    fn finish_batch(&mut self) -> Result<()> {
        Ok(())
    }
}
