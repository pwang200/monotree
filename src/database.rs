//! A module for implementing database supporting `monotree`.
use crate::*;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

use utils::*;

/// A database using `HashMap`.
#[derive(Serialize, Deserialize, Debug)]
pub struct MemoryDB {
    db: HashMap<Hash, Vec<u8>>,
}

impl MemoryDB {
    pub fn new() -> Self {
        MemoryDB { db: HashMap::new() }
    }

    pub fn get(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        match self.db.get(key) {
            Some(v) => Ok(Some(v.to_owned())),
            None => Ok(None),
        }
    }

    pub fn put(&mut self, key: &[u8], value: Vec<u8>) -> Result<()> {
        self.db.insert(slice_to_hash(key), value);
        Ok(())
    }

    pub fn delete(&mut self, key: &[u8]) -> Result<()> {
        self.db.remove(key);
        Ok(())
    }

    pub fn init_batch(&mut self) -> Result<()> {
        Ok(())
    }

    pub fn finish_batch(&mut self) -> Result<()> {
        Ok(())
    }
}
