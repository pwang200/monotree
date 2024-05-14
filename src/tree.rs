//! A module implementing `monotree`.
use crate::utils::*;
use crate::*;
use serde::{Serialize, Deserialize};
use crate::hasher::Hasher;

/// A structure for `monotree`.
#[derive(Serialize, Deserialize, Debug)]
pub struct Monotree {
    db: MemoryDB,
}

impl Default for Monotree {
    fn default() -> Self {
        Self::new()
    }
}

impl Monotree
{
    pub fn new() -> Self {
        let db = MemoryDB::new();
        Monotree { db}
    }

    /// Insert key-leaf entry into the `monotree`. Returns a new root hash.
    pub fn insert(&mut self, root: Option<&Hash>, key: &Hash, leaf: &Hash) -> Result<Option<Hash>> {
        match root {
            None => {
                let (hash, bits) = (leaf, Bits::new(key));
                self.put_node(Node::new(Some(Unit { hash, bits }), None))
            }
            Some(root) => self.put(root, Bits::new(key), leaf),
        }
    }

    fn put_node(&mut self, node: Node) -> Result<Option<Hash>> {
        let hasher = SimpleHash::new();
        let bytes = node.to_bytes()?;
        let hash = hasher.digest(&bytes);
        self.db.put(&hash, bytes)?;
        Ok(Some(hash))
    }

    /// Recursively insert a bytes (in forms of Bits) and a leaf into the tree.  
    ///
    /// Optimization in `monotree` is mainly to compress the path as much as possible
    /// while reducing the number of db accesses using the most intuitive model.
    /// As a result, compared to the standard Sparse Merkle Tree,
    /// this reduces the number of DB accesses from `N` to `log2(N)` in both reads and writes.
    ///
    /// Whenever invoked a `put()` call, at least, more than one `put_node()` called,
    /// which triggers a single hash digest + a single DB write.  
    /// Compressing the path recudes the number of `put()` calls, which yields
    /// reducing the number of hash function calls as well as the number of DB writes.  
    ///
    /// There are four modes when putting the entries.
    /// And each of them is processed in a (recursive) `put()` call.
    /// The number in parenthesis refers to the minimum of DB access and hash fn call required.
    ///
    /// * set-aside (1)
    ///     putting the leaf to the next node in the current depth.
    /// * replacement (1)
    ///     replacement the existing node on the path with the new leaf.
    /// * consume & pass-over (2+)
    ///     consuming the path on the way, then pass the rest of work to their child node.
    /// * split-node (2)
    ///     immediately split node into two with the longest common prefix,
    ///     then wind the recursive stack from there returning resulting hashes.
    fn put(&mut self, root: &[u8], bits: Bits, leaf: &[u8]) -> Result<Option<Hash>> {
        let bytes = self.db.get(root)?.expect("bytes");
        let (lc, rc) = Node::cells_from_bytes(&bytes, bits.first())?;
        let unit = lc.as_ref().expect("put(): left-unit");
        let n = Bits::len_common_bits(&unit.bits, &bits);
        match n {
            n if n == 0 => self.put_node(Node::new(lc, Some(Unit { hash: leaf, bits }))),
            n if n == bits.len() => self.put_node(Node::new(Some(Unit { hash: leaf, bits }), rc)),
            n if n == unit.bits.len() => {
                let hash = &self
                    .put(unit.hash, bits.shift(n, false), leaf)?
                    .expect("put(): hash");
                let unit = unit.to_owned();
                self.put_node(Node::new(Some(Unit { hash, ..unit }), rc))
            }
            _ => {
                let bits = bits.shift(n, false);
                let ru = Unit { hash: leaf, bits };

                let (cloned, unit) = (unit.bits.clone(), unit.to_owned());
                let (hash, bits) = (unit.hash, unit.bits.shift(n, false));
                let lu = Unit { hash, bits };

                let hash = &self
                    .put_node(Node::new(Some(lu), Some(ru)))?
                    .expect("put(): hash");
                let bits = cloned.shift(n, true);
                self.put_node(Node::new(Some(Unit { hash, bits }), rc))
            }
        }
    }

    /// Get a leaf hash for the given root and key.
    pub fn get(&mut self, root: Option<&Hash>, key: &Hash) -> Result<Option<Hash>> {
        match root {
            None => Ok(None),
            Some(root) => self.find_key(root, Bits::new(key)),
        }
    }

    fn find_key(&mut self, root: &[u8], bits: Bits) -> Result<Option<Hash>> {
        let bytes = self.db.get(root)?.expect("bytes");
        let (cell, _) = Node::cells_from_bytes(&bytes, bits.first())?;
        let unit = cell.as_ref().expect("find_key(): left-unit");
        let n = Bits::len_common_bits(&unit.bits, &bits);
        match n {
            n if n == bits.len() => Ok(Some(slice_to_hash(unit.hash))),
            n if n == unit.bits.len() => self.find_key(&unit.hash, bits.shift(n, false)),
            _ => Ok(None),
        }
    }

    /// Remove the given key and its corresponding leaf from the tree. Returns a new root hash.
    pub fn remove(&mut self, root: Option<&Hash>, key: &[u8]) -> Result<Option<Hash>> {
        match root {
            None => Ok(None),
            Some(root) => self.delete_key(root, Bits::new(key)),
        }
    }

    fn delete_key(&mut self, root: &[u8], bits: Bits) -> Result<Option<Hash>> {
        let bytes = self.db.get(root)?.expect("bytes");
        let (lc, rc) = Node::cells_from_bytes(&bytes, bits.first())?;
        let unit = lc.as_ref().expect("delete_key(): left-unit");
        let n = Bits::len_common_bits(&unit.bits, &bits);
        match n {
            n if n == bits.len() => match rc {
                Some(_) => self.put_node(Node::new(None, rc)),
                None => Ok(None),
            },
            n if n == unit.bits.len() => {
                let hash = self.delete_key(&unit.hash, bits.shift(n, false))?;
                match (hash, &rc) {
                    (None, None) => Ok(None),
                    (None, Some(_)) => self.put_node(Node::new(None, rc)),
                    (Some(ref hash), _) => {
                        let unit = unit.to_owned();
                        let lc = Some(Unit { hash, ..unit });
                        self.put_node(Node::new(lc, rc))
                    }
                }
            }
            _ => Ok(None),
        }
    }

    /// This method is intended to use the `insert()` method in batch mode.
    pub fn inserts(
        &mut self,
        root: Option<&Hash>,
        keys: &[Hash],
        leaves: &[Hash],
    ) -> Result<Option<Hash>> {
        let indices = get_sorted_indices(keys, false);
        self.db.init_batch()?;
        let mut root = root.cloned();
        for i in indices.iter() {
            root = self.insert(root.as_ref(), &keys[*i], &leaves[*i])?;
        }
        self.db.finish_batch()?;
        Ok(root)
    }

    /// This method is intended to use the `get()` method in batch mode.
    pub fn gets(&mut self, root: Option<&Hash>, keys: &[Hash]) -> Result<Vec<Option<Hash>>> {
        let mut leaves: Vec<Option<Hash>> = Vec::new();
        for key in keys.iter() {
            leaves.push(self.get(root, key)?);
        }
        Ok(leaves)
    }

    /// This method is intended to use the `remove()` method in batch mode.
    pub fn removes(&mut self, root: Option<&Hash>, keys: &[Hash]) -> Result<Option<Hash>> {
        let indices = get_sorted_indices(keys, false);
        let mut root = root.cloned();
        self.db.init_batch()?;
        for i in indices.iter() {
            root = self.remove(root.as_ref(), &keys[*i])?;
        }
        self.db.finish_batch()?;
        Ok(root)
    }

    /// Generate a Merkle proof for the given root and key.
    pub fn get_merkle_proof(&mut self, root: Option<&Hash>, key: &[u8]) -> Result<Option<Proof>> {
        let mut proof: Proof = Vec::new();
        match root {
            None => Ok(None),
            Some(root) => self.gen_proof(root, Bits::new(key), &mut proof),
        }
    }

    fn gen_proof(&mut self, root: &[u8], bits: Bits, proof: &mut Proof) -> Result<Option<Proof>> {
        let bytes = self.db.get(root)?.expect("bytes");
        let (cell, _) = Node::cells_from_bytes(&bytes, bits.first())?;
        let unit = cell.as_ref().expect("gen_proof(): left-unit");
        let n = Bits::len_common_bits(&unit.bits, &bits);
        match n {
            n if n == bits.len() => {
                proof.push(self.encode_proof(&bytes, bits.first())?);
                Ok(Some(proof.to_owned()))
            }
            n if n == unit.bits.len() => {
                proof.push(self.encode_proof(&bytes, bits.first())?);
                self.gen_proof(unit.hash, bits.shift(n, false), proof)
            }
            _ => Ok(None),
        }
    }

    fn encode_proof(&self, bytes: &[u8], right: bool) -> Result<(bool, Vec<u8>)> {
        match Node::from_bytes(bytes)? {
            Node::Soft(_) => Ok((false, bytes[HASH_LEN..].to_vec())),
            Node::Hard(_, _) => {
                if right {
                    Ok((
                        true,
                        [&bytes[..bytes.len() - HASH_LEN - 1], &[0x01]].concat(),
                    ))
                } else {
                    Ok((false, bytes[HASH_LEN..].to_vec()))
                }
            }
        }
    }
}

/// Verify a Merkle proof with the given root, leaf and hasher if the proof is valid or not.
///
/// Be aware of that it fails if not provided a suitable hasher used in the tree
/// This generic fn must be independantly called upon request, not a member of Monotree.
pub fn verify_proof(
    //hasher: &H,
    root: Option<&Hash>,
    leaf: &Hash,
    proof: Option<&Proof>,
) -> bool {
    let hasher = SimpleHash::new();
    match proof {
        None => false,
        Some(proof) => {
            let mut hash = leaf.to_owned();
            proof.iter().rev().for_each(|(right, cut)| {
                if *right {
                    let l = cut.len();
                    let o = [&cut[..l - 1], &hash[..], &cut[l - 1..]].concat();
                    hash = hasher.digest(&o);
                } else {
                    let o = [&hash[..], &cut[..]].concat();
                    hash = hasher.digest(&o);
                }
            });
            root.expect("verify_proof(): root") == &hash
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct FakeRandom{
        d : u8,
    }

    impl FakeRandom {
        pub fn new() ->FakeRandom{
            FakeRandom{d:0u8}
        }

        pub fn random_byte(&mut self) -> u8 {
            self.d = self.d * 13 % 251;
            self.d
        }

        pub fn random_bytes(&mut self, n: usize) -> Vec<u8> {
            (0..n).map(|_| self.random_byte()).collect()
        }

        pub fn random_hash(&mut self) -> Hash {
            slice_to_hash(&self.random_bytes(HASH_LEN))
        }

        pub fn random_hashes(&mut self, n: usize) -> Vec<Hash> {
            (0..n).map(|_| self.random_hash()).collect()
        }
    }

    /// Get a fixed lenght byte-array or `Hash` from slice.
    pub fn slice_to_hash(slice: &[u8]) -> Hash {
        let mut hash = [0x00; HASH_LEN];
        hash.copy_from_slice(slice);
        hash
    }

    #[test]
    fn put_get_proof_work() {
        let mut tree = Monotree::default();
        let mut fr = FakeRandom::new();

        // put and get
        let root = None;
        let n = 33usize;
        let keys = fr.random_hashes(n);
        let leaves = fr.random_hashes(n);
        let root = tree.inserts(root.as_ref(), &keys, &leaves).unwrap();
        let get_results = tree.gets(root.as_ref(), &keys).unwrap();
        let rl = get_results.len();
        assert_eq!(rl, n);
        let get_third = get_results[n/3].unwrap();
        assert!(!get_results.is_empty());
        assert_eq!(leaves[n/3], get_third);
        let key = keys[n/2];
        let leaf = match tree.get(root.as_ref(), &key).unwrap() {
            Some(l) => l,
            _ => fr.random_hash(),
        };
        assert_eq!(leaves[n/2], leaf);

        // Merkle proof
        let proof = tree.get_merkle_proof(root.as_ref(), &key).unwrap();
        // let hasher = SimpleHash::new();
        // assert!(verify_proof(&hasher, root.as_ref(), &leaf, proof.as_ref()));
        assert!(verify_proof(root.as_ref(), &leaf, proof.as_ref()));
    }

    #[test]
    fn serde_works() {
        let mut tree = Monotree::default();
        let mut fr = FakeRandom::new();

        // put
        let root = None;
        let n = 57usize;
        let keys = fr.random_hashes(n);
        let leaves = fr.random_hashes(n);
        let root = tree.inserts(root.as_ref(), &keys, &leaves).unwrap();

        // serialization
        let encoded: Vec<u8> = bincode::serialize(&tree).unwrap();
        let mut decoded: Monotree = bincode::deserialize(&encoded[..]).unwrap();
        let get_results = decoded.gets(root.as_ref(), &keys).unwrap();

        for idx in 0..n {
            let nr = get_results[idx].unwrap();
            assert_eq!(nr, leaves[idx]);
        }

        // proof still works
        let key = keys[n/2];
        let leaf = match tree.get(root.as_ref(), &key).unwrap() {
            Some(l) => l,
            _ => fr.random_hash(),
        };
        assert_eq!(leaves[n/2], leaf);

        // Merkle proof
        let proof = tree.get_merkle_proof(root.as_ref(), &key).unwrap();
        assert!(verify_proof( root.as_ref(), &leaf, proof.as_ref()));
    }
}
