//! Sequence Trie - a trie-like data-structure for storing sequences of values.
//!
//! See the `SequenceTrie` type for documentation.

use std::hash::Hash;
use std::collections::hash_map::{self, HashMap, Entry};
use std::iter::Map;
use std::default::Default;

#[cfg(test)]
mod tests;

/// A `SequenceTrie` is recursively defined as a value and a map containing child Tries.
///
/// Typically, Tries are used to store strings, which can be thought of as lists of `char`s.
/// Generalising this to any key type, a Trie is a data structure storing values for keys
/// which are themselves lists. Let the parts of such a list-key be called "key fragments".
/// In our representation of a Trie, `K` denotes the type of the key fragments.
///
/// The nesting of child Tries creates a tree structure which can be traversed by mapping
/// key fragments onto nodes. The structure is similar to a k-ary tree, except that the children
/// are stored in `HashMap`s, and there is no bound on the number of children a single node may
/// have (effectively k = ∞). In a SequenceTrie with `char` key fragments, the key
/// `['a', 'b', 'c']` might correspond to something like this (warning: not real code).
///
/// ```ignore
/// SequenceTrie {
///     value: Some(0u),
///     children: 'a' => SequenceTrie {
///         value: Some(1u),
///         children: 'b' => SequenceTrie {
///             value: None,
///             children: 'c' => SequenceTrie {
///                 value: Some(3u),
///                 children: Nil
///             }
///         }
///     }
/// }
/// ```
///
/// Values are stored optionally at each node because inserting a value for a list-key only inserts
/// a value for the last fragment of the key. The intermediate prefix nodes are created with value
/// `None` if they do not exist already.
///
/// The above SequenceTrie could be created using the following sequence of operations:
///
/// ```ignore
/// let trie: SequenceTrie<char, uint> = SequenceTrie::new();
/// trie.insert(['a', 'b', 'c'], 3u);
/// trie.insert([], 0u);
/// trie.insert(['a'], 1u);
/// ```
///
/// The order of insertion is never important.
///
/// One interesting thing about Tries is that every key is a *descendant* of the root, which itself
/// has no key fragment. Although this is a rather trivial observation, it means that every key
/// corresponds to a non-empty sequence of prefix nodes in the tree. This observation is the
/// motivation for the `get_prefix_nodes` method, which returns the nodes corresponding to the longest
/// prefix of a given key.
///
/// The empty list key, `[]`, always corresponds to the root node of the Trie.
///
/// # The Sequence Trie Invariant
/// All leaf nodes have non-trivial values (not equal to `None`). This invariant is maintained by
/// the insertion and removal methods and can be relied upon.
#[derive(Debug, Clone)]
pub struct SequenceTrie<K, V> where K: TrieKey {
    /// Node value.
    pub value: Option<V>,

    /// Node children as a hashmap keyed by key fragments.
    pub children: HashMap<K, SequenceTrie<K, V>>
}

/// Aggregate trait for types which can be used to key a `SequenceTrie`.
///
/// This trait is automatically implemented for all types implementing
/// the supertraits.
pub trait TrieKey: PartialEq + Eq + Hash + Clone {}
impl<K> TrieKey for K where K: PartialEq + Eq + Hash + Clone {}

impl<K, V> SequenceTrie<K, V> where K: TrieKey {
    /// Create a new SequenceTrie node with no value and an empty child map.
    pub fn new() -> SequenceTrie<K, V> {
        SequenceTrie {
            value: None,
            children: HashMap::new()
        }
    }

    /// Insert a key and value into the SequenceTrie.
    ///
    /// Returns `true` if the key did not already correspond to a value.
    pub fn insert(&mut self, key: &[K], value: V) -> bool {
        let key_node = key.iter().fold(self, |current_node, fragment| {
            match current_node.children.entry(fragment.clone()) {
                Entry::Vacant(slot) => slot.insert(SequenceTrie::new()),
                Entry::Occupied(slot) => slot.into_mut()
            }
        });
        let is_new_value = match key_node.value {
            Some(_) => false,
            None => true
        };
        key_node.value = Some(value);
        is_new_value
    }

    /// Find a reference to a key's value, if it has one.
    pub fn get(&self, key: &[K]) -> Option<&V> {
        self.get_node(key).and_then(|node| node.value.as_ref())
    }

    /// Find a reference to a key's node, if it has one.
    pub fn get_node(&self, key: &[K]) -> Option<&SequenceTrie<K, V>> {
        // Recursive base case, if the key is empty, return the node.
        let fragment = match key.first() {
            Some(head) => head,
            None => return Some(self)
        };

        // Otherwise, recurse down the tree.
        match self.children.get(fragment) {
            Some(node) => node.get_node(&key[1..]),
            None => None
        }
    }

    /// Find a mutable reference to a key's value, if it has one.
    pub fn get_mut(&mut self, key: &[K]) -> Option<&mut V> {
        self.get_mut_node(key).and_then(|node| node.value.as_mut())
    }

    /// Find a mutable reference to a key's node, if it has one.
    pub fn get_mut_node(&mut self, key: &[K]) -> Option<&mut SequenceTrie<K, V>> {
        // Recursive base case, if the key is empty, return the node.
        let fragment = match key.first() {
            Some(head) => head,
            None => return Some(self)
        };

        // Otherwise, recurse down the tree.
        match self.children.get_mut(fragment) {
            Some(node) => node.get_mut_node(&key[1..]),
            None => None
        }
    }

    /// Find the longest prefix of nodes which match the given key.
    pub fn get_prefix_nodes(&self, key: &[K]) -> Vec<&SequenceTrie<K, V>> {
        let mut node_path = vec![self];

        for fragment in key.iter() {
            match node_path.last().unwrap().children.get(fragment) {
                Some(node) => node_path.push(node),
                None => break
            }
        }
        node_path
    }

    /// Find the value of the nearest ancestor with a non-empty value, if one exists.
    ///
    /// If all ancestors have empty (`None`) values, `None` is returned.
    pub fn get_ancestor(&self, key: &[K]) -> Option<&V> {
        self.get_ancestor_node(key).and_then(|node| node.value.as_ref())
    }

    /// Find the nearest ancestor with a non-empty value, if one exists.
    ///
    /// If all ancestors have empty (`None`) values, `None` is returned.
    pub fn get_ancestor_node(&self, key: &[K]) -> Option<&SequenceTrie<K, V>> {
        let node_path = self.get_prefix_nodes(key);

        for node in node_path.iter().rev() {
            if node.value.is_some() {
                return Some(*node);
            }
        }
        None
    }

    /// Remove the node corresponding to the given key.
    ///
    /// This operation is like the reverse of `insert` in that
    /// it also deletes extraneous nodes on the path from the root.
    ///
    /// If the key node has children, its value is set to `None` and no further
    /// action is taken. If the key node is a leaf, then it and its ancestors with
    /// empty values and no other children are deleted. Deletion proceeds up the tree
    /// from the key node until a node with a non-empty value or children is reached.
    ///
    /// If the key doesn't match a node in the Trie, no action is taken.
    pub fn remove(&mut self, key: &[K]) {
        self.remove_recursive(key);
    }

    /// Recursive remove method that uses the call stack to safely and
    /// efficiently remove a node and its extraneous ancestors.
    ///
    /// Return `true` if the node should be deleted.
    ///
    /// See `remove` above.
    fn remove_recursive(&mut self, key: &[K]) -> bool {
        match key.first() {
            // Base case: Leaf node, no key left to recurse on.
            None => { self.value = None; },

            // Recursive case: Inner node, delete children.
            Some(fragment) => {
                // Find the child entry in the node's hashmap.
                if let Entry::Occupied(mut entry) = self.children.entry(fragment.clone()) {
                    // Work out whether to delete the child by calling remove recursively.
                    let delete_child = entry.get_mut().remove_recursive(&key[1..]);

                    if delete_child {
                        entry.remove();
                    }
                }
                // NB: If the child isn't found, false will be returned.
                // The `self` node is either a leaf, with a non-trivial value, or an
                // inner node (with children).
            }
        }

        // If the node is childless and valueless, mark it for deletion.
        if self.children.is_empty() && self.value.is_none() {
            true
        } else {
            false
        }
    }

    /// Return an iterator over all the key-value pairs in the collection.
    pub fn iter<'a>(&'a self) -> Iter<'a, K, V> {
        Iter {
            root: self,
            root_visited: false,
            key: vec![],
            stack: vec![]
        }
    }

    /// Return an iterator over all the keys in the trie.
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        // First fn coerced to a fn pointer (borrowed from HashMap impl).
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn(KeyValuePair<'a, K, V>) -> Vec<&'a K> = first;

        Keys {
            inner: self.iter().map(first)
        }
    }

    /// Return an iterator over all the values stored in the trie.
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        // Second fn coerced to a fn pointer (borrowed from HashMap impl).
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn(KeyValuePair<'a, K, V>) -> &'a V = second;

        Values {
            inner: self.iter().map(second)
        }
    }
}

/// Iterator over the keys and values of a `SequenceTrie`.
pub struct Iter<'a, K: 'a, V: 'a> where K: TrieKey {
    root: &'a SequenceTrie<K, V>,
    root_visited: bool,
    key: Vec<&'a K>,
    stack: Vec<StackItem<'a, K, V>>
}

/// Vector of key fragment references and values, yielded during iteration.
pub type KeyValuePair<'a, K, V> = (Vec<&'a K>, &'a V);

/// Iterator over the keys of a `SequenceTrie`.
pub struct Keys<'a, K: 'a, V: 'a> where K: TrieKey {
    inner: Map<Iter<'a, K, V>, fn(KeyValuePair<'a, K, V>) -> Vec<&'a K>>
}

/// Iterator over the values of a `SequenceTrie`.
pub struct Values<'a, K: 'a, V: 'a> where K: TrieKey {
    inner: Map<Iter<'a, K, V>, fn(KeyValuePair<'a, K, V>) -> &'a V>
}

/// Information stored on the iteration stack whilst exploring.
struct StackItem<'a, K: 'a, V: 'a> where K: TrieKey {
    child_iter: hash_map::Iter<'a, K, SequenceTrie<K, V>>
}

/// Delayed action type for iteration stack manipulation.
enum IterAction<'a, K: 'a, V: 'a> where K: TrieKey {
    Push(&'a K, &'a SequenceTrie<K, V>),
    Pop
}

impl<'a, K, V> Iterator for Iter<'a, K, V> where K: TrieKey {
    type Item = KeyValuePair<'a, K, V>;

    fn next(&mut self) -> Option<KeyValuePair<'a, K, V>> {
        use IterAction::*;

        // Special handling for the root.
        if !self.root_visited {
            self.root_visited = true;
            self.stack.push(StackItem {
                child_iter: self.root.children.iter()
            });
            if let Some(ref root_val) = self.root.value {
                return Some((vec![], root_val));
            }
        }

        loop {
            let action = match self.stack.last_mut() {
                Some(stack_top) => {
                    match stack_top.child_iter.next() {
                        Some((fragment, child_node)) => Push(fragment, child_node),
                        None => Pop
                    }
                }
                None => return None
            };

            match action {
                Push(fragment, node) => {
                    self.stack.push(StackItem {
                        child_iter: node.children.iter()
                    });
                    self.key.push(fragment);
                    if let Some(ref value) = node.value {
                        return Some((self.key.clone(), value));
                    }
                }
                Pop => {
                    self.key.pop();
                    self.stack.pop();
                }
            }
        }
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> where K: TrieKey {
    type Item = Vec<&'a K>;

    fn next(&mut self) -> Option<Vec<&'a K>> {
        self.inner.next()
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> where K: PartialEq + Eq + Hash + Clone {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.inner.next()
    }
}

impl<K, V> PartialEq for SequenceTrie<K, V> where K: TrieKey, V: PartialEq {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.children == other.children
    }
}

impl<K, V> Eq for SequenceTrie<K, V> where K: TrieKey, V: Eq {}

impl<K, V> Default for SequenceTrie<K, V> where K: TrieKey {
    fn default() -> Self {
        SequenceTrie::new()
    }
}
