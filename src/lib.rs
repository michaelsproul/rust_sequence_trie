//! Sequence Trie - a trie-like data-structure for storing sequences of values.
//!
//! See the `SequenceTrie` type for documentation.

use std::hash::Hash;
use std::collections::hash_map::{self, HashMap, Entry};
use std::iter::IntoIterator;
use std::default::Default;
use std::borrow::{Borrow, ToOwned};
use std::mem;
use std::marker::PhantomData;

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
/// have (effectively k = ∞). In a `SequenceTrie` with `char` key fragments, the key
/// `['a', 'b', 'c']` might correspond to something like this:
///
/// ```text
/// SequenceTrie {
///     value: Some(0),
///     children: 'a' => SequenceTrie {
///         value: Some(1),
///         children: 'b' => SequenceTrie {
///             value: None,
///             children: 'c' => SequenceTrie {
///                 value: Some(3),
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
/// The above `SequenceTrie` could be created using the following sequence of operations:
///
/// ```
/// # use sequence_trie::SequenceTrie;
/// let mut trie: SequenceTrie<char, i32> = SequenceTrie::new();
/// trie.insert(&['a', 'b', 'c'], 3);
/// trie.insert(&[], 0);
/// trie.insert(&['a'], 1);
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
pub struct SequenceTrie<K, V>
    where K: TrieKey
{
    /// Node value.
    value: Option<V>,

    /// Node children as a hashmap keyed by key fragments.
    children: HashMap<K, SequenceTrie<K, V>>,
}

/// Aggregate trait for types which can be used to key a `SequenceTrie`.
///
/// This trait is automatically implemented for all types implementing
/// the supertraits.
pub trait TrieKey: 'static + PartialEq + Eq + Hash + Clone {}
impl<K> TrieKey for K where K: 'static + PartialEq + Eq + Hash + Clone {}

impl<K, V> SequenceTrie<K, V>
    where K: TrieKey
{
    /// Creates a new `SequenceTrie` node with no value and an empty child map.
    pub fn new() -> SequenceTrie<K, V> {
        SequenceTrie {
            value: None,
            children: HashMap::new(),
        }
    }

    /// Checks if this node is empty.
    ///
    /// A node is considered empty when it has no value and no children.
    pub fn is_empty(&self) -> bool {
        self.children.is_empty() && self.value.is_none()
    }

    /// Inserts a key and value into the SequenceTrie.
    ///
    /// Returns `None` if the key did not already correspond to a value, otherwise the old value is
    /// returned.
    pub fn insert<'key, I, Q: 'key + ?Sized>(&mut self, key: I, value: V) -> Option<V>
        where I: IntoIterator<Item = &'key Q>,
              Q: ToOwned<Owned = K>,
              K: Borrow<Q>
    {
        self.insert_owned(key.into_iter().map(ToOwned::to_owned), value)
    }

    /// Version of `insert` that takes an owned sequence of key fragments.
    ///
    /// This function is used internally by `insert`.
    pub fn insert_owned<I>(&mut self, key: I, value: V) -> Option<V>
        where I: IntoIterator<Item = K>
    {
        let key_node = key.into_iter().fold(self, |current_node, fragment| {
            current_node.children.entry(fragment).or_insert_with(Self::new)
        });

        mem::replace(&mut key_node.value, Some(value))
    }

    /// Finds a reference to a key's value, if it has one.
    pub fn get<'key, I>(&self, key: I) -> Option<&V>
        where I: IntoIterator<Item = &'key K>
    {
        self.get_node(key).and_then(|node| node.value.as_ref())
    }

    /// Finds a reference to a key's node, if it has one.
    pub fn get_node<'key, I>(&self, key: I) -> Option<&SequenceTrie<K, V>>
        where I: IntoIterator<Item = &'key K>
    {
        let mut current_node = self;

        for fragment in key {
            match current_node.children.get(fragment) {
                Some(node) => current_node = node,
                None => return None,
            }
        }

        Some(current_node)
    }

    /// Finds a mutable reference to a key's value, if it has one.
    pub fn get_mut<'key, I>(&mut self, key: I) -> Option<&mut V>
        where I: IntoIterator<Item = &'key K>
    {
        self.get_node_mut(key).and_then(|node| node.value.as_mut())
    }

    /// Finds a mutable reference to a key's node, if it has one.
    pub fn get_node_mut<'key, I>(&mut self, key: I) -> Option<&mut SequenceTrie<K, V>>
        where I: IntoIterator<Item = &'key K>
    {
        let mut current_node = Some(self);

        for fragment in key {
            match current_node.and_then(|node| node.children.get_mut(fragment)) {
                Some(node) => current_node = Some(node),
                None => return None,
            }
        }

        current_node
    }

    /// Finds the longest prefix of nodes which match the given key.
    pub fn get_prefix_nodes<'key, I>(&self, key: I) -> Vec<&SequenceTrie<K, V>>
        where I: 'key + IntoIterator<Item = &'key K>
    {
        self.prefix_iter(key).collect()
    }

    /// Finds the value of the nearest ancestor with a non-empty value, if one exists.
    ///
    /// If all ancestors have empty (`None`) values, `None` is returned.
    pub fn get_ancestor<'key, I>(&self, key: I) -> Option<&V>
        where I: 'key + IntoIterator<Item = &'key K>
    {
        self.get_ancestor_node(key).and_then(|node| node.value.as_ref())
    }

    /// Finds the nearest ancestor with a non-empty value, if one exists.
    ///
    /// If all ancestors have empty (`None`) values, `None` is returned.
    pub fn get_ancestor_node<'key, I>(&self, key: I) -> Option<&SequenceTrie<K, V>>
        where I: 'key + IntoIterator<Item = &'key K>
    {
        self.prefix_iter(key)
            .filter(|node| node.value.is_some())
            .last()
    }

    /// Removes the node corresponding to the given key.
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
    pub fn remove<'key, I>(&mut self, key: I)
        where I: IntoIterator<Item = &'key K>
    {
        self.remove_recursive(key);
    }

    /// Recursive remove method that uses the call stack to safely and
    /// efficiently remove a node and its extraneous ancestors.
    ///
    /// Return `true` if the node should be deleted.
    ///
    /// See `remove` above.
    fn remove_recursive<'key, I>(&mut self, key: I) -> bool
        where I: IntoIterator<Item = &'key K>
    {
        let mut fragments = key.into_iter();
        match fragments.next() {
            // Base case: Leaf node, no key left to recurse on.
            None => {
                self.value = None;
            }

            // Recursive case: Inner node, delete children.
            Some(fragment) => {
                // Find the child entry in the node's hashmap.
                if let Entry::Occupied(mut entry) = self.children.entry(fragment.clone()) {
                    // Work out whether to delete the child by calling remove recursively.
                    let delete_child = entry.get_mut().remove_recursive(fragments);

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
        self.is_empty()
    }

    /// Returns an iterator over all the key-value pairs in the collection.
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            root: self,
            root_visited: false,
            key: vec![],
            stack: vec![],
        }
    }

    /// Returns an iterator over all the keys in the trie.
    pub fn keys(&self) -> Keys<K, V> {
        Keys { inner: self.iter() }
    }

    /// Returns an iterator over all the values stored in the trie.
    pub fn values(&self) -> Values<K, V> {
        Values { inner: self.iter() }
    }

    /// Returns an iterator over the longest prefix of nodes which match the given key.
    pub fn prefix_iter<'trie, 'key, I>(&'trie self,
                                       key: I)
                                       -> PrefixIter<'trie, 'key, K, V, I::IntoIter>
        where I: 'key + IntoIterator<Item = &'key K>
    {
        PrefixIter {
            next_node: Some(self),
            fragments: key.into_iter(),
            _phantom: PhantomData,
        }
    }
}

/// Iterator over the keys and values of a `SequenceTrie`.
pub struct Iter<'a, K: 'a, V: 'a>
    where K: TrieKey
{
    root: &'a SequenceTrie<K, V>,
    root_visited: bool,
    key: Vec<&'a K>,
    stack: Vec<StackItem<'a, K, V>>,
}

/// Vector of key fragment references and values, yielded during iteration.
pub type KeyValuePair<'a, K, V> = (Vec<&'a K>, &'a V);

/// Iterator over the keys of a `SequenceTrie`.
pub struct Keys<'a, K: 'a, V: 'a>
    where K: TrieKey
{
    inner: Iter<'a, K, V>,
}

/// Iterator over the values of a `SequenceTrie`.
pub struct Values<'a, K: 'a, V: 'a>
    where K: TrieKey
{
    inner: Iter<'a, K, V>,
}

/// Information stored on the iteration stack whilst exploring.
struct StackItem<'a, K: 'a, V: 'a>
    where K: TrieKey
{
    child_iter: hash_map::Iter<'a, K, SequenceTrie<K, V>>,
}

/// Delayed action type for iteration stack manipulation.
enum IterAction<'a, K: 'a, V: 'a>
    where K: TrieKey
{
    Push(&'a K, &'a SequenceTrie<K, V>),
    Pop,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
    where K: TrieKey
{
    type Item = KeyValuePair<'a, K, V>;

    fn next(&mut self) -> Option<KeyValuePair<'a, K, V>> {
        use IterAction::*;

        // Special handling for the root.
        if !self.root_visited {
            self.root_visited = true;
            self.stack.push(StackItem { child_iter: self.root.children.iter() });
            if let Some(ref root_val) = self.root.value {
                return Some((vec![], root_val));
            }
        }

        loop {
            let action = match self.stack.last_mut() {
                Some(stack_top) => {
                    match stack_top.child_iter.next() {
                        Some((fragment, child_node)) => Push(fragment, child_node),
                        None => Pop,
                    }
                }
                None => return None,
            };

            match action {
                Push(fragment, node) => {
                    self.stack.push(StackItem { child_iter: node.children.iter() });
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

impl<'a, K, V> Iterator for Keys<'a, K, V>
    where K: TrieKey
{
    type Item = Vec<&'a K>;

    fn next(&mut self) -> Option<Vec<&'a K>> {
        self.inner.next().map(|(k, _)| k)
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V>
    where K: TrieKey
{
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }
}

impl<K, V> PartialEq for SequenceTrie<K, V>
    where K: TrieKey,
          V: PartialEq
{
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.children == other.children
    }
}

impl<K, V> Eq for SequenceTrie<K, V>
    where K: TrieKey,
          V: Eq
{}

impl<K, V> Default for SequenceTrie<K, V>
    where K: TrieKey
{
    fn default() -> Self {
        SequenceTrie::new()
    }
}

/// Iterator over the longest prefix of nodes which matches a key.
pub struct PrefixIter<'trie, 'key, K, V, I>
    where K: 'trie + TrieKey,
          V: 'trie,
          I: 'key + Iterator<Item = &'key K>
{
    next_node: Option<&'trie SequenceTrie<K, V>>,
    fragments: I,
    _phantom: PhantomData<&'key I>,
}

impl<'trie, 'key, K, V, I> Iterator for PrefixIter<'trie, 'key, K, V, I>
    where K: 'trie + TrieKey,
          V: 'trie,
          I: 'key + Iterator<Item = &'key K>
{
    type Item = &'trie SequenceTrie<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(current_node) = self.next_node.take() {
            if let Some(fragment) = self.fragments.next() {
                self.next_node = current_node.children.get(fragment)
            }

            return Some(current_node);
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let lower = if self.next_node.is_some() {
            1
        } else {
            0
        };

        (lower, self.fragments.size_hint().1)
    }
}
