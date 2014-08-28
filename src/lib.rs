//! Generic Trie implementation.
//!
//! Useful for hierarchical data.

use std::hash::Hash;
use std::collections::hashmap::HashMap;

/// A Trie is recursively defined as a value and a map containing child Tries.
///
/// Typically, Tries are used to store strings, which can be thought of as lists of `char`s.
/// Generalising this to any key type, a Trie is a data structure storing values for keys
/// which are themselves lists. Let the parts of such a list-key be called "key fragments".
/// In our representation of a Trie, `K` denotes the type of the key fragments.
///
/// The nesting of child Tries creates a tree structure which can be traversed by mapping
/// key fragments onto nodes. In a Trie with `char` key fragments, the key `['a', 'b', 'c']`
/// might correspond to something like this (warning: not real code).
///
/// ```ignore
/// Trie {
///     value: Some(0u),
///     children: 'a' => Trie {
///         value: Some(1u),
///         children: 'b' => Trie {
///             value: None,
///             children: 'c' => Trie {
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
/// The above Trie could be created using the following sequence of operations:
///
/// ```ignore
/// let trie: Trie<char, uint> = Trie::new();
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
/// motivation for the `find_prefix_nodes` method, which returns the nodes corresponding to the longest
/// prefix of a given key.
///
/// The empty list key, `[]`, always corresponds to the root node of the Trie.
pub struct Trie<K, V> {
    /// Node value.
    pub value: Option<V>,

    /// Node children as a hashmap keyed by key fragments.
    pub children: HashMap<K, Trie<K, V>>
}

impl<K, V> Trie<K, V> where K: PartialEq + Eq + Hash + Clone {
    /// Create a new Trie node with no value and an empty child map.
    pub fn new() -> Trie<K, V> {
        Trie {
            value: None,
            children: HashMap::new()
        }
    }

    /// Insert a key and value into the Trie.
    ///
    /// Returns `true` if the key did not already correspond to a value.
    pub fn insert(&mut self, key: &[K], value: V) -> bool {
        let key_node = key.iter().fold(self, |current_node, fragment| {
            current_node.children.find_or_insert(fragment.clone(), Trie::new())
        });
        let is_new_value = match key_node.value {
            Some(_) => false,
            None => true
        };
        key_node.value = Some(value);
        is_new_value
    }

    /// Find a reference to a key's value, if it has one.
    pub fn find(&self, key: &[K]) -> Option<&V> {
        // Recursive base case, if the key is empty, return the node's value.
        let fragment = match key.head() {
            Some(head) => head,
            None => return self.value.as_ref()
        };

        // Otherwise, recurse down the tree.
        match self.children.find(fragment) {
            Some(node) => node.find(key.slice_from(1)),
            None => None
        }
    }

    /// Find a mutable reference to a key's value, if it has one.
    pub fn find_mut(&mut self, key: &[K]) -> Option<&mut V> {
        // Recursive base case, if the key is empty, return the node's value.
        let fragment = match key.head() {
            Some(head) => head,
            None => return self.value.as_mut()
        };

        // Otherwise, recurse down the tree.
        match self.children.find_mut(fragment) {
            Some(node) => node.find_mut(key.slice_from(1)),
            None => None
        }
    }

    /// Find the longest prefix of nodes which match the given key.
    pub fn find_prefix_nodes(&self, key: &[K]) -> Vec<&Trie<K, V>> {
        let mut node_path = vec![self];

        for fragment in key.iter() {
            match node_path.last().unwrap().children.find(fragment) {
                Some(node) => node_path.push(node),
                None => break
            }
        }
        node_path
    }

    /// Find the value of the nearest ancestor with a non-empty value, if one exists.
    ///
    /// If all ancestors have empty (`None`) values, `None` is returned.
    pub fn find_ancestor(&self, key: &[K]) -> Option<&V> {
        self.find_ancestor_node(key).and_then(|node| node.value.as_ref())
    }

    /// Find the nearest ancestor with a non-empty value, if one exists.
    ///
    /// If all ancestors have empty (`None`) values, `None` is returned.
    pub fn find_ancestor_node(&self, key: &[K]) -> Option<&Trie<K, V>> {
        let node_path = self.find_prefix_nodes(key);

        for node in node_path.iter().rev() {
            if node.value.is_some() {
                return Some(*node);
            }
        }
        None
    }
}

#[cfg(test)]
mod test {
    use super::Trie;

    fn make_trie() -> Trie<char, uint> {
        let mut trie = Trie::new();
        trie.insert([], 0u);
        trie.insert(['a'], 1u);
        trie.insert(['a', 'b', 'c', 'd'], 4u);
        trie.insert(['a', 'b', 'x', 'y'], 25u);
        trie
    }

    #[test]
    fn find() {
        let trie = make_trie();
        let data = [
            (vec![], Some(0u)),
            (vec!['a'], Some(1u)),
            (vec!['a', 'b'], None),
            (vec!['a', 'b', 'c'], None),
            (vec!['a', 'b', 'x'], None),
            (vec!['a', 'b', 'c', 'd'], Some(4u)),
            (vec!['a', 'b', 'x', 'y'], Some(25u)),
            (vec!['b', 'x', 'y'], None)
        ];
        for &(ref key, value) in data.iter() {
            assert_eq!(trie.find(key.as_slice()), value.as_ref());
        }
    }

    #[test]
    fn find_mut() {
        let mut trie = make_trie();
        let key = ['a', 'b', 'c', 'd'];
        *trie.find_mut(key).unwrap() = 77u;
        assert_eq!(*trie.find(key).unwrap(), 77u);
    }

    #[test]
    fn find_ancestor() {
        let trie = make_trie();
        let data = [
            (vec![], 0u),
            (vec!['a'], 1u),
            (vec!['a', 'b'], 1u),
            (vec!['a', 'b', 'c'], 1u),
            (vec!['a', 'b', 'c', 'd'], 4u),
            (vec!['a', 'b', 'x'], 1u),
            (vec!['a', 'b', 'x', 'y'], 25u),
            (vec!['p', 'q'], 0u),
            (vec!['a', 'p', 'q'], 1u)
        ];
        for &(ref key, value) in data.iter() {
            assert_eq!(*trie.find_ancestor(key.as_slice()).unwrap(), value);
        }
    }

    #[test]
    fn find_prefix_nodes() {
        let trie = make_trie();
        let prefix_nodes = trie.find_prefix_nodes(['a', 'b', 'z']);
        // There should be 3 nodes: root, a, b.
        assert_eq!(prefix_nodes.len(), 3);
        let values = [Some(0u), Some(1u), None];
        for (node, value) in prefix_nodes.iter().zip(values.iter()) {
            assert_eq!(node.value, *value);
        }
    }
}
