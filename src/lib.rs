///! A tree-like data structure for storing paths and associated data.

use std::fmt::{Show, Formatter, FormatError};
use std::hash::Hash;
use std::collections::hashmap::HashMap;

pub struct Node<K, V> {
    pub key: K,
    pub value: Option<V>,
    pub children: HashMap<K, Node<K, V>>
}

impl<K, V> Node<K, V> where K: PartialEq + Eq + Hash + Clone {
    pub fn new(key: K) -> Node<K, V> {
        Node {
            key: key,
            value: None,
            children: HashMap::new()
        }
    }

    pub fn insert(&mut self, path: &[K], value: V) {
        let current_node = path.iter().fold(self, |current_node, key| {
            current_node.children.find_or_insert(key.clone(), Node::new(key.clone()))
        });
        current_node.value = Some(value);
    }

    pub fn find_path(&self, path: &[K]) -> Vec<&Node<K, V>> {
        let mut node_path = vec![self];

        for key in path.iter() {
            match node_path.last().unwrap().children.find(key) {
                Some(node) => node_path.push(node),
                None => break
            }
        }
        node_path
    }

    pub fn ancestor_value(&self, path: &[K]) -> Option<&V> {
        let node_path = self.find_path(path);

        for node in node_path.iter().rev() {
            if node.value.is_some() {
                return node.value.as_ref();
            }
        }
        None
    }
}

impl<K, V> Show for Node<K, V> where K: Show, V: Show {
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), FormatError> {
        try!("Node { key: ".fmt(formatter));
        try!(self.key.fmt(formatter));
        try!(", value: ".fmt(formatter));
        try!(self.value.fmt(formatter));
        try!(" }".fmt(formatter));
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::Node;

    #[test]
    fn path_finding() {
        let mut root: Node<&'static str, uint> = Node::new("root");
        root.insert(["a", "b", "c"], 3u);
        root.insert(["a"], 1u);
        root.insert(["a", "b"], 2u);
        root.insert([], 0u);

        let node_path = root.find_path(["a", "b", "c"]);
        let results = [("root", 0u), ("a", 1), ("b", 2), ("c", 3)];
        for (node, &(key, value)) in node_path.iter().zip(results.iter()) {
            assert_eq!(node.key, key);
            assert_eq!(node.value.unwrap(), value);
        }
    }

    #[test]
    fn ancestor_value() {
        let mut root: Node<uint, uint> = Node::new(0u);
        root.insert([1u, 2, 3], 3u);
        root.insert([1u, 2, 3, 4, 5, 6], 6u);
        root.insert([1u, 2, 3, 7, 8, 9], 9u);
        assert_eq!(root.ancestor_value([1u, 2, 3, 4]), Some(&3u));
    }
}
