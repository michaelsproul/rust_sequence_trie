extern crate path_tree;

use path_tree::Node;

fn main() {
    let mut root: Node<&'static str, uint> = Node::new("root");

    root.insert([], 0u);
    root.insert(["one", "two", "three"], 3u);

    println!("Path for [one, two, three]: {}", root.find_path(["one", "two", "three"]));
    println!("Path for []: {}", root.find_path([]));
    println!("Nearest ancestor for [one, two]: {}", root.ancestor_value(["one", "two"]));
}
