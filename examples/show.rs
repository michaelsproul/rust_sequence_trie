extern crate trie;

use trie::Trie;

fn main() {
    let mut trie: Trie<&str, bool> = Trie::new();
    trie.insert(&["wow", "cow"], true);
    trie.insert(&["wow", "this"], false);
    println!("{}", trie);
}
