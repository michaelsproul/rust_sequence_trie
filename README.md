[Generic Trie][doc]
===================

[![Build Status](https://travis-ci.org/michaelsproul/rust-generic-trie.svg)](https://travis-ci.org/michaelsproul/rust-generic-trie)

This is a generic Trie implementation that uses a hash map to store child nodes. The Trie is keyed
by lists of type `K`, which can be anything implementing `PartialEq`, `Eq`, `Hash` and `Clone`.

For more information, see the [documentation][doc].

[doc]: http://www.rust-ci.org/michaelsproul/rust-generic-trie/doc/trie
