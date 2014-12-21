[Sequence Trie][doc]
====

[![Build Status](https://travis-ci.org/michaelsproul/rust-sequence-trie.svg)](https://travis-ci.org/michaelsproul/rust-sequence-trie)

This is a generic Trie implementation that uses a hash map to store child nodes. The Trie is keyed by lists of type `K`, which can be anything implementing `PartialEq`, `Eq`, `Hash` and `Clone`. If your keys are explicit lists and you want to be able to store a different value for each fragment of a key, this might be the data structure for you!

I'm still undecided about what to call this data-structure, as it's kind of half-way between an unbounded tree and a trie... Suggestions welcome.

For more information, see the [documentation][doc].

[doc]: http://sproul.io/rust/sequence_trie/
