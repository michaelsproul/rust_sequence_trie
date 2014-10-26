[Generic Trie][doc]
===================

[![Build Status](https://travis-ci.org/michaelsproul/rust-generic-trie.svg)](https://travis-ci.org/michaelsproul/rust-generic-trie)

This is a generic Trie implementation that uses a hash map to store child nodes. The Trie is keyed
by lists of type `K`, which can be anything implementing `PartialEq`, `Eq`, `Hash` and `Clone`.

For more information, see the [documentation][doc].

# Performance

At the moment this data structure is hideously slow. Here are some benchmarks comparing it to a single `HashMap`.

```
# Keys of length 16.
test benchmark::hashmap_k1024_l16 ... bench:    482449 ns/iter (+/- 14268)
test benchmark::trie_k1024_l16    ... bench:   5886284 ns/iter (+/- 139267)
# Keys of length 128.
test benchmark::hashmap_k64_l128  ... bench:    190855 ns/iter (+/- 20254)
test benchmark::trie_k64_l128     ... bench:   2051748 ns/iter (+/- 226994)
```

In these benchmarks, the Trie is around 12x slower...

I plan to remedy this, possibly by switching to a Patricia/Radix Trie (suggestions welcome).

[doc]: http://www.rust-ci.org/michaelsproul/rust-generic-trie/doc/trie/
