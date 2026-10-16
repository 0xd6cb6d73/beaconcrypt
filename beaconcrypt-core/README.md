# beaconcrypt-core

The `no_std` protocol state machine used by `beaconcrypt`. This crate owns deterministic PQXDH registration transitions, symmetric ratchet state and receive-key caching, record admission, and commitment transcripts. Cryptographic primitives, entropy, wire parsing, and storage are supplied by the `beaconcrypt` adapter.

The crate forbids unsafe Rust and erases owned ratchet secrets with `zeroize`. The `test-utils` feature exposes additional receive transitions for adapter regression tests.
