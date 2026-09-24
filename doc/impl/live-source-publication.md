# Bounded source frame publication

`RawCtxSourcePublication` closes a precise part of the gap between an inner CTX seal and the optional ciphertext returned by the source send adapter. Under the ordinary bounded, normal-return codec contract, the writer cannot suppress an already completed inner seal. The theorem keeps the original key, nonce, complete public context, actual protected record, encoded bytes, auxiliary state and shared hash cache on the same execution. It does not assume that every inner seal is a published message in the earlier generic optional-writer interface.

## Concrete library boundary

The production `seal_frame` in `beaconcrypt/src/ratchet.rs` obtains the detached AEAD body and tag, computes the commitment, appends tag and commitment, sets the CryptoFrame payload, sequence and sender in source order, and calls `capnp::serialize::write_message` with a fresh `Vec<u8>`. The locked dependency is Cap'n Proto 0.26.2, with the standard-library feature enabled.

Inspection of that pinned dependency's `src/serialize.rs` shows that `write_message` propagates only errors from the sink's `write_all` operations. `src/io.rs` forwards this call to the standard-library writer. `Vec<u8>::write_all` appends the bytes and returns success on normal return; allocation failure and panic are not an `Err` value that becomes the source's optional None. This is an ordinary codec/allocator boundary, not a security assumption about protocol origin. The proof does not verify Cap'n Proto, Rust's standard library or allocator implementations.

The builder has a concrete size limit. Cap'n Proto's `private/layout.rs::set_list_size_and_count` asserts that a Data list has fewer than `2^29` elements. The source's protected payload has `plaintext.length + 80` bytes: the unchanged ChaCha20-Poly1305 body length, a 16-byte tag and a 64-byte commitment. `BodyLength` states only that ordinary detached-body length law; it imposes no secrecy or authentication premise. The theorem therefore uses the explicit domain `plaintext.length + 80 < 2^29` alongside the source's 153-byte associated-data width.

This domain is not an implemented admission check. The current source only rejects empty application messages before sending. The proof makes no normal-return or availability claim for oversized messages, exhausted allocation, native panics or other external runtime failures. Those cases must not silently become an optional serialization failure in a claimed exact normal-return interpretation.

`WritesOn writer encode` says that the actual writer returns `some (encode frame)` for bounded Data fields. Here `encode` denotes its actual serialized bytes, not a new wire format or an independently sampled string. `ReadsOn reader encode` is the existing ordinary conditional field law: if reading, root access and payload access succeed, their results are the fields supplied to the writer and the input is consumed completely. It allows reader rejection. In particular, the default production `ReaderOptions` has a traversal limit, so this module does not assert that every successfully written buffer is accepted by the default reader. Native library binding and implementation correctness remain explicit external contracts; the source setting order and decoder prelude already have separate checked modules.

## Ten checked consumers

| Theorem | Established result |
| --- | --- |
| `shared_publication` | The original shared-cache source seal equals its actual typed CTX computation followed by successful encoding on the bounded domain. This is a complete computation equality, including auxiliary state and the actual final hash cache. |
| `source_shared` | The live service's real sealing callback is exactly the existing canonical shared interpreter on every input, including invalid-width rejection. |
| `source_publication` | Instantiates the bounded publication equality with the real fixed-HKDF source callback used by the live service. |
| `source_supported` | Gives both directions of the supported-result correspondence: each source outcome and its matching inner record have exactly the same cache and actual serialized bytes. It does not choose a separate witness execution. |
| `source_no_failure` | A bounded, valid-width, normally returning source seal has no supported None result under the displayed codec contract. It does not erase native runtime failures or apply to an arbitrary optional writer. |
| `protected_length` | Derives the exact protected-payload length from a supported inner source seal and the ordinary detached-body length law. |
| `source_decode` | Whenever the actual published bytes successfully decode, the result has the exact source sequence, sender and protected inner record, with its original cache and auxiliary state. It supplies no unconditional reader-success claim. |
| `pending_publication` | The real prepared-send adapter wraps those actual bytes in Some with the selected sequence and original API target. The encoded sender and API target remain distinct. |
| `source_continued` | Any subsequent adaptive computation receives the same actual Some bytes and complete primitive poststate. The equality applies before probability evaluation, preserving ciphertext-dependent continuations. |
| `source_uniform` | The original source callback uses at most 64 byte-valued uniform queries for its one shared commitment request, including the optional-writer branches outside the bounded contract. |

The source call budgets already distinguish its one AEAD, one commitment and one writer call. The last theorem is a sampling bound, not a claim that AEAD evaluation, byte appends, builder allocation, serialization or subsequent application work is free. No new cryptographic advantage or statistical loss is introduced by these exact equalities. They retain all actual key/nonce correlations and impose no independence, honest-target or no-alias condition.

The prepared-send result is the value passed unchanged through the existing extracted finish and owner reinstallation proofs. Consuming this module in a global selected-record compiler still has to establish its actual bounded inputs, use the ordinary native codec binding, and relate the returned value to the relevant public API transcript. A successful callback is not an assertion that the caller delivered the frame over a network. Registration transactions or other outer operations may have additional publication decisions and need their own existing source boundaries.

This module supplies the bounded source publication obligation for the target-relative symbolic material service. It does not finish the applied-pi trace map, the multi-session security theorem, current-chain/reveal freshness, per-key nonce accounting or registration/session agreement. Raw byte identity remains separate from decoded field identity; no canonical wire encoding is assumed. Snapshots, persistence and primitive implementation proofs remain outside the task.

All ten guarded dependency checks pass with only `propext`, `Classical.choice` and `Quot.sound`. Direct check evidence is `/tmp/source-publication-guarded.log`. No Rust or shared proof gate is changed by this isolated package; integration must add its root import, documentation entry and inventory locks after independent review.
