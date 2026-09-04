# Representation bridge milestone

## Audit

The current `vcvio` base has `Pqxdh.ratchetCrypto c` over byte-list chains and key/nonce pairs, and `ratchet.concrete.withInterpreter cr execute` over extracted chain and material wrappers. There are no declarations literally named `CryptoInterpretation` or `ConcreteCrypto`. Existing `PqxdhInitialRatchetComplementarity` explicitly does not identify these interpretations; it connects initial chain bytes and zero-state kernels only. Existing `RatchetByteSurface` identifies each extracted 76-byte response offset but does not prove its equality with the byte model's ongoing KDF. Consequently, prior ongoing ratchet and initialization theorems could use unrelated cryptographic interpretations.

## Agreed interface and ownership

`BeaconcryptCore/Refinement/RepresentationBridge.lean` owns the exact byte maps `absChain`, `absMaterial`, `mapSend`, and `mapRecv`, the record interpretation `recordCrypto`, the extracted-step interpretation `concreteCrypto`, the primitive `KdfLaw`, and operation commutation. Protocol composition owns the separate 64-byte initial KDF law. The ideal models remain unchanged.

## Proved

- `interpretedStep_bytes` identifies the chain, AEAD key, and nonce produced by the actual extracted response parser with the model's complete byte slices. It follows from the existing extracted splitter equation and injective response-result equality.
- `kdfChain_commutes`, `kdfMsg_commutes`, `chainAt_commutes`, `msgKeyAt_commutes`, and `skipKeys_commutes` connect ongoing derivation and all cached material at every logical index.
- `absChain_injective` and `absMaterial_injective` establish that these maps erase no chain, key, or nonce information.
- `sendStep_commutes` preserves the exact logical index, complete encoded record, and full send poststate.
- `recvStep_commutes` preserves every complete plaintext or receive error and the full receive poststate, including cached-key removal, newly skipped keys, replay, skip-budget rejection, and authentication-failure rollback.
- `ByteKernelRefines` composes the established extracted-kernel relation with the exact representation maps. Its witnesses retain live-slot soundness, completeness, and empty-tail properties. `chainsAndCounters` exposes equality of both chains and counters directly.

## Legitimate assumptions

`KdfLaw c execute` requires the interpreter's 76-byte reply to equal `c.hkdf` on the actual core-issued chain bytes and `INFO_R` label. It is a primitive reply representation equation, not a premise about any protocol transition or desired refinement conclusion. The law does not require HKDF pseudorandomness or a prefix assumption.

`recordCrypto` interprets sealing and opening as the existing PQXDH model's record operations on all represented key and nonce bytes, with identical `RecordAD`, plaintext byte strings, and ciphertext byte strings. A concrete external interpreter must implement those operations, including record parsing, associated-data binding, CTX checking, and AEAD. This module does not verify any cryptographic implementation or surrounding library. Send-failure and adapter outcome handling belong to the API execution semantics, rather than to this total record interpretation. The existing correctness/length laws bundled by `Pqxdh.Crypto` remain explicit model boundary assumptions.

The proof is about imported extracted Lean definitions and relies on the existing extraction/toolchain trust boundary. It adds no custom axioms, `sorry`, `admit`, or refinement-shaped assumptions. The guarded axiom checks for both complete step commutation theorems report only `propext`, `Classical.choice`, and `Quot.sound`.

## Validation and remaining work

The module is checked incrementally with Lean 4.31.0, then built with `lake.orig build BeaconcryptCore.Refinement.RepresentationBridge`. The interpreter wrapper `lake` has a stale Nix-store Bash shebang in this environment; invoking the installed `lake.orig` avoids that unrelated environment issue. Full repository verification, inventory checks, documentation integration, and final branch integration are coordinator responsibilities. This milestone alone does not claim complete API history or registration refinement; subsequent protocol and trace composition must consume these operation equalities.
