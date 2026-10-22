# Property-based testing

This change adds test-only Proptest dependencies to the transport codec and public adapter crates. Production dependencies, protocol behavior, wire formats, snapshots, known-answer vectors, generated codecs, and formal proofs are unchanged.

## Contracts and independent models

Codec properties generate valid values, canonical encodings, structured syntax violations, and bounded arbitrary inputs. They compare decoded values, encoded sizes, and canonical bytes. Boundary strategies explicitly exercise CBOR width transitions and complete-message limits; size arithmetic can be tested without repeatedly allocating maximum-size payloads. Parsing syntax does not establish cryptographic validity. A syntactically valid empty ciphertext need not be admissible as a protected record, and arbitrary byte changes need not produce invalid syntax.

Ratchet histories exercise both directions and multiple peers with send bursts, delayed delivery, replay, malformed input, authentication failures, and routing changes. An independent sequence/set model predicts receive admission and cached-key consumption without invoking production transition functions. Authentic delivery after a rejected attempt checks that failed authentication did not consume its receive key. Admission accounts for existing cached keys plus skipped sequences; the incoming target does not occupy a cache slot.

Persistence histories track the authoritative head, generation, CAS attempts, sent records, and accepted records while interleaving protocol operations and activation. Restoring claims a new generation, so continuity means preserving session behavior rather than preserving the complete snapshot bytes. CAS failure withholds output and poisons the owner; recovery uses the trusted current store. Rejected established receives neither commit nor consume an armed CAS failure. Registration properties separately model pending, established, and aborted lifecycles: invalid completion destroys pending secrets. Existing registration failure regressions continue to cover consumed requests when server response construction fails.

These runtime tests complement the existing vectors, exhaustive authentication checks, explicit boundary regressions, and formal guarantees. They do not replace tests of the exact wire and persistence compatibility contracts or establish the durability of an application's storage implementation.

## Wasm coverage found by mutation testing

The first complete mutation campaign found 31 survivors in the existing Wasm tests. New tests exercise constructor guards, identity and ratchet-status dispatch, exported allocation/call/free operations, complete packed replies, snapshot host callbacks, and wiping before buffer deallocation. The zeroization observer inspects initialized live allocations before the system allocator releases them. Guest pointer and callback tests run on actual `wasm32-wasip1` with the production 256 MiB memory bound through a small Wazero runner. An isolated probe distinguishes acceptance of the largest admissible snapshot length followed by allocation failure from premature rejection, without allocating 2 GiB.

Native mutation testing covers the adapter, core, and parser. `.cargo/mutants-wasm.toml` separately covers the guest on its real target through `scripts/test-wasm.sh --mutants`; the Wasm CI job runs these guest unit tests before building the release artifact. Three exact-location exclusions document equivalent guest mutations: pointer/length OR versus XOR over disjoint halves, and two fallible allocation guards whose changed cases still return zero under the supported wasm32 memory bound. No remaining guest code is excluded from that target's mutation campaign.

## Running and reproducing

The normal `cargo test --workspace --locked` command includes bounded property campaigns. Run the new targets alone with:

```sh
cargo test -p beaconcrypt-parse --test properties --locked
cargo test -p beaconcrypt --test ratchet_properties --test persistence_properties --test registration_properties --locked
```

Increase exploration or reproduce a campaign using the decimal seed and case count:

```sh
PROPTEST_CASES=256 PROPTEST_RNG_SEED=104729 cargo test -p beaconcrypt-parse --test properties --locked
PROPTEST_CASES=256 PROPTEST_RNG_SEED=104729 cargo test -p beaconcrypt --test ratchet_properties --test persistence_properties --test registration_properties --locked
```

Integration tests explicitly persist failure seeds under each crate's `proptest-regressions/` directory, independently of the current working directory. Commit those regression files when a failure is found. Preserve significant bugs as named tests with concrete inputs or command histories as well: changing a generator or dependency can change the meaning of a seed. Generated commands use stable selectors and bounded data so shrinking can remove steps without leaving invalid references. Assertions concern semantic outcomes rather than equality of randomly generated cryptographic keys or ciphertexts; Proptest's seed controls test inputs, not production entropy.

The existing Rust pull-request job runs bounded campaigns with fresh random inputs and uploads failure seeds. The `Property tests` workflow runs larger campaigns every Monday at 03:23 UTC and can be dispatched manually with a case count. Each of its three jobs derives and logs a seed from the workflow run ID plus its matrix offset, so new runs explore new inputs while retries of the same run remain reproducible. Failed jobs upload regression files for local replay.

For mutation testing, use a fixed seed and the normal bounded case counts so comparisons between mutants use the same generated inputs:

```sh
PROPTEST_RNG_SEED=104729 cargo mutants --workspace
bash scripts/test-wasm.sh --mutants --output .build/wasm-mutations
```

Both mutation configurations enforce the lockfile. The guest script requires the Rust target and Zig versions pinned in `scripts/wasm-toolchain.json`, plus the repository's Go toolchain. It runs the real guest tests with `bash scripts/test-wasm.sh` and the guest mutation campaign with `--mutants`. Do not lower the property case counts for mutation testing.

## Validation

Validation used Rust 1.97.1 and the committed lockfile:

- `cargo fmt --all` and `git diff --check` pass.
- `PROPTEST_RNG_SEED=104729 cargo test --workspace --locked --offline` passes all 343 tests.
- Both role-only library checks pass with `--no-default-features --features pqxdh,beacon` and `--no-default-features --features pqxdh,server`.
- `cargo clippy --workspace --all-targets --all-features --locked --offline` passes. The existing `partialeq_ne_impl` warning in the core and `missing_const_for_thread_local` warning in the Wasm adapter remain; a stricter `-D warnings` run stops at the former. The new property targets introduce no warnings.
- All eleven new tests pass with `PROPTEST_CASES=256` under each of seeds `104729`, `130363`, and `155921`: 7,680 generated cases across ten properties, plus the deterministic complete-message boundary checks.
- `bash scripts/test-wasm.sh --offline` passes 22 ordinary guest tests and the isolated allocation-failure probe under the pinned Rust/Zig toolchains.
- `go vet -mod=readonly -buildvcs=false ./scripts/wasm-test-runner`, shell syntax checks, and parsing all three changed workflows as YAML pass.

Complete fresh mutation reruns pass without `--iterate`: the native campaign tests all 1,299 configured mutants (908 caught, 391 unviable), and the WASI campaign tests all 135 non-equivalent guest mutants (123 caught, 12 unviable). Both reports have empty `missed.txt` and `timeout.txt` files. The initial 31 guest survivors are resolved as 28 additional caught mutants and the three documented equivalent exclusions. The native run uses seed `104729`, 12 jobs, and 60-second test/120-second build limits; the guest run uses four jobs and 120-second test/180-second build limits. Property case counts remain at their normal defaults throughout mutation testing.
