<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 9 implementation record

This document records the original Stage 9 inventory rollout. The maintained inventory now includes affine operational ratchet state, establishment-gated `EstablishedRemote`/`BeaconState::Established` ownership, inert update snapshots, duplicate-rejecting canonical state decoding, and generation/head CAS with loser fencing. `SnapshotStore` is trusted for payload integrity and provenance plus linearizable, durable, rollback-resistant head management; snapshots have no cryptographic authentication or encryption. These are reviewed production refinements, not new F* or ProVerif conclusions. Historical references below to clonable forks and the original adapter-count baseline describe the earlier snapshot.

## Result and scope

Stage 9 completes the staged rollout with a maintained, mechanically checked
trust-boundary inventory. The inventory covers opaque production adapters and
primitive calls, the laws assumed when lifting core theorems to production,
concrete-to-logical adapter refinements, pinned proof-library/tool assumptions,
generated-code exceptions, embedded ProVerif replacements, every handwritten
F*/ProVerif review unit, and the result-classification control.

The canonical inventory is
[`crates/protocol-core/proofs/trusted-boundary.md`](../../crates/protocol-core/proofs/trusted-boundary.md).
Its companion manifest fingerprints the complete monitored surface, while a
standalone checker verifies file membership, hashes, backend structure, and
exception use. The existing formal-verification CI entry point now runs this
gate after extraction.

Stage 9 does not change production Rust behavior, an F* theorem, a ProVerif
primitive equation/process/query, or an expected result classification. It
turns the proof's previously distributed trust statements into one reviewable
baseline and makes silent baseline drift fail.

## Review of the Stage 8 commit

This implementation is based on commit
`8803ef9370bd104de92d621d82ece858e013d235`, which completed Stage 8. That
commit and its full diff were reviewed before Stage 9 work.

Stage 8 changed only the locked proof shell, proof/CI Makefiles, the dedicated
workflow, and documentation. It did not change production Rust, either
generated F* module, either handwritten F* lemma module, the generated
ProVerif library, a handwritten ProVerif model/query/process, or the result
classifier. Re-extraction under Stage 8's pinned Rust frontend was
byte-identical to Stage 7, and the reviewed query classifications stayed
unchanged.

No Stage 8 semantic regression was found. Its tool identity, locked-input,
strict F*, exact ProVerif result, timeout, and tracked/untracked generated-diff
controls remain intact.

While Stage 9 was in progress, the branch advanced to
`d291dc7b702dc56b18b79ac56d65436339ecdbf0` (`Add plain english description
of the proofs`). That concurrent commit was also reviewed: it adds only
`doc/formal-verification-analysis.md` and a four-line link from this plan. It
does not alter production code, proof sources, generated artifacts, tool
controls, or result policy. Those documentation changes were preserved and are
not attributed to Stage 9 in the implementation map below.

## Review finding: proof success did not force trust-boundary review

Before Stage 9, a changed trust assumption could still pass the complete
pipeline:

- `check-fstar-policy` rejected local `assume`/`admit` and lax/admitted-query
  flags, but did not inventory external hax library contracts or adapter
  preconditions;
- the ProVerif extraction check rejected known placeholders and required three
  operation names, but did not review the replacement bodies, generated
  defaults/converters, or their handwritten use;
- the result gate ensured exact query classifications, but a handwritten
  primitive equation or process could change while retaining those results;
- `check-generated` rejected a diff from the checked-in extraction, but an
  intentionally committed generated change became the new Git baseline
  without requiring an assumption-inventory update; and
- the Stage 7 artifact table did not include the ratchet lemma file, the two
  top-level ProVerif process files, or the trusted AWK result classifier.

These were review-control gaps, not discovered counterexamples to the existing
F* or ProVerif claims. Stage 9 adds an independent reviewed baseline that must
move explicitly with any such change.

## Implementation map

| File | Responsibility |
| --- | --- |
| `crates/protocol-core/proofs/trusted-boundary.md` | Canonical human-readable inventory of opaque wrappers, laws, refinements, proof-library trust, generated exceptions, handwritten fragments, and trace limits. |
| `crates/protocol-core/proofs/reviewed-inventory.txt` | Category/path/SHA-256 baseline for every monitored production, extraction, proof, model, generated, tool-control, and inventory file. |
| `crates/protocol-core/proofs/check-inventory.sh` | Exact membership/hash and structural exception checker with actionable category/file failures. |
| `crates/protocol-core/Makefile` | Expose `check-inventory` and run it after backend regeneration in complete and ProVerif-only locked-shell verification. |
| `crates/protocol-core/README.md` | Document the inventory purpose, standalone command, and maintenance workflow. |
| `doc/formal-verification.md` | Mark Stage 9 complete, summarize its implementation, and add inventory drift to CI policy. |

## Inventory contents

### Opaque production boundary

The inventory names the exact repository-owned wrapper functions and complete
impl blocks rather than trying to enumerate methods in upstream crates. Those
wrappers are the stable review units that determine how opaque behavior enters
the claimed trace:

- beacon/server construction, registration bundle creation, response finish,
  server acceptance, and response construction;
- the ordered shared-secret translation and root HKDF wrapper;
- one-step ratchet HKDF and two-chain initialization;
- frame sender parsing, encryption, decryption, and commitment construction;
- high-level peer selection and logical/concrete key delegation;
- ratchet/server persistence serialization and checked restoration;
- explicit secret/transcript erasure, recorded as outside the formal claim; and
- the Windows-GNU erasure and OS-RNG compatibility shims.

There are no explicit hax-opaque functions in the isolated core. Every Rust
function outside the core is opaque to extraction, so the manifest recursively
derives and fingerprints the complete production `src` surface. The canonical
inventory individually groups every proof-relevant wrapper and classifies the
remaining binding, platform, API-forwarding, and compatibility functions as
outside the claimed trace.

The underlying operations are OS-backed key generation, Ed25519 sign/verify,
Ed25519-to-X25519 conversion, four complementary X25519 computations, ML-KEM
encapsulation/decapsulation, HKDF-SHA-512, ChaCha20-Poly1305-IETF, BLAKE2b,
byte comparison, Cap'n Proto, serde, allocation, and zeroization.

### Primitive laws and refinements

The inventory distinguishes conditional F* inputs from ProVerif's stronger
ideal symbolic theory. It records freshness, signature provenance,
identity-key conversion, complementary DH agreement, KEM correctness, KDF
determinism/domain separation, AEAD opening/authentication, fixed-tuple CTX
binding, exact encoding constructors, byte-comparison correctness, and the
bounded collision-free abstraction of finite IDs/sequences.

Sixteen adapter refinements cover the production correspondence: exact
logical/concrete ratchet caches, one KDF call per logical step, paired send
capabilities, receive retry/consumption, peer-map isolation, checked restore,
signed wire translation, shared-secret order, ratchet splitting, response and
assigned-ID authentication, monotonic replay state, truthful ID availability,
failure-free logical publication, single-use beacon coins, exact Phase-2 and
CryptoFrame mappings, and high-level/no-rollback trace preconditions.

None is turned into an F* axiom. Cap'n Proto, concrete primitives, allocation,
persistence media/integrity beyond import validation, zeroization mechanics,
FFI, independent replicas, rollback recovery, low-level compatibility calls,
and cloned/forked live state remain explicit exclusions.

### Proof-library and generated exceptions

The F* proof-library inventory identifies the three val-only fixed-range
update contracts used by the PQXDH layout proof and the val-only
`shift_right_lemma` contract used by the little-endian key-ID proof. The other
selected array, slice, Option/Result, equality, and finite-integer operations
are transparent definitions in the pinned hax/Core_models libraries.
Correctness of hax translation, F*/Z3 checking, and ProVerif analysis remains
trusted.

The generated ProVerif baseline is deliberately explicit:

- the public channel, generic option constructors/error, empty constant, and
  primitive bitstring/nat/bool defaults and conversions in hax's preamble;
- six selected nominal types and their data constructors;
- twelve generated type converters;
- six arbitrary record default constants;
- nine error helpers and eleven textual `construct_fail()` occurrences;
- nineteen reductions in total; and
- exactly three production-backed operations.

Handwritten code uses only `RootKeyInput_to_bitstring`, at exactly two root-KDF
sites. It never calls a generated `from_bitstring`, default, or error helper.
The root-input backend replacement models the successful constructor path and
does not model the Rust all-zero-DH error; F* proves that error behavior, while
the honest ProVerif processes call the symbolic constructor after ideal DH.

The F* exceptions record generated module options, proof-language visibility
of Rust-private constructors, the three reviewed range contracts, and the
reviewed right-shift lemma contract. Local assumptions/admissions, the former
opaque `to_le_bytes`,
`while_loop_return`, and derived whole-binding equality assumptions remain
prohibited rather than inventoried exceptions.

### Handwritten units

Every recursively discovered non-generated `.fst`, `.fsti`, `.pv`, `.pvl`,
and the AWK classifier is in the exact membership manifest. The F* lemma files
are strictly checked proofs rather than trusted axiom modules, but their
complete contents are still review units. The three embedded Rust replacement
attributes and both extraction/checker Makefiles are separately inventoried.

Whole-file hashes intentionally make each file the review atom. This covers
all primitive declarations, reductions, wire constructors, events, tables,
free names, processes, queries, proof helpers, and result-policy branches
without relying on a parser that might miss a newly valid backend syntax form.

## Mechanical review gate

`make check-inventory` performs four layers of checks:

1. Parse the manifest strictly, including a valid final record without a
   trailing newline, and reject unknown categories, malformed/truncated
   records, missing/duplicate paths, and any SHA-256 mismatch.
2. Independently derive and compare exact file sets for all production Rust
   and schemas, protocol-core Rust, generated F*/ProVerif artifacts, and
   handwritten F*/ProVerif files. Generated membership recursively discovers
   backend source extensions even when an ignore rule would hide them from
   Git. A second exhaustive set check admits no other file extension under
   `proofs/`, and monitored-tree symlinks are rejected.
3. Require no hax opaque annotation and exactly the three reviewed ProVerif
   replacements; multiline, no-ignore scans enforce the generated
   type/converter/default/error/reduction baseline and the sole allowed
   handwritten converter use.
4. Enforce handwritten primitive, event, table, free-name, process, and query
   counts and reject the prohibited generated F* constructs.

The manifest monitors the entire root `src/*.rs` and schema surface
conservatively, not just files that currently call the protocol core. It also
monitors both Cargo manifests, the workspace lockfile, Cargo configuration,
ignore policy, extraction selectors, F* flags, locked flake,
formal-verification workflow, generated artifacts, handwritten proof files,
result checker, mandatory protocol regressions, and the inventory gate itself.

There is no automatic manifest-refresh target. An intentional change must be
reviewed, documented in the canonical inventory where its meaning changes,
regenerated and proved, and then receive only the affected new digest. This
creates a visible review diff but cannot cryptographically establish who
reviewed it or whether their reasoning was sound.

## CI ordering

The complete locked-shell order is now:

1. verify exact tool identities;
2. regenerate and strictly check F*;
3. regenerate ProVerif;
4. run all strict ProVerif scenarios and result classification; and
5. check the complete inventory against the post-regeneration, post-proof tree.

The ProVerif-only target also checks the inventory after its extraction and
strict result checks. CI continues to invoke only:

```sh
make -C crates/protocol-core check-generated
```

That target inherits the inventory gate through `verify` and then retains the
tracked/untracked generated Git diff check. Running the inventory after
regeneration prevents a pre-extraction check from accepting stale generated
hashes.

## Compatibility and proof meaning

There is no wire, API, persistence, production dependency, theorem, query, or
expected-result change in Stage 9. The generated artifacts remain the Stage 7
semantic baseline reproduced by Stage 8's locked toolchain. Normal production
builds still do not enable the extraction-only `proverif` feature.

The completed rollout supports protocol claims only under the enumerated
primitive laws, adapter refinements, model bounds, and trace preconditions. It
does not prove the primitive implementations, serialization libraries,
persistence media, erasure, bindings, rollback/replica coordination, or
computational security of the symbolic ProVerif model.

## Validation performed

The implementation is validated with:

```sh
make -C crates/protocol-core check-inventory
make -C crates/protocol-core check-generated
cargo fmt --all -- --check
cargo test --workspace --all-targets --locked
cargo check --locked --no-default-features --features pqxdh,server --lib
cargo check --locked --no-default-features --features pqxdh,beacon --lib
cargo clippy --workspace --all-targets --all-features --locked -- \
  -D warnings -A clippy::type-complexity
git diff --check
```

All commands pass. The locked shell reports rustc 1.93.0-nightly, Cargo
1.93.0-nightly, hax 0.3.7, F* 2025.10.06~dev, Z3 4.15.3, and ProVerif 2.05.
Both generated modules and both handwritten F* lemma modules discharge every
obligation. ProVerif returns the exact reviewed classifications: eleven true
baseline results, five false reachability negations, and two true plus three
false compromise results. The Rust workspace runs 168 tests with no failures
or ignored tests; both minimal feature builds, formatting, clippy with the
repository's existing type-complexity allowance, and whitespace checks pass.

Negative checker trials run in isolated temporary copies. The gate rejects a
monitored-byte change; missing, substituted, or truncated manifest records;
correctly processes a valid final record without a trailing newline; and
rejects unexpected top-level or nested handwritten proof files, ignored extra
generated files, a fourth replacement in either reviewed Rust module,
single-line or multiline/whitespace-obscured replacement syntax, and
single-line or multiline handwritten calls to generated default/error helpers.
Additional trials reject arbitrary-extension helpers and symlinked proof or
Rust source files.
The unchanged generated identities are:

| Generated artifact | Lines | SHA-256 |
| --- | ---: | --- |
| F* PQXDH module | 932 | `d73891ba4ac6818a5a1d8fdb3f3fe8daaccb077489ee0fd428519c8eabd90941` |
| F* ratchet module | 360 | `7c8fcf79aa084d032742462dcdf23bcb0367f5711010eba4688c8bd71821afd7` |
| ProVerif library | 358 | `81ef938f5726bb5f6fcf482b29199c06e66c7805caac0b5a73414f653038f386` |
