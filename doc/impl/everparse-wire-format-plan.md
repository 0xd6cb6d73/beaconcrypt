<!-- SPDX-License-Identifier: 0BSD -->

# Verified wire-format migration plan

## Status and baseline

This document is an implementation plan for the `proof` branch at commit `3a80190b534ffd891743d63b0e780d8427743c9c`. It describes proposed future work and does not record completed behavior.

The objective is to replace the three Cap'n Proto protocol messages with a format whose attacker-facing parser is generated and verified through EverParse or Vest, while minimizing deployed code size. Wire compatibility with Cap'n Proto is not required, and the implementation MUST NOT retain a legacy decoder or negotiate between formats.

This plan does not cover the canonical JSON server-persistence format. It also does not change signatures, key encodings, KDF inputs, associated data, the ratchet, the CTX commitment transcript, replay identifiers, persistence envelopes, or public byte-buffer APIs.

A local planning baseline built with Rust 1.97.1 for `x86_64-unknown-linux-gnu` using `cargo build --release -p beaconcrypt --no-default-features --features pqxdh,beacon,server --lib` produced a stripped `libbeaconcrypt.so` of 510,656 bytes, with 494,760 bytes reported in its text section by `size`. These figures are not a cross-platform target; every candidate MUST be compared using the same commit, toolchain, target, feature set, linker, and clean build procedure.

## Current serialization boundary

The protocol wire surface contains only three message shapes:

- `InitKex` contains the encoded beacon identity and three signed public-key fields.
- `KexResponse` contains the assigned key ID, server identity, ephemeral X25519 key, ML-KEM ciphertext, and an initial serialized `CryptoFrame`.
- `CryptoFrame` contains a sequence number, sender key ID, and the protected payload `ciphertext || AEAD tag || commitment`.

Cap'n Proto generation currently runs from `beaconcrypt/build.rs`, which means every normal source build requires the schema compiler. Generated modules are exposed from `beaconcrypt/src/lib.rs`, and direct Cap'n Proto use appears in `beaconcrypt/src/beacon.rs`, `beaconcrypt/src/server.rs`, `beaconcrypt/src/ratchet.rs`, tests, and malformed-input fixtures.

The cryptographic core already gives the registration fields exact semantic widths. The Ed25519 identity encoding is 33 bytes, each signed encoded X25519 field is 98 bytes, the signed encoded ML-KEM-768 public key is 1,249 bytes, a raw Ed25519 or X25519 public key is 32 bytes, and an ML-KEM-768 ciphertext is 1,088 bytes. A protected frame payload must be longer than the 80-byte AEAD-tag-plus-commitment overhead because plaintexts are nonempty.

## Candidate A: EverCDDL and deterministic CBOR

EverCDDL accepts CDDL and generates Rust data types, parsers, and serializers for deterministic CBOR. The generated Rust is currently standalone rather than requiring a separately installed EverCBOR runtime. This path offers the strongest generated end-to-end codec story: the parser and serializer come from the same checked format description, and deterministic CBOR provides a canonical representation.

An illustrative schema is:

```cddl
init-kex = [
  1, 1,
  bstr .size 33,
  bstr .size 98,
  bstr .size 98,
  bstr .size 1249
]

crypto-frame = [
  1, 3,
  uint,
  uint,
  bstr
]

kex-response = [
  1, 2,
  uint,
  bstr .size 32,
  bstr .size 32,
  bstr .size 1088,
  crypto-frame
]
```

The exact fixed-size and minimum-size refinement syntax MUST be validated against the pinned EverCDDL release before this becomes an authoritative schema.

Arrays are preferable to CBOR maps because all fields are mandatory and ordered. Literal version and message-kind fields make the alternatives unambiguous, reject cross-message confusion, and leave room for a future incompatible version. Embedding `crypto-frame` directly removes the current serialize-inner-frame/store-as-bytes/parse-inner-frame cycle.

The disadvantages for this repository are runtime and generated-code size, a more complicated generated API than the format requires, and a larger generator toolchain. Deterministic CBOR must recognize canonical integer and byte-string encodings and represent general CBOR structure even though beaconcrypt needs only three tuples. Link-time optimization may remove much of that machinery, so the size cost MUST be measured rather than assumed.

EverCDDL is documented in the EverParse repository at <https://github.com/project-everest/everparse>, and the verified deterministic-CBOR/CDDL design is described at <https://arxiv.org/abs/2505.17335>.

## Candidate B: a custom flat format parsed with EverParse/3D actions

A flat format is a particularly good structural fit because every message is fixed-width or consists of a fixed-width prefix followed by exactly one variable-width tail. It needs no tree representation, field tags, padding, offset table, or embedded length. The caller already supplies exactly one message as `&[u8]`, so the containing transport remains responsible for message framing.

Each message begins with the following three bytes:

```text
magic   = 0xbc
version = 0x01
kind    = 0x01 InitKex | 0x02 KexResponse | 0x03 CryptoFrame
```

All integers are fixed-width little-endian `u64`. Little-endian is selected to match the existing assigned-ID plaintext binding and commitment transcript, although the wire integers remain separate from those cryptographic byte strings.

### `InitKex`

```text
offset  size   field
0       1      magic
1       1      version
2       1      kind = 1
3       33     encoded beacon identity
36      98     signature || encoded prekey
134     98     signature || encoded one-time key
232     1249   signature || encoded ML-KEM-768 key
```

The only valid `InitKex` length is 1,481 bytes. The format is a direct concatenation of already role-tagged and signed values, so it adds no redundant length metadata.

### `CryptoFrame`

```text
offset  size       field
0       1          magic
1       1          version
2       1          kind = 3
3       8          sequence, little-endian
11      8          sender key ID, little-endian
19      remaining  protected payload
```

The minimum valid frame length is 100 bytes: the 19-byte prefix, at least one ciphertext byte, a 16-byte AEAD tag, and a 64-byte commitment. The protected payload consumes the remainder of the input, so no length field is necessary and no alternate encoding represents the same semantic frame.

### `KexResponse`

```text
offset  size       field
0       1          magic
1       1          version
2       1          kind = 2
3       8          assigned beacon key ID, little-endian
11      32         server Ed25519 identity
43      32         ephemeral X25519 public key
75      1088       ML-KEM-768 ciphertext
1163    remaining  complete CryptoFrame encoding
```

The nested frame starts at byte 1,163 and consumes the remainder. The minimum valid response length is therefore 1,263 bytes. Reusing the complete frame encoding makes standalone and registration frames identical and lets the response validator apply the frame constraints transitively.

The standard 3D buffer entrypoints use a 32-bit input length. The Rust façade MUST reject inputs longer than `u32::MAX` before conversion, and the implementation SHOULD define a substantially smaller deployment limit for protected payloads if beaconcrypt is expected to receive untrusted transport allocations. That policy limit is separate from the structural encoding and must apply consistently to standalone and nested frames.

### 3D specification shape

The authoritative `.3d` syntax MUST be produced and checked with the pinned tool, but its conceptual structure is:

```c
typedef struct _WireHeader(UINT8 ExpectedKind) {
  UINT8 Magic { Magic == 0xbc };
  UINT8 Version { Version == 1 };
  UINT8 Kind { Kind == ExpectedKind };
} WireHeader;

entrypoint typedef struct _InitKex {
  WireHeader(1) Header;
  UINT8 IdentityKey[33];
  UINT8 PreKey[98];
  UINT8 OneTimeKey[98];
  UINT8 PqKey[1249];
} InitKex;

entrypoint typedef struct _CryptoFrame(UINT32 TotalLength) {
  WireHeader(3) Header;
  UINT64 Seq;
  UINT64 KeyId;
  UINT8 ProtectedPayload[TotalLength - 19];
} CryptoFrame;
```

`KexResponse` would use the same pattern with a fixed prefix and a nested frame whose length is `TotalLength - 1163`. The real specification MUST reject underflow before subtracting the fixed prefix, require the frame and response minimum lengths, require exact end-of-input consumption, and use the generator's native fixed-width and dependent-length constructs rather than user callbacks where possible.

The production entrypoints SHOULD augment fields with 3D `on-success` or `act` actions that write decoded integers and field pointers to caller-provided out-parameters. For example, the frame entrypoint can write the decoded `Seq` and `KeyId` values to `mutable UINT64*` outputs and write the protected payload's `field_ptr` to a `mutable PUINT8*` output. This makes field selection and integer decoding part of the generated validator rather than reimplementing fixed offsets in Rust.

EverParse/3D generates C validators that are verified for memory safety, arithmetic safety, functional correctness with respect to the 3D format, no heap allocation, and double-fetch freedom within the validator. Its action language can pass validated scalar values and pointers to fields back to caller code, and its verified write footprint covers the explicit action outputs. The 3D documentation is at <https://project-everest.github.io/everparse/3d.html>, and its action language is documented at <https://project-everest.github.io/everparse/3d-lang.html#actions>.

## Candidate C: the custom flat format generated by Vest

Vest is a high-assurance parser and serializer generator for Rust. A `.vest` format description is compiled to safe Rust data types, parsers, serializers, and length functions, with proofs checked by Verus. Vest's stated guarantees include parser soundness and completeness with respect to the format specification, parser and serializer round trips, serializer non-ambiguity, memory and arithmetic safety, termination, and panic freedom. Generated parsers can borrow fixed and tail byte fields without copying, and generated serializers can write directly into a caller-provided buffer.

The custom flat encoding described for Candidate B is also the proposed Vest encoding; only its generated implementation changes. The format uses constants for the magic, version, and kind, fixed arrays for cryptographic fields, little-endian `u64` values for identifiers and sequences, and one tail-consuming protected payload. These constructs are directly represented by Vest's DSL. The authoritative `.vest` syntax MUST be validated with the pinned compiler, but its conceptual form is:

```text
InitKex =
    const 0xbc || const 1 || const 1 ||
    bytes[33] || bytes[98] || bytes[98] || bytes[1249]

CryptoFrame =
    const 0xbc || const 1 || const 3 ||
    u64le || u64le || tail(minimum-length = 81)

KexResponse =
    const 0xbc || const 1 || const 2 ||
    u64le || bytes[32] || bytes[32] || bytes[1088] || CryptoFrame
```

The spike MUST confirm how the pinned Vest version expresses the minimum tail length and a nested tail-consuming structure. If a length refinement is unnecessarily costly or unsupported, Vest may parse the remaining bytes as a tail and leave the existing cryptographic layer to reject protected payloads shorter than 81 bytes, provided the top-level façade still rejects structural prefixes and requires exact input consumption. No length field should be added solely to accommodate the generator unless measurement shows that it reduces deployed code size.

Vest removes Candidate B's internal C ABI, raw out-parameters, returned field pointers, and Rust reconstruction of C-projected data. It also generates the serializer, so parser/serializer correspondence is verified rather than established only by tests and review. Proof and ghost code are erased, and an application can compile and use the generated Rust without running Verus during an ordinary build. The deployed artifact still contains the executable combinators and any retained Vest runtime support, so these benefits do not establish a code-size advantage over specialized 3D C.

Vest remains an early-stage research project with incomplete documentation and no stable release series. The generator, Vest library, Verus, `vstd`, Z3, and Rust compiler compatibility therefore require explicit pins and a reproducible verification environment. The spike MUST verify compatibility with beaconcrypt's Rust 1.96 baseline, supported targets, Rust edition, feature combinations, release LTO settings, and published-crate packaging. Vest is documented at <https://github.com/secure-foundations/vest>, and its design and guarantees are described in the USENIX Security 2025 paper at <https://tracycy.com/papers/vest-usenix-security25.pdf>.

## Parser, projection, and serializer trust boundaries

Vest offers the smallest application-level trust boundary of the three candidates. The generated safe Rust parser and serializer receive the Vest/Verus guarantees, and borrowed fields remain tied to the Rust input lifetime without crossing an internal FFI boundary. The project still trusts the correspondence between the intended format and the `.vest` description, Vest's lowering and small formal property definitions, Verus, `vstd`, the Rust compiler, and the handwritten semantic façade that maps generated values into beaconcrypt-core inputs. Allocation behavior, ratchet transactions, public C/Go/Python buffer contracts, and cryptographic correctness remain outside the codec proof.

The Vest façade MUST require the reported consumed length to equal the complete input length at every top-level entrypoint. A successful prefix parse is not a successful beaconcrypt message parse. A tail field is expected to consume the remainder, but the explicit equality check remains part of the reviewed façade and its tests. The generated nested frame in a `KexResponse` MUST be returned as a typed value from the same parse rather than reparsing an opaque byte string.

3D normally describes its entrypoints as validators rather than general typed parsers or serializers, but actions can project validated fields into caller-provided outputs during the same generated pass. A custom-format implementation would therefore contain three distinct pieces:

1. Generated C validates the complete byte slice and uses specification-defined actions to return decoded integers and pointers to validated byte fields.
2. A small Rust FFI façade checks the generated result, binds returned field pointers to the input lifetime, and exposes borrowed typed views.
3. A small safe-Rust serializer allocates the exact size and writes the header, fixed fields, little-endian integers, and variable tail.

The validator and its local actions receive the generated 3D proof. The Rust FFI façade and serializer remain adapter code, and the project MUST NOT describe the complete codec as formally verified merely because validation and action execution are verified. The generated validator's double-fetch property also does not automatically cover a later Rust read through a returned field pointer; the EverParse documentation assigns preservation of that property to the application after `field_ptr` escapes.

This residual boundary is reasonable only if it is kept deliberately small:

- Field offsets and integer decoding MUST remain in the `.3d` specification and its actions rather than being duplicated in Rust.
- Out-parameters MUST be initialized before the call and ignored unless the generated entrypoint reports validation success and complete input consumption, because actions may have written a prefix of outputs before a later field fails.
- The Rust façade MUST range-check every returned pointer and fixed length against the original input before constructing a slice, then expose fixed-width fields as `&[u8; N]` and the variable tail as one lifetime-bound slice.
- The action-enabled entrypoint MUST return the nested `CryptoFrame` values from a successful `KexResponse` parse so registration does not validate or project the same bytes twice.
- Serialization MUST calculate the exact output length with checked arithmetic, allocate once, fill every byte, and contain no fallible branch after ratchet material has been consumed other than allocation failure handled with the existing semantics.
- Serializer output MUST always pass the generated validator and decode to the original semantic values.
- Accepted parser inputs MUST reserialize byte-for-byte identically, establishing canonicality for the implemented projection even though this correspondence is tested and reviewed rather than proved by 3D.
- FFI entry points MUST uphold Rust's immutability requirements for the duration of validation and use of returned field pointers, or copy attacker-owned input once before parsing, so a foreign caller cannot mutate bytes between validation and cryptographic use without violating an explicit API contract.

If verified parser/serializer inversion is a hard requirement rather than verified input validation, use Vest or EverCDDL. Writing a LowParse/F* format with parsers and serializers and extracting it through KaRaMeL could retain the flat encoding, but it is a substantially larger proof and maintenance project than a Vest or 3D description.

## Code-size assessment

The custom format is likely to minimize deployed code size for four reasons:

- Each validator recognizes one linear layout with constant offsets and at most one length-dependent tail.
- Integer decoding is two fixed little-endian loads rather than canonical CBOR major-type processing.
- Serialization is direct copying and does not need a generic object representation or CBOR sizing pass.
- The Cap'n Proto runtime and generated schema machinery can be removed entirely.

Wire-size savings are secondary. `InitKex` is dominated by its 1,249-byte signed ML-KEM key, and custom encoding saves only a handful of bytes compared with deterministic CBOR. The material benefit is expected to be executable size, compile time, and a smaller attack surface.

The expected code-size advantage is not yet demonstrated. Before selecting the format, implement three isolated spikes against the same semantic test vectors:

- Spike A generates only the three EverCDDL Rust codecs and a minimal façade.
- Spike B generates only the three action-enabled 3D C entrypoints and adds the complete Rust FFI façade and safe-Rust serializer.
- Spike C generates the three custom-flat-format Vest Rust codecs and adds only the semantic Rust façade and complete-input checks.

For all three spikes, build `beaconcrypt` with the same clean release command and record the stripped file size, `size` text/data values, and symbol-level contribution using `cargo bloat` or an equivalent link map. Measure default Rust, beacon-only, server-only, C/Go binding, and Python binding artifacts because dead-code elimination differs by crate type and exported API.

The comparison MUST include all support code that ships in the binary, including generated helpers, C wrappers, Rust FFI shims, error handlers, Vest combinators and runtime dependencies retained after linking, and any CBOR runtime copied into generated Rust. Generator binaries and proof-time dependencies do not count toward deployed code size, but their pinned version and regeneration cost must be documented separately.

Adopt the custom format only if it produces a material reduction in the target deployment artifacts. A suggested decision threshold over EverCDDL is at least a 10% reduction in the codec-attributable text size or at least 16 KiB in the final constrained artifact; the actual deployment owner MAY replace this threshold before the spike begins. Prefer Vest over 3D when Vest is within 16 KiB in the final constrained artifact because the generated serializer and removal of the internal C/FFI boundary materially reduce residual trust and integration complexity. Prefer 3D only when it demonstrates a larger deployed-size advantage that the deployment owner considers worth that boundary.

## Recommended architecture

Subject to the size spike, prefer the custom flat format generated by Vest. It matches the unusually simple layouts, keeps the implementation in safe Rust, and generates both sides of the codec with verified correspondence. Keep action-enabled 3D as the minimum-size fallback if its final artifact is materially smaller, and keep EverCDDL as the fallback if the Vest toolchain cannot support the required targets or if using a standardized deterministic encoding becomes more important than the flat format.

For Vest, add the following repository structure:

```text
beaconcrypt/src/schema/beaconcrypt_wire.vest
beaconcrypt/src/wire.rs
beaconcrypt/src/wire/generated.rs
```

The exact generated filename should follow the pinned Vest compiler. Generated Rust MUST be checked in, and normal Cargo builds MUST compile the checked-in module without invoking Vest, Verus, or Z3. Do not generate production sources from `build.rs`. A regeneration target should generate into a temporary directory, verify the result, and compare it byte-for-byte with the checked-in module. The build should depend only on the minimum runtime crates actually referenced by generated code, with default features disabled where supported and every version pinned.

If 3D wins the size gate, use `beaconcrypt/src/schema/BeaconcryptWire.3d` plus checked-in generated C and headers under `beaconcrypt/src/wire/generated/`, compiled through a narrowly configured build dependency. Normal Cargo builds in that configuration MUST NOT invoke EverParse, F*, KaRaMeL, or Z3.

`wire.rs` should expose only semantic façade functions:

```rust
fn encode_init_kex(fields: InitKexFields<'_>) -> Option<Vec<u8>>;
fn decode_init_kex(input: &[u8]) -> Option<InitKexRef<'_>>;
fn encode_crypto_frame(frame: CryptoFrameFields<'_>) -> Option<Vec<u8>>;
fn decode_crypto_frame(input: &[u8]) -> Option<CryptoFrameRef<'_>>;
fn encode_kex_response(fields: KexResponseFields<'_>) -> Option<Vec<u8>>;
fn decode_kex_response(input: &[u8]) -> Option<KexResponseRef<'_>>;
```

Generated Vest types and combinators, or generated C symbols and raw out-parameters in the 3D fallback, MUST remain private to this module. Protocol code must not depend on generated names, format offsets, raw pointers, or generator-specific integer representations.

## Ratchet and registration integration

Refactor frame construction so `seal_frame` first produces a private semantic value containing `seq`, `sender_kid`, and the protected payload. Established-message APIs serialize it as a standalone frame. Registration response construction embeds the same semantic frame directly in `KexResponse` rather than serializing a frame and then wrapping it as an opaque blob.

Refactor frame opening into parsing plus a shared `open_parsed_frame` helper. Standalone receive parses a `CryptoFrame`; registration finish obtains the already validated nested frame from `KexResponse` and opens it without a second format parse.

Preserve the existing transaction boundaries:

- `InitKex` serialization MUST succeed before the beacon publishes `InitSent`.
- `KexResponse` serialization MUST succeed before the server commits the assigned key ID and peer.
- Malformed input MUST be rejected before any protocol or ratchet mutation.
- A failed receive MUST remain exactly state-neutral under the maintained receive contract.
- Frame serialization failure after send material allocation MUST preserve the currently documented send-material consumption behavior unless the core transaction is separately redesigned and proved.

The CBOR or custom integer encodings MUST NOT replace the eight-byte little-endian assigned-ID prefix inside the initial encrypted plaintext. The CTX commitment MUST continue to use the core-produced little-endian sequence and sender-ID transcript, independently of the outer wire representation.

## Toolchain and regeneration

Pin the selected generator and its complete proof environment through the repository's locked proof tooling. For Vest this includes the Vest compiler and library, Verus, `vstd`, Z3, and the compatible Rust toolchain. For EverParse this includes the selected release or commit and its F*, Pulse, KaRaMeL, and Z3 environment. Add a regeneration target that writes into a temporary directory, verifies and generates or extracts the specification, and compares every generated source byte-for-byte with the checked-in copies.

Do not use EverParse's weak or hash-only checking modes as the verification gate. CI MUST actually regenerate and verify when the schema, generator pin, or generated output changes. Ordinary builds may use checked-in generated sources without installing the proof toolchain.

Extend the reviewed inventory so it independently discovers `.vest`, `.3d`, or `.cddl` specifications, the generator pin, regeneration scripts, generated wire sources, any generated headers, runtime dependencies, and the handwritten façade. Replace the existing `*.capnp`-specific schema inventory rather than deleting the schema tripwire.

Review generated artifacts rather than silently accepting regeneration. Record the EverParse version, invocation, input hashes, generated diff, and any code-size change in the implementation completion document and pull request.

## Implementation order

1. Pin the Vest and EverParse inputs needed for reproducible spikes and build all three code-size candidates without changing production call sites.
2. Select Vest, 3D, or EverCDDL using the measured deployment artifacts, target compatibility, and trust-boundary decision above.
3. Add the authoritative schema, checked-in generated code, regeneration target, and private Rust façade.
4. Add codec round-trip, canonicality, fixed-vector, malformed-input, truncation, extension, and full-consumption tests while Cap'n Proto remains in production.
5. Refactor `CryptoFrame` construction and opening around private semantic frame values.
6. Switch `InitKex`, `CryptoFrame`, and `KexResponse` together because mixed-format compatibility is not required.
7. Remove the `capnp` and `capnpc` dependencies, Cap'n Proto generation from `build.rs`, generated module declarations, all three `.capnp` schemas, and Cap'n Proto-specific test helpers.
8. Update protocol documentation, formal-verification analysis, trusted-boundary documentation, reviewed inventory, examples, and completion records.
9. Run the full validation and mutation suites and review every generated and known-answer artifact diff.

## Test plan

Codec tests MUST cover:

- Round trips for minimum and representative messages, `0`, `1`, and `u64::MAX` identifiers and sequences, and every fixed cryptographic field width.
- Rejection of every truncated prefix and fixed field, every appended byte, every successful prefix parse that does not consume the complete input, wrong magic, wrong version, every wrong kind, undersized protected payloads, and response inputs whose nested frame is malformed.
- Byte-for-byte canonical reserialization of every accepted input.
- Serializer output acceptance by the generated validator for property-generated semantic values.
- Mutation of every header, integer byte, fixed field, ciphertext byte, AEAD tag byte, and commitment byte while checking the appropriate format or cryptographic rejection layer.
- Registration success, authentication failure, replay, wrong-server binding, wrong assigned-ID binding, malformed input, ratchet rollback neutrality, out-of-order receive, replayed frame, and sequence-window boundaries.
- Identical semantic behavior through Rust, C, Go, and Python byte-buffer APIs.

Fuzz the generated entrypoints and the complete `parse or validate -> project -> serialize` façade. Seed fuzzers with valid minimum and maximum-width integer encodings, all prefix truncations, trailing extensions, and nested response/frame boundary cases. Generated acceptance followed by façade projection failure is always a bug.

## Required validation

Run:

```sh
cargo fmt --all --check
cargo clippy --workspace --all-targets --all-features -- -D warnings
cargo test
cargo check -p beaconcrypt --no-default-features --features pqxdh,beacon --lib
cargo check -p beaconcrypt --no-default-features --features pqxdh,server --lib
cargo build -p beaconcrypt --release --features gobinds
go test -race ./...
uv run maturin develop --uv
uv run pytest tests
make -C beaconcrypt-core verify
make -C beaconcrypt-core check-inventory
```

After each substantial code addition, run the complete mutation suite and fix every missed or timed-out viable mutant before considering the work complete.

## Formal claims and documentation

For the Vest custom format, document that the generated parser and serializer are verified against the `.vest` specification with Vest's stated guarantees. Retain the intended-format-to-specification correspondence, generator lowering, Verus and `vstd`, Rust compiler correctness, linker behavior, allocation, full-input-consumption check, and façade-to-core correspondence in the residual trusted boundary.

For the 3D custom-format fallback, claim only that the generated validator and its explicit extraction actions are verified against the 3D layout specification with EverParse's stated guarantees. The Rust FFI façade, serializer, C ABI invocation, Rust/C compiler correctness, linker behavior, allocation, lifetime and immutability assumptions for returned field pointers, and correspondence from façade values to core inputs remain reviewed adapter obligations unless separately proved.

For EverCDDL, document the generated parser and serializer guarantees and deterministic-CBOR assumptions, but retain generated-code extraction, compiler correctness, façade-to-core correspondence, allocation, and FFI behavior in the trusted boundary.

Update `doc/formal-verification-analysis.md` with a plain-English explanation of the selected schema, generated guarantees, residual trust, and why no cryptographic transcript changed. Update `beaconcrypt-core/proofs/trusted-boundary.md` and `reviewed-inventory.txt` so the new schema, generated output, build integration, and façade cannot change unnoticed.

## Decision

The custom flat format makes sense for beaconcrypt and is the provisional recommendation because the layouts are linear, mostly fixed-width, already semantically typed by the core, and used through message-oriented byte-slice APIs. Vest is the preferred implementation candidate because it keeps parsing and serialization in generated verified Rust, supports borrowed fixed and tail fields, and avoids both a general serialization format and the internal C/FFI boundary required by 3D.

The recommendation is conditional on the isolated spike demonstrating acceptable deployed code size and the pinned Vest toolchain supporting every required build target. If Vest is within 16 KiB of 3D in the final constrained artifact, prefer Vest for its smaller residual trust boundary. If Vest is materially larger and minimum size remains decisive, use action-enabled 3D after explicitly accepting its unverified Rust projection and serializer boundary. Use EverCDDL deterministic CBOR if neither flat-format generator meets the compatibility or maintenance requirements, or if a standardized deterministic representation is preferred despite its expected size cost.
