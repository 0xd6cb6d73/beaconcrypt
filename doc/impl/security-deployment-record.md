# Deployment boundary remediation record

## Changes and security impact

Added fallible `Beacon::try_new` and `Server::try_new` constructors and routed persistent/C/Python construction through them. Rust compatibility constructors retain explicit panic behavior; malformed foreign key/seed lengths now return the existing C/Go failure result or Python `ValueError`. Initialization and key-generation errors are propagated when the dependency reports them. No network-forgery property follows from this engineering change.

C buffers now wipe their entire allocation capacity through `zeroize` before deallocation, and Go temporary C input copies use volatile erasure before `free`. The public ownership convention and ABI remain unchanged. The regenerated C header changes only the destructor and constructor contracts; its diff has been reviewed. The Python stub was formatted with Black and documents constructor errors. The Rust example demonstrates fallible construction and the new persistence helper.

Added `ServerSnapshot::validate_successor` to validate envelope structure, same lineage, exact next generation including exhaustion rejection, and the complete parent digest. The binding store uses this check; the Rust sample store also invokes it. Tests include valid successors, malformed envelopes, wrong lineage, skipped/initial/exhausted generations and altered parent links. This catches malformed links within a conforming store and provides a reusable check to external implementations; it cannot authenticate or establish freshness for an attacker-controlled store.

Pinned the reviewed Rust wrapper to `libsodium-rs = "=0.2.4"`; the lockfile remains unchanged. `doc/deployment-boundary.md` records the resolved native archive hash, API assumptions, entropy requirements, supported validation configuration and platform limitations. Inspection confirmed the upstream wrapper's load-time panicking initializer, which remains a precise pre-API limitation even with fallible constructors.

## Validation evidence

The initial environment used Rust 1.95, lacked Cap'n Proto and GNU Make on PATH, and the installed Rust 1.96 toolchain's default lld wrapper referred to a collected Nix store path. Validation uses installed Rust 1.96 with `RUSTFLAGS='-C linker-features=-lld'`, Cap'n Proto 1.1.0 from the repository-pinned Nix package set, and GNU Make 4.4.1. This selects the available system linker without changing repository compiler flags. The pinned test-vector submodules were initialized at their recorded commits and are unmodified.

The full all-feature adapter Rust tests pass, including the new Rust and C constructor regressions. The initial workspace run caught constructor-sensitive source fixtures; those are being synchronized with their original substantive checks preserved. Final integrated mutation, binding, lint, feature and proof evidence will be recorded in the integration milestone rather than treating this development check as completion.

`python3 scripts/check_lean_panic_freedom.py` reconstructs 269 extracted-operation contracts. This is an inventory check; the integrated Lean build must check their certificates. No new proof or generated core extraction change is introduced by this workstream.

## Remaining obligations

The dependency can fail before our fallible constructors run; native RNG failure and allocation termination are not universally recoverable. Rust `new` remains a documented compatibility panic wrapper. Erasure covers owned native allocations and does not remove managed-language/application copies, old reallocations, snapshots or crash dumps. A real persistence store must independently supply protected current bytes/head, durable atomic CAS and rollback resistance. The single-process example and foreign checkpoint APIs do not supply those deployment properties. Windows native linkage and compatibility functions need platform-specific validation.
