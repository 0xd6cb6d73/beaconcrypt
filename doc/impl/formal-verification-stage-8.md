<!-- SPDX-License-Identifier: 0BSD -->

# Formal verification Stage 8 implementation record

## Result and scope

Stage 8 pins the complete proof-tool bundle and runs extraction plus every F*
and ProVerif gate in CI. The repository now owns a locked Nix flake, verifies
the exact tool identities before extraction, prevents Cargo or Nix lock-file
updates during verification, and rejects both tracked and untracked generated
artifact drift.

This stage is reproducibility and CI work. It does not change production Rust,
an F* theorem, a ProVerif primitive equation or process, or an expected query
classification. Re-extraction with the newly enforced Rust nightly is
byte-identical to the Stage 7 output.

The implementation is based on commit
`6d604d32f80a10dd379198b39c8775457298cb72`, which completed Stage 7. That
commit and its complete diff were reviewed before this work. In particular,
Stage 8 preserves the role-bearing signed X25519 layouts, the regenerated
Stage 6 F* lemmas, the three narrow production-backed ProVerif replacements,
the one-owner non-rollback replay refinement, and the exact baseline,
reachability, and compromise result policy.

## Review finding: the Rust frontend escaped the Stage 7 pin

Stage 7 entered hax's `ci-examples` shell through a revision-qualified GitHub
flake URL. The hax revision and that revision's transitive F* and nixpkgs locks
were stable, but the shell did not include hax's `packages.rustc`. Nix
therefore retained the caller's ambient rustc and Cargo on `PATH`. The Stage 7
artifacts were generated with rustc 1.97.1 rather than hax's declared
`nightly-2025-11-08` toolchain.

This was a reproducibility gap, not evidence of a semantic proof failure. The
two F* modules and the ProVerif library were regenerated in an isolated copy
with hax's Rust package first on `PATH`; all three files were byte-identical,
all strict F* obligations passed, and all ProVerif results matched.

The pinned nightly is deliberately scoped to the protocol-core proof shell.
The production workspace declares Rust 1.96, while the isolated core declares
Rust 1.85 and stays within the subset accepted by the hax frontend. A root
`rust-toolchain.toml` using Rust 1.93 would incorrectly lower the compiler used
for the application and was not added.

## Implementation map

| File | Responsibility |
| --- | --- |
| `flake.nix` | Extend hax's CI proof shell with hax's own Rust package, F*'s exact Z3 package, and the `rg` used by extraction checks. |
| `flake.lock` | Pin hax and every transitive source, including the Rust overlay, F*, and both nixpkgs revisions, by revision and NAR hash. |
| `crates/protocol-core/Makefile` | Enter the local locked shell, check tool identities and F* assumption policy, run cargo-hax with `--locked`, and reject tracked or untracked extraction drift. |
| `crates/protocol-core/proofs/fstar/Makefile` | Select the qualified Z3 4.15.3 executable explicitly while retaining strict generated and handwritten F* checking. |
| `.github/workflows/formal-verification.yml` | Run the complete regeneration and proof gate on a fixed Linux runner with read-only permissions and a bounded timeout. |
| `crates/protocol-core/README.md` | Document the hermetic commands, pins, CI behavior, and Stage 8 record. |
| `doc/formal-verification.md` | Mark Stage 8 complete and record the rollout result and remaining Stage 9 work. |

## Locked proof bundle

The local flake follows hax's own F* and nixpkgs inputs rather than resolving
parallel copies. Nix therefore evaluates one reviewed dependency graph. The
checked bundle is:

| Component | Checked identity | Pin provenance |
| --- | --- | --- |
| rustc | `1.93.0-nightly (843f8ce2e 2025-11-07)` | hax `nightly-2025-11-08` Rust package |
| Cargo | `1.93.0-nightly (636800288 2025-10-31)` | same Rust package |
| hax | `0.3.7` | revision `5b0ba8be6da3c313fdfed1c19dd0f0721a29f4b3` |
| F* | `2025.10.06~dev` | revision `7b347386330d0e5a331a220535b6f15288903234` |
| Z3 | `4.15.3` | newest solver shipped by the same locked F* input and qualified against this proof corpus |
| ProVerif | `2.05` | hax's package from nixpkgs revision `3de8f8d73e35724bf9abef41f1bdbedda1e14a31`, with hax's reviewed division-by-zero patch |

The hax and F* binaries do not embed useful source revisions in their version
banners (`commit=unknown` and `commit=unset`). `flake.lock` is therefore the
authoritative source-revision record, while `make check-toolchain` verifies
that the corresponding runtime versions are the binaries actually selected.
It runs before either backend in both the complete and ProVerif-only paths and
prints the six checked identities into the CI log.
The effective F* and ProVerif checker commands and the F* flag set use GNU
Make's `override` assignments, so environment or command-line variables cannot
replace them after the identity and policy gates run.

F*'s package wraps several supported solver versions. The F* proof flags now
include `--z3version 4.15.3`, and the shell exposes that same
`z3-4.15.3` executable for the version gate. This prevents a future F* default
change from silently selecting another bundled solver.

The flake also supplies ripgrep. Stage 7's ProVerif placeholder and
required-item checks called `rg` but inherited it from the developer or runner
image; it is now part of the locked environment instead.

## Latest-compatible qualification

The proof stack was audited against its upstream releases on 2026-08-02. A
version was advanced only when the complete extraction and proof corpus
accepted it; an upstream version number alone was not treated as compatibility
evidence.

| Component | Qualification evidence | Decision |
| --- | --- | --- |
| hax and `hax-lib` | The locked hax revision was still upstream `main`, whose workspace release was 0.3.7. The CLI and library are source-coupled, and the crate remains pinned exactly to the CLI release. | Keep hax `5b0ba8b` and `hax-lib` 0.3.7. |
| Rust frontend | That hax revision declares `nightly-2025-11-08` and uses compiler-private APIs. A newer ambient compiler is not a supported substitute. | Keep the hax-declared rustc and Cargo pair. |
| F* | All three subsequent official releases were exercised. The first, v2025.12.15, rejects hax's `Core_models.Bundle.fst`; v2026.05.17 rejects `Hax_lib.fst`; and v2026.07.24 both removes the explicit `--cmi` mode and rejects `Hax_lib.fst` after adapting the invocation. | Keep v2025.10.06, the latest release compatible with the locked hax proof libraries. |
| Z3 | The locked F* package supplies 4.8.5, 4.13.3, and 4.15.3. The complete generated and handwritten F* corpus was run with 4.15.3 and every verification condition discharged. Newer upstream solvers are outside this F* release's supported bundle. | Advance from 4.13.3 to 4.15.3 and select it explicitly. |
| ProVerif | 2.05 remained the latest official release. Hax's package applies its required reviewed division-by-zero patch. | Keep 2.05 from hax's graph. |
| Transitive Nix inputs | The root flake follows the current hax revision's F* and nixpkgs inputs. Updating crane, rust-overlay, nixpkgs, or another transitive input independently would create a toolchain combination not tested by hax. | Keep the integrated upstream lock graph rather than mixing individually newer inputs. |

The new workflow dependencies received the same scoped review. Checkout is
pinned to v7.0.1, Determinate Nix to v3.21.9, and Cachix to v17, each by an
immutable commit. Those were their current compatible releases on the audit
date. The Nix action's optional KVM setup is disabled because this proof shell
does not use virtual machines, and checkout does not persist credentials.

## Lock and proof gates

The outer verification targets invoke the local flake with
`--no-update-lock-file`. A missing or stale lock is an error rather than an
implicit dependency refresh. Both cargo-hax commands pass `--locked` to their
internal Cargo builds, preventing dependency resolution from changing
`Cargo.lock` during extraction.

After the identity gate, `make verify-in-shell` retains the Stage 7 order:

1. regenerate the F* extraction;
2. reject `assume` or `admit` in repository-owned F* sources and reject lax or
   admitted-query flags in the F* checker;
3. check generated and handwritten F* modules strictly;
4. regenerate the ProVerif extraction;
5. reject placeholders and require all three production-backed replacements;
6. require all eleven baseline security queries to be true;
7. require all five reachability negations to be false; and
8. require the compromise split to remain exactly two true and three false.

Each ProVerif scenario retains its 240-second timeout and the strict result
classifier. False reachability negations and the three reviewed compromise
attacks are required results; every missing, substituted, unproved,
inconclusive, or differently classified query fails the job.

`make check-generated` runs that full suite and then compares both generated
directories to Git. It now performs two complementary checks: `git diff`
catches changes and deletions of tracked output, and `git ls-files --others`
catches newly generated untracked files. Ignored proof caches remain outside
the artifact comparison.

## Continuous integration

The dedicated `Formal verification` GitHub Actions workflow runs for pushes
and pull requests targeting `main`, merge-queue checks, and manual dispatch.
It uses `ubuntu-24.04`, read-only repository permission, and a 60-minute job
timeout. The workflow actions are referenced by immutable commits, including
the Nix installer release and Cachix action. It disables unused KVM setup and
does not leave Git credentials in the checkout.

The cache configuration follows hax's upstream CI: it pulls from the public
`hax`, `fstar-nix-versions`, and `z3-nix-versions` caches and cannot push.
Nix verifies cache signatures and store identities, while the flake lock
verifies input revisions and NAR hashes. The only proof command in the job is:

```sh
make -C crates/protocol-core check-generated
```

That command selects the locked shell itself, so CI and the documented local
workflow use the same entry point. The mutable runner image is not a source of
proof binaries: the locked shell supplies them, and the version gate fails if
an ambient tool changes any checked version banner.

## Validation performed

The final implementation was validated with:

```sh
make -C crates/protocol-core check-generated
cargo fmt --all -- --check
cargo test --workspace --all-targets --locked
nix --extra-experimental-features 'nix-command flakes' flake check \
  --no-update-lock-file --no-build --all-systems path:.
nix --extra-experimental-features 'nix-command flakes' shell \
  'github:nixos/nixpkgs/3de8f8d73e35724bf9abef41f1bdbedda1e14a31#actionlint' \
  -c actionlint .github/workflows/formal-verification.yml
git diff --check
```

The locked-shell identity check reports the exact versions listed above. The
complete pipeline regenerates both backends, discharges all generated and
handwritten F* obligations, and obtains the Stage 7 classifications of eleven
true baseline results, five false reachability negations, and the compromise
split of two true and three false. The generated F* PQXDH and ratchet modules
and generated ProVerif library remain byte-identical to the reviewed Stage 7
artifacts, and the tracked/untracked artifact gate exits successfully. All
four declared proof-shell derivations evaluate, actionlint accepts the workflow,
and the Rust workspace runs 168 tests with no failures or ignored tests.
The complete F* corpus also passes with the selected Z3 4.15.3; the incompatible
post-v2025.10.06 F* trials fail inside hax's own proof libraries before reaching
the repository lemmas, establishing the recorded compatibility boundary.

The final generated identities remain:

| Generated artifact | Lines | SHA-256 |
| --- | ---: | --- |
| F* PQXDH module | 932 | `d73891ba4ac6818a5a1d8fdb3f3fe8daaccb077489ee0fd428519c8eabd90941` |
| F* ratchet module | 360 | `7c8fcf79aa084d032742462dcdf23bcb0367f5711010eba4688c8bd71821afd7` |
| ProVerif library | 358 | `81ef938f5726bb5f6fcf482b29199c06e66c7805caac0b5a73414f653038f386` |

## Remaining rollout work

Stage 9 remains: maintain a reviewed inventory of every opaque Rust function,
primitive assumption, adapter refinement, generated-code exception, and
handwritten backend fragment, and make unreviewed inventory drift a CI review
failure. Stage 8 does not expand the proof boundary or remove any limitation
recorded in the Stage 6 and Stage 7 implementation records.
