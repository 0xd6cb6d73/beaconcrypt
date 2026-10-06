# Raw-accept source cut and native KEM origin

Status: four modules and nine statements pass direct single-module Lean 4.34 checks with exact `#print axioms` guards that permit only `propext`, `Classical.choice` and `Quot.sound`. The root module also checks against the retained artifacts. These modules have not yet been independently reviewed. They are source-correspondence components; they do not join the authenticated root theorem and give no probability bound of their own.

## Modules and statements

| Module | Statements | Content |
| --- | --- | --- |
| `PqxdhRegistrationJointAcceptCut` | `scan_finish`, `scan_bound`, `selected_bound` | Suspend the adversary's adaptive source14 program immediately before its selected raw `.accept raw` request and resume it unchanged. |
| `PqxdhRegistrationJointAcceptCutSource` | `commands_bind`, `commands_resume`, `pending_command` | Apply that cut to the exposed complete command compiler with owners and native state retained. |
| `PqxdhRegistrationJointNativeKemOrigin` | `selected_source`, `key_or_failure` | Connect the selected original candidate at a fresh generated owner to that owner's native KEM public key, or to the existing native tuple-origin failure event. |
| `PqxdhRegistrationJointCutVerification` | `verified_pure` | Show that the attached verification step in the exposed Server prefix is the pure public source verification. |

## What is proved

`AcceptCut.scan work index` walks the adversary program over `PqxdhRegistrationJointRevealSchedule.Spec`. It forwards every query once and passes each reply to the original continuation. It counts only raw `.accept raw` requests, and it suspends before the zero-based `index`th one, keeping the raw bytes and the original optional-answer continuation. The scan never reads a reply to decide whether to count, so rejected attempts are counted as well. `scan_finish` is the program equality `scan work index >>= finish = work`; because it is an equality of oracle programs, it holds under every later interpreter, including the native state and private histories. `scan_bound` and `selected_bound` carry every `IsQueryBoundP` cap of `work` to the scan and to `selected`, which packages the caller-supplied public owner address with the suspended raw bytes. If the program completes before the selected request, `selected` returns a fixed public fallback without examining any state. No query is added, and continuation work that the scan omits is neither charged nor used to offset earlier calls.

`AcceptCutSource` states the cut on `PqxdhRegistrationJointKemEncapsulation.commands`, which is the actual source14 command compiler with only its encapsulation operation exposed. `commands_bind` shows that this compiler respects program composition and passes on the complete owner registry and native state. `commands_resume` shows that compiling the scan and then compiling the resumed remainder from the resulting state gives the original compiled execution. `pending_command` shows that, at a pending cut, the next computation is the exposed `KemEncapsulation.accept` on the same raw bytes and native state. The original continuation then receives the actual optional reply, and the owner registry is unchanged.

`CutVerification.verified_pure` uses the exposed prefix handler, which is the encapsulation-exposing `prefixImpl` composed with the Server prefix compiler. From any consumed-registration list, simulating `PqxdhServerRootPreparation.verifyInput raw` equals `pure (PqxdhRegistrationJointRawSignatures.verified setup codec checks raw, consumed)`. The verification therefore makes no oracle query, leaves the consumed list unchanged and does not touch pools, signing logs or reveal state. The equality holds before any interpreter is chosen for the exposed encapsulation hook or for a KEM challenger.

`NativeKemOrigin.selected_source` shows that, when the initialized report source finishes with outcome `encoded`, the candidate that `PqxdhRegistrationJointFinalCandidate.selected` reads from the adversary's output equals the candidate parsed from the outcome's original raw bytes. Reattaching private pools does not change it. `key_or_failure` covers every result in the support of `PqxdhJointPhase1Reports.run` over `PqxdhRegistrationJointReportCompiler.initialized`. Its premises are that the addressed owner is generated and unrevealed, that the owner has a source identity key, and that the selected candidate verifies under that key. It concludes one of two cases. In the first, the decoded tuple occurs in the owner's literal chronological signing transcript, and the owner's native KEM slot holds the decoded PQ public key. In the second, `PqxdhRegistrationJointNativeOriginEvent.Failure` holds. The integrated `NativeOriginEvent.transport` already bounds that event by the ordinary final-report detector with coefficient one. No premise requires an honest incoming tuple.

## What is not proved

The next join is still open. It is to instantiate this cut inside the initialized report compiler, so that `AcceptCut.selected work index owner fallback` becomes the `program` argument of `key_or_failure` and of the existing `PqxdhRegistrationJointFinalCandidate` machinery. The raw-accept ordinal must stay distinct from the encapsulation ordinal of `PqxdhRegistrationJointKemCut`. A request rejected before encapsulation makes the two ordinals differ, and no theorem here relates them. The owner must be selected by a public source handle or index, never by comparing a secret key. The join must use `verified_pure`, `key_or_failure` and the native-origin coefficient-one transport, and it must keep all source and private state and every source query class. None of the modules here proves that the pending raw accept reaches encapsulation, that its verified PQ field equals the selected challenge key, or any selection or freshness loss.

Handoff item 1 also remains open. The authenticated root theorem still needs the actual source14 accept/report execution to be joined to the retained Phase-1 EUF reduction and the selected one-key ML-KEM challenge. Its final event must cover honest unchanged candidates, honest changed candidates, attacker-owned candidates and rejection, without an honest-target premise. The candidate/KEM value must also stay out of the KDF distinguisher's public context. These modules add no KDF, Extract or root-input statement.

Handoff item 7 also remains open. The production/source boundary still lacks its acceptance, root, record, rollback/replay, publication and associated-data joins. These modules are statements about the existing Lean source14 model, not new Rust correspondence. Compiler correctness, storage, physical erasure, codec internals and native primitive internals remain external contracts. Persistence, snapshots and attacker access to running code remain outside the experiment.

## Assumptions and accounting

No primitive game, contract, axiom or premise is added. The only primitive-facing endpoint mentioned is the existing ordinary joint Ed25519/X25519 weak-EUF family that bounds the native tuple-origin failure. It is cited, not re-proved or strengthened. Symbolic constructor injectivity is not used. `scan` forwards each query exactly once and keeps every cap of the original program, so the existing source query classes and the all-reply resource bills of the native-origin and KEM-cut cohorts are unchanged.

## Evidence and reproduction

The evidence receipt is [`proof-receipts/registration-joint-accept-cut.json`](proof-receipts/registration-joint-accept-cut.json). It records the WIP source hashes, the final module hashes, both rounds of direct checks, the exact axiom output, the guard list, the root check and the focused inventory result. Each module was checked on its own, in dependency order, with:

```text
flock /tmp/bc-arc-scratch/lean.lock timeout 180 \
  /home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean \
  -j1 -M8000 --root=<worktree>/beaconcrypt-core/proofs/lean -o <scratch>/<module>.olean <module>.lean
```

`LEAN_PATH` is the retained artifact path recorded in the lane manifest. The inventory gate is `make -C beaconcrypt-core check-inventory SHELL=bash`, run in the locked minimal proof flake. Neither the full `lake build` nor the final verification matrix has been run for this change.
