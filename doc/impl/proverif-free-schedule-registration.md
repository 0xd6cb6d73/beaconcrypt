# Free-schedule ProVerif registration (fs-registration)

This guide records stage P1 of the staged ProVerif plan for audit findings F2, F13 and F11: the shared free-schedule (fs) vocabulary, the `fs-registration` scenario, its serial verification group, its result checker, the repository-wide ProVerif declaration check, and the transcript-fidelity and inventory gates that pin them. The plain-English explanation of every result is in [What beaconcrypt's formal verification proves](../formal-verification-analysis.md#free-schedule-proverif-registration-fs-registration), and the meaning of every fs event as a Rust API outcome, with what each claim therefore says about Rust, is in [the fs event-meaning reference](../proverif-fs-event-meaning.md).

Every fs result is a symbolic result (Dolev-Yao attacker, free constructors, ideal hash, KDF and AEAD) for a bounded process. None of them is a computational bound. Cap'n Proto is out of scope: messages are abstract byte strings that each side can decode. libsodium is a black-box functional contract. Persistence is out of scope, and the proof Server has perfect key management and no backup or restore (owner decision OD2). Reading the results as statements about the Rust API rests on the paper arguments L1, L5 and L6 of the plan ([Pending paper arguments](#pending-paper-arguments)). L6 was reviewed at the start of stage P2; L1 and L5 are pending, and until they are written and reviewed, each result is cited as a symbolic result for the fs process, which models the Rust interface under these pending abstraction steps.

## Basis and decisions

The Rust basis is branch `codex/full-proof-composition` at `533901f`, whose Rust sources are identical to `959cdab`, the basis of the plan and of the P0 spike. The Rust code is authoritative: where the model and Rust differ, the model follows Rust. The decisions applied here are those of gate G0 and the owner:

- OD1: bounded results are the ProVerif deliverable; there is no unbounded tier.
- OD2: two Server objects built from one seed are one Server identity; replay claims are per live Server state, and R4 is an expected consequence.
- OD7: at most 1800 s per target, about 3 h for the whole fs group, run serially; each run may use a 10 GiB address space, with the fs group running alone on the machine.
- OD11: the serial step-by-step run is the final verification record.
- Theory `crypto.pvl` (G0 section 4), a self-contained `fs-common.pvl` (G0 section 5), the single selection heuristic nx with its documentation paragraph, the reg-v2 process shape, and the bound K_reg = 3 for the security results.

## Pending paper arguments

The ProVerif verdicts are exact statements about the fs process. Their Rust readings rest on three paper arguments of the plan (section 6); L1 and L5 are not yet written, and L6 was reviewed at the start of stage P2. The plan requires citing fs results as symbolic results for the fs process under these abstraction steps, marked pending, until they are reviewed (OD10). G0 dropped L7 and L8 with tier U; L2, L3 and L4 concern the record scenarios.

- **L1, Server decomposition and accept/build scheduling: not yet written.** It must cover (i) accept and build made adjacent; (ii) builds in another order than the accepts, which renames key IDs in build order; (iii) an accept that is never built, which is the drop; (iv) a `RegistrationOutput` accepted by one live object and built by another live object with the same identity key and `server_kid`, which `pqxdh.rs:853-858` accepts because it checks only these two values, and in which the key ID comes from the building object's counter; (v) failures between the registration ID and the insertion, which leave the state unchanged. OD2 does not settle case (iv): the model runs unbounded live objects with one identity (R4 relies on this), but it never builds a token on another object than the one that accepted it, so this case stays open until L1 covers it.
- **L5, Beacon lifecycle: not yet written.** At most one signed bundle output per Beacon object (a failed bundle call, which may already have signed, outputs nothing and may be repeated), at most one finish, and a failed finish aborts for good and is never retried. The injectivity of A1, the single bundle behind R1' and model step 4 rely on it.
- **L6, event projection: written as a paper draft in P0, now maintained as [the fs event-meaning reference](../proverif-fs-event-meaning.md), and reviewed at the start of stage P2 ([review record](../proverif-fs-event-meaning.md#review-record)).** The event meanings below follow it.

Every Rust reading in this guide, and the Rust readings of all six security results, rest on L1, L5 and L6.

## Files

| File | Role |
| --- | --- |
| `beaconcrypt-core/proofs/pro-verif/fs-common.pvl` | Shared vocabulary of the fs family: the `fs_kid` and `fs_seq` bridges, five declarations copied verbatim from `environment.pvl`, the empty-slot and build constants, all eleven fs events of P1 with their meaning (P2 later added `FsReceivedFrame` and the frame field of `FsReceiveRejected`), and the heuristic nx |
| `fs-registration.pvl` | The Server object step macro `FS_REG_STEP`, the stop process and the honest Beacon, with one `@beaconcrypt-fs-fidelity` citation per step |
| `fs-registration-consumed.pvl`, `fs-control-nocheck.pvl` | The consumed-set test, and its negative control C-NOCHECK |
| `fs-registration-binding.pvl`, `fs-control-uks.pvl` | How the root input and associated data bind the Beacon identity, and the negative control C-UKS |
| `fs-registration-k1.pvl`, `-k2.pvl`, `-k3.pvl` | The step expansions for K_reg = 1, 2 and 3 and the main process |
| `fs-registration-<claim>.pv` (13 files) | One query per file: `a1`, `a2`, `r1`, `r1prime`, `r2`, `r3`, `r4`, `r5`, `s3-server`, `s3-beacon`, `w1`, `w2`, `w3` |
| `check-free-schedule.py` | Runs every target as its own ProVerif process, serially, and checks the exact expected result lines per class |
| `test-free-schedule-checker.py` | Regression test of the checker (receipts, manifest and process runner) |
| `declaration-allowlist.tsv` | Reviewed allowlist of every ProVerif heuristic, precision setting, output setting and `[precise]` input in the `.pv` and `.pvl` files under `proofs/pro-verif` and in the string literals of the Python files there |
| `beaconcrypt-core/tests/proverif_transcript_fidelity.rs` | Five new tests pin the fs wiring, citations, vocabulary, checker manifest and declaration policy |
| `beaconcrypt-core/Makefile` | `check-proverif-fs`, `check-proverif-fs-registration`, `PROVERIF_FS_TIMEOUT`, `PROVERIF_FS_ADDRESS_SPACE_KIB`, `PROVERIF_FS_LOG_DIR`, `PROVERIF_FS_SCENARIOS`, and the calls from `verify-in-shell` and `verify-proverif-in-shell` |
| `beaconcrypt-core/proofs/check-inventory.sh`, `reviewed-inventory.txt` | New file hashes and counts, and fs tripwires |

## Running

The fs group needs the machine to itself: each target may take up to 1800 s and a 10 GiB address space. In P1 the group held only fs-registration and one pass took about 45 minutes; since stage P2 it also holds the Server-to-Beacon record scenario and since stage P3 the Beacon-to-Server record scenario, and one pass of the whole group takes a little under three hours (the [b2s guide](proverif-free-schedule-records-b2s.md#results) records the current pass). Inside the locked proof shell, run:

```sh
make -C beaconcrypt-core check-proverif-fs
```

It runs the transcript-fidelity test, then the checker regression test and every fs-registration target, then the checker regression test again and every fs-records-s2b target, then the checker regression test again and every fs-records-b2s target, one ProVerif process at a time. `make -C beaconcrypt-core check-proverif-fs-registration` runs the fs-registration targets alone (2658.4 s of ProVerif time, about 44 minutes, in the latest pass). The checker applies the per-target timeout and the address-space limit (the equivalent of `ulimit -v`) to each ProVerif process itself and prints the time and peak resident memory of each run. Without a log directory the checker writes the ProVerif logs into a temporary directory `beaconcrypt-fs-logs-*` under `$TMPDIR`: it removes the directory after a successful run, and after a failure it keeps it, names the failing target's log in every error message and prints the directory. `make -C beaconcrypt-core check-proverif-fs PROVERIF_FS_LOG_DIR=<dir>` keeps the log of every target in `<dir>`. To run the checker directly, for one target or with kept logs and a TSV of times:

```sh
python3 beaconcrypt-core/proofs/pro-verif/check-free-schedule.py --scenario fs-registration --list
python3 beaconcrypt-core/proofs/pro-verif/check-free-schedule.py --scenario fs-registration --only A1 --log-dir /tmp/fs-logs --results /tmp/fs-results.tsv --timeout 1800 --address-space-kib 10485760
```

On a shared machine, run the fs group only when no other ProVerif, Lean or Rust build uses the memory, and never together with the parallel `check-proverif` roster.

## Model structure and Rust mapping

Unbounded Server objects share the one honest Server identity `SERVER_IDENTITY_SECRET` and own key ID `SERVER_KEY_ID`. Each object is a non-replicated chain of K_reg steps whose state lives in process variables: `kid_next`, the next key-ID offset (the object's build count plus one), and two consumed-ID slots. Unbounded honest Beacons run in parallel. The attacker builds its own identities with the public constructors `ed_public`, `sign`, `x25519_public` and `mlkem_public`, and the same Server code serves them. Every attacker input is `[precise]`.

Server step (one `get_shared_secret` call followed by an attacker-chosen build or drop):

| Model step | Rust |
| --- | --- |
| Read one attacker bundle | `beaconcrypt/src/server.rs:332-336` |
| Identity tag and key decode | `server.rs:337-342` |
| The three signature checks and the role tags in one tuple `let` | `server.rs:343-353`; `beaconcrypt-core/src/pqxdh.rs:325-345` |
| `init` = `VerifiedInitKex(identity, prekey, one_time, pq)` | `server.rs:347-353` |
| Registration ID `identity ‖ one_time` | `server.rs:354`; `pqxdh.rs:195-204`, hax replacement `pqxdh.rs:212-220` |
| Consumed check, `FsServerReplayRejected` on replay | `server.rs:355-360`; `pqxdh.rs:245-251` |
| Fresh ephemeral and KEM coins | `server.rs:368`, `:373` |
| Identity conversion and DH1-DH4; `FsServerAcceptFailed` when the prekey or the one-time key is not an X25519 public key, the only failures here under `crypto.pvl` | `server.rs:374-394` |
| Root input and root | `server.rs:395-414`; `pqxdh.rs:391-405` |
| Insertion into the consumed set, then `FsServerAccepted` | `server.rs:415-421` |
| Build: next key ID `fs_kid(kid_next)` | `server.rs:434-439`; `pqxdh.rs:838-844` |
| Prepare commit and associated data | `server.rs:440-458`; `pqxdh.rs:847-858`, `:877-880` |
| Fresh payload, binding, seal at sequence one with sender `SERVER_KEY_ID` | `server.rs:459-479` |
| Peer installed: `FsServerCommitted`, then the response is output | `server.rs:489-501` |
| Drop or failed build: ID stays consumed, counter unchanged | `server.rs:113-118` |

Beacon (one `get_registration_bundle`, then one `finish_registration`):

| Model step | Rust |
| --- | --- |
| Fresh identity, prekey, ML-KEM key and pinned Server key | `beaconcrypt/src/beacon.rs:65-83` |
| Fresh one-time key at bundle time | `beacon.rs:301-305` |
| `FsBeaconStarted`, then the signed bundle is output | `beacon.rs:335-357`, `:398`; `pqxdh.rs:304-321` |
| Decode the response, convert the Server identity, decapsulate, DH1-DH4 | `beacon.rs:402-449` |
| Response identity equals the pin | `beacon.rs:450-457`; `pqxdh.rs:545-547` |
| Root, receive chain, associated data from the pin | `beacon.rs:458-461`; `pqxdh.rs:552-555` |
| Frame sender `SERVER_KEY_ID`, sequence one, open | `beacon.rs:462-470` |
| Assigned-ID binding | `beacon.rs:476-484`; `pqxdh.rs:616-628` |
| Pin checks and commit: `FsBeaconEstablished` | `beacon.rs:493-509` |

The transcript-fidelity test `free_schedule_rust_fidelity_annotations_are_exact` holds the complete list of 59 citations. Each annotation has the form `(* @beaconcrypt-fs-fidelity key=... src=<path>:<first>-<last> anchor=<text> *)`; the test requires the exact list and order per file, a range of at most 40 lines, and that the first cited line starts with the anchor text. A Rust change that moves the first line of a cited range fails the test until the citation is reviewed again; a change inside a cited range that leaves its first line in place, for example a check inserted into the last range cited in a file, is not detected by this test.

## Model steps and their justifications

1. **Process-level lets (reg-v2).** The bundle parse and the four DH calls are process-level `let` bindings with one failure branch each. A `letfun` with internal `let` bindings has the same semantics, but ProVerif expands it into catch-fail chains with more branches; the P0 spike measured all its registration results in the process-level form. The order of checks and the events on each branch are those of Rust.
2. **Accept and build adjacent (pending L1).** `get_shared_secret` and `build_registration_response` are separate Rust calls. In the model a successful accept is followed at once, on the same object, by an attacker-chosen build or drop. The intended argument: reordering builds after other calls renames key IDs in build order; an accept never built is the drop; a failure between accept and commit consumes the ID and leaves the counter unchanged, which is the drop branch. It is obligation L1 of the plan, which is pending and not yet written. A `RegistrationOutput` built on another live object with the same identity key and `server_kid` (`pqxdh.rs:853-858` checks only these) gets its key ID from the building object's counter; the model never builds on another object, and OD2 does not exclude such runs, so this case (iv) is open until L1 covers it.
3. **No separate all-zero check.** Under `crypto.pvl` a DH destructor succeeds only on `x25519_public(_)` inputs and returns a private `x25519_shared(_, _)` term, which never equals a public constant. The core all-zero check (`pqxdh.rs:383-389`) and libsodium's own refusal can therefore never reject a value that reached them, and the DH destructor failure stands in for every Rust DH refusal (same observable effect: `None`, no state change). The check must be added when a theory with low-order points is used (stage P4).
4. **Finish collapsed to sequence one.** Rust opens the response frame with the general receive and then aborts if its sequence is not one (`beacon.rs:462-470`). Every other sequence ends in the same terminal abort with no output, so opening only at `fs_seq(1)` is exact for every event of this scenario; the terminal abort is part of the pending L5. The witness that a later frame is opened before the gate (A3) belongs to the record scenario, which has later frames. Because this scenario has no later frames, the gate decides no verdict here: a review run with the gate line removed still gave A1 TRUE at K_reg = 2. The transcript-fidelity test pins the gate for fidelity, and the record-scenario A1 with the control C-NOGATE is what exercises it.
5. **Nonempty-payload check omitted.** `beacon.rs:473-475` can only reject, and model payloads are never empty.
6. **Fresh registration payload.** The application may pass any nonempty data; the model uses a fresh name per build. Authentication is therefore shown for fresh application payloads ([L6 register item E7](../proverif-fs-event-meaning.md#register-of-coarser-and-finer-points)). A build with `data = None` uses the public default payload `REGISTRATION_WITNESS`, the single byte 0xFF (`server.rs:459`, `shared.rs:50`), and callers do pass `None`; that default payload is not covered by the fresh-name model.
7. **Failures that emit no event.** Failures before the registration ID, and allocation, randomness, ML-KEM decoding, encapsulation, key conversion, size conversion and HKDF failures after it, return `None` with no state change and no output; deleting such a call from a Rust run leaves every other event unchanged (case (v) of the pending L1). One of them can occur after the signatures verified: libsodium refuses to convert a Beacon identity key outside the prime-order subgroup (`server.rs:374`), although Ed25519 verification accepts such a key; in `crypto.pvl` the conversion of a verified identity never fails, which is a property of the theory, not of Rust ([the reference](../proverif-fs-event-meaning.md#fsserveracceptfailedobj-s-b-rid)). Occupancy is always `Available` in the model, as in Rust outside test helpers. The bridge `fs_kid(n)` stands for `server_kid + n` without wrapping, so the model's builds match Rust's key IDs when `server_kid + K_reg <= u64::MAX`; when that fails (for example `server_kid = u64::MAX`, which exhausts the counter at the first build), every exhausted Rust build returns `None` and is the model's drop, so those runs are still covered.
8. **The bound counts inputs.** A bundle that fails to parse also uses one of the K_reg steps, with the state unchanged. This is conservative: every Rust run of a Server object maps to a model run in which only its first K_reg calls are covered.
9. **na (record scenarios).** Writing a fresh name without session arguments, `new x[]`, changes only ProVerif's internal abstraction of names, making it coarser (more facts derivable), and not the process semantics; a TRUE verdict stays sound and a FALSE verdict still needs a reconstructed trace. It is accepted for the record scenarios (G0 section 2) and not used in `fs-registration`.
10. **Selection heuristic nx and `[precise]`.** See [the heuristic paragraph](../formal-verification-analysis.md#the-fs-selection-heuristic-nx) and [the precision settings](../formal-verification-analysis.md#proverif-precision-and-approximation-settings). Neither restricts traces.

The C-UKS hooks are two pure `letfun`s, `fs_root_dh2` and `fs_associated_data`, whose bodies are a variable and a total reduction; ProVerif inlines them without new branches (checked in the expanded process and by unchanged K_reg = 2 timings against P0).

## Event meanings

Each event is a predicate on one Rust public call (the L6 projection, maintained as [the fs event-meaning reference](../proverif-fs-event-meaning.md) and reviewed at the start of stage P2). That document gives every event's success conditions, state change, field kinds and coarser or finer points with Rust citations, and the Rust reading of each claim. The table summarises the Rust outcome; `S` is the Server identity (the Beacon's pin on the Beacon side), `B` the Beacon identity, `init` the verified key tuple, `rid` the registration ID, `kid` the assigned key ID.

| Event | Rust outcome |
| --- | --- |
| `FsBeaconStarted(S, B, init, rid)` | `get_registration_bundle` returned `Some(bundle)`; `rid` is a ghost |
| `FsServerAccepted(obj, S, B, init, rid, root)` | `get_shared_secret` on `obj` returned `Some(token)`: `rid` inserted, no peer installed |
| `FsServerReplayRejected(obj, S, B, rid)` | `get_shared_secret` returned `None` because `rid` was consumed (witness and definitional use only) |
| `FsServerAcceptFailed(obj, S, B, rid)` | `get_shared_secret` returned `None` after the consumed check, set unchanged (witness use only); under `crypto.pvl` only when the prekey or the one-time key is not an X25519 public key |
| `FsServerCommitted(obj, S, B, init, kid, root, ad, payload)` | `build_registration_response` returned `Some(response)`: peer installed under `kid`; `init` and `root` are ghosts |
| `FsBeaconEstablished(S, B, init, kid, root, ad, payload)` | `finish_registration` returned `Some(payload)` and the Beacon is `Established` |
| `FsBeaconFinishOpenedLater(S, B, t)` | Record scenarios, witness only: the finish opened sequence `t != 1` before the gate aborted |
| `FsSent(dir, S, B, kid, root, t, m)` | Record scenarios: allocation of sequence `t` for `m`, not the `Some` return (the counter stays advanced when sealing fails) |
| `FsReceived(dir, S, B, kid, root, t, m)` | Record scenarios: a receive accepted sequence `t` and returned `m` |
| `FsFarAccepted(dir, S, B, kid, root, t)` | Record scenarios: the far-target branch opened `t > T_max`; the worker stops |
| `FsReceiveRejected(dir, S, B, kid, root, t)` | Record scenarios, witness only: a parsed frame from the expected sender was rejected with the entry state preserved |

Some fields are not values that the call returns. `fs-common.pvl` calls four of them ghost fields: `root` on `FsServerCommitted` (a field of the opaque token there) and on every record event (dropped by Rust after deriving the chains), `init` on `FsServerCommitted`, `rid` on `FsBeaconStarted` (computed only by the model, from the Beacon's keys), and `kid` on Beacon receives (the Beacon's stored assigned ID, which the receive does not return); [the reference](../proverif-fs-event-meaning.md#field-kinds) classifies them more finely. A claim that mentions such a field quantifies over it as a function of the run history. Failure-cause events are finer than the Rust outcome, which is the same `None` for every failure; they never appear in a security result.

## Claims, classes and bounds

| Target | Class | K_reg | Query file | Expected |
| --- | --- | --- | --- | --- |
| A1 | security | 3 | `fs-registration-a1.pv` | `inj-event(FsBeaconEstablished(s,b,init,kid,root,ad,p)) ==> inj-event(FsServerCommitted(obj,s,b,init,kid,root,ad,p))` true |
| A2 | security | 3 | `fs-registration-a2.pv` | `event(FsServerAccepted(obj,s,ed_public(k),init,rid,root)) ==> event(FsBeaconStarted(s2,ed_public(k),init,rid)) \|\| attacker(k)` true |
| R1 | security | 3 | `fs-registration-r1.pv` | two `FsServerAccepted` on one object with one `rid` are the same event: true |
| R1' | security | 3 | `fs-registration-r1prime.pv` | two `FsServerAccepted` on one object for `ed_public(k)` are the same event `\|\| attacker(k)`: true |
| S3-server | security | 3 | `fs-registration-s3-server.pv` | `FsServerCommitted(…, ed_public(k), …, root, …) && attacker(root) ==> attacker(k)` true |
| S3-beacon | security | 3 | `fs-registration-s3-beacon.pv` | `FsBeaconEstablished(…, root, …) && attacker(root)` unreachable |
| R2 | definitional | 2 | `fs-registration-r2.pv` | `FsServerReplayRejected ==> FsServerAccepted` (same object and `rid`) true by construction |
| R3 | witness | 2 | `fs-registration-r3.pv` | an honest bundle rejected as a replay: reachable |
| R5 | witness | 2 | `fs-registration-r5.pv` | `FsServerAcceptFailed` before `FsServerAccepted` of the same `rid` on one object: the "failure after acceptance" correspondence is false |
| W1 | witness | 1 | `fs-registration-w1.pv` | `FsBeaconEstablished` with `fs_kid(1)`: reachable |
| W2 | witness | 2 | `fs-registration-w2.pv` | `FsBeaconEstablished` with `fs_kid(2)`: reachable |
| W3 | witness | 1 | `fs-registration-w3.pv` | `FsServerAccepted` for `ed_public(k)` with `attacker(k)`: reachable |
| R4 | limitation | 1 | `fs-registration-r4.pv` | an honest bundle accepted by two Server objects: the uniqueness query is false |
| C-NOCHECK | control | 2 | `fs-registration-r1.pv` with `fs-control-nocheck.pvl` | R1 false |
| C-UKS | control | 1 | `fs-registration-a1.pv` with `fs-control-uks.pvl` | A1 false, and its non-injective form false too |

A1 and both S3 forms are about runs in which no Server object sends a record after registration, since this scenario has none. R1' holds because an honest Beacon outputs at most one signed bundle, so one one-time key (pending L5). S3-beacon, like A1, is about Beacons that pin the honest Server key; W3 witnesses the corruption condition of A2. The corruption conditions of R1' and S3-server need more than its single accept: R1' needs a second accepted bundle of the same attacker identity on the same object, which follows after more attacker inputs, and S3-server needs a build, which follows such an accept after one more attacker choice; neither has a separate witness.

The checker holds the exact ProVerif result line of every target (ProVerif renames some query variables, for example `obj` to `obj_1`). A FALSE result must come with exactly one reconstructed trace; a TRUE result with none. R5 is a witness written as a correspondence, because ProVerif 2.05 rejects time inequalities in reachability queries; like R4 and the two controls, it is FALSE by design.

Measured traces of the FALSE results: R3, an honest bundle accepted and built on one object and then replayed to it; R5, an attacker identity's bundle with a prekey that is not an X25519 key fails after the consumed check, and the same identity and one-time key with a valid prekey are then accepted by the same object; R4, one honest bundle delivered to two Server objects; C-NOCHECK, an attacker identity registering twice on one object with the same one-time key and different prekeys; C-UKS, an attacker identity re-signing an honest Beacon's prekey, one-time and ML-KEM keys, the Server building the response for the attacker identity, and the honest Beacon completing with that response.

## Results of the serial verification pass

The verification record is one serial run of `make -C beaconcrypt-core check-proverif-fs PROVERIF_FS_LOG_DIR=<dir>` on 2026-10-04 from 18:09 to 18:53 (+02:00), on the tree of the commit that records it: commit `f85e7c3` plus that commit's fix of the checker's log file names, with every file outside `doc/` identical to the recording commit. It ran inside the locked proof shell (entered through a copy of `flake.nix` and `flake.lock` whose SHA-256 match the repository files), holding the shared ProVerif lock, with ProVerif 2.05, `PROVERIF_FS_TIMEOUT` = 1800 s and `PROVERIF_FS_ADDRESS_SPACE_KIB` = 10485760, on a 16 GB machine used by this run alone. The transcript-fidelity test (23 tests) and the checker regression test (36 tests) passed first. Every target ran as its own ProVerif process, one after another, gave its exact expected result lines and left its own log, fifteen in all. The peak address space (`VmPeak` in `/proc/<pid>/status`) was sampled every quarter second by a separate script; runs shorter than about a second can end between two samples.

| Target | Class | K_reg | Verdict | ProVerif time (s) | Peak RSS (KiB) | Peak address space (KiB) |
| --- | --- | --- | --- | --- | --- | --- |
| A1 | security | 3 | TRUE | 1029.12 | 9866724 | 10130732 |
| A2 | security | 3 | TRUE | 113.69 | 5711716 | 5975116 |
| R1 | security | 3 | TRUE | 413.70 | 5826020 | 6053932 |
| R1' | security | 3 | TRUE | 582.24 | 5849956 | 6113356 |
| S3-server | security | 3 | TRUE | 86.24 | 5022692 | 5286348 |
| S3-beacon | security | 3 | TRUE | 378.41 | 5284324 | 5549260 |
| R2 | definitional | 2 | TRUE | 2.44 | 259428 | 519752 |
| R3 | witness | 2 | FALSE (reachable) | 1.49 | 168644 | 424488 |
| R5 | witness | 2 | FALSE (reachable) | 2.69 | 295876 | 559464 |
| W1 | witness | 1 | FALSE (reachable) | 0.07 | 37236 | not sampled |
| W2 | witness | 2 | FALSE (reachable) | 2.01 | 180548 | 442184 |
| W3 | witness | 1 | FALSE (reachable) | 0.04 | 37236 | not sampled |
| R4 | limitation | 1 | FALSE (expected) | 0.04 | 37236 | 281412 |
| C-NOCHECK | control | 2 | FALSE (expected) | 1.70 | 182340 | 443560 |
| C-UKS | control | 1 | FALSE (expected) | 0.08 | 37236 | not sampled |

The run took 2614.0 s of ProVerif time (2603.4 s for the six security results) and 2642.0 s (44 minutes) of wall time for the whole Make target, including both transcript-fidelity runs and the shell start, which is within the share of about one hour of the 3 h fs budget (OD7). Two earlier serial passes gave the same fifteen exact results: one at commit `7518974`, the record of the first P1 commit (2635.4 s of ProVerif time), and one at commit `f85e7c3` before the log-name fix (2587.5 s), in which R1 and R1' wrote the same log file; that collision is what the fix removes. Per-target times of the three passes agree within about 7% for every run longer than one second. `check-inventory`, run afterwards through Make in the same locked shell environment, reported that the inventory matches the reviewed boundary.

A1 is the critical run. The cap is an `RLIMIT_AS` limit on the address space (virtual memory), which is always at least the resident memory. A1's peak address space was 10130732 KiB (9.66 GiB), 96.6% of the 10485760 KiB (10 GiB) cap, in this pass and in the pass at `f85e7c3`, so A1 keeps 355028 KiB (0.34 GiB, 3.4%) of headroom; its peak resident memory was 9866724 KiB (9.41 GiB), 94.1% of the cap. A model change that enlarges the Server step can push it over the cap; the recorded fallback is A1 at K_reg = 2 (3.4 s), which would be a weakening. The other security results peaked at 5022692-5849956 KiB (4.79-5.58 GiB) resident and 5286348-6113356 KiB (5.04-5.83 GiB) of address space. Peak resident figures of about 37200 KiB for the shortest runs are the floor of the measurement: the checker reads the peak resident memory of the child process with `wait4`, which includes the forked checker before it starts ProVerif. The P0 spike measured A1 at K_reg = 3 in 1071.7 s and about 9.80 million KiB resident.

## What the bounds do not cover

The security results hold for unbounded Server objects, honest Beacons and attacker identities, but only for the first three `get_shared_secret` calls of each Server object (and the builds that follow its accepts). A Server object's fourth or later bundle is not covered by ProVerif; the per-object replay rule at any depth is the Lean theorem `no_reacceptance` (`PqxdhRegistrationAdmission`), and the composition of bounded ProVerif results with Lean state-machine facts is not part of P1. These bounded results do not discharge global closure item 1 (arbitrary reached committed states). The scenario contains no record traffic, so A1 and S3 are about runs without later Server records, and the scenario says nothing about records, the sequence-one gate witness, agreement under later taskings (the HB-95 class), record secrecy or record replay (stages P2 and P3). The theory is `crypto.pvl`, so it says nothing about same-role DH equalities, X25519 encoding aliases, low-order points or ML-KEM implicit rejection (F13, stage P4). Application payloads are fresh values; the public default payload `REGISTRATION_WITNESS` is not covered. A token accepted by one live object and built by another is not modelled (case (iv) of the pending L1).

## OD2: replay per live Server state

The proof Server is an idealisation: its identity key is generated or derived once, never disclosed, and never backed up or restored. Two Server objects built from the same seed are one Server identity for the protocol but keep separate consumed sets in Rust (`server.rs:26-32`, `:148-168`). R1 and R1' are therefore stated per live Server object, and R4 shows that a second live object with the same key accepts the same honest bundle again. That is the expected consequence of OD2, not a modelling error: the replay claims apply to deployments that run one live Server object per identity key. OD2 does not cover a token that one live object accepts and another builds; that is case (iv) of the pending L1.

## Beacon pins

Bundles carry no Server field (`pqxdh.rs:304-321`), and a Rust Beacon can pin any key. A2 leaves the pin `s2` of the sending Beacon free, R1' does not mention the pin, and S3-server speaks only of Server events and attacker knowledge, so all three read as statements about any Beacon. In this scenario the pin enters only the finish, which outputs nothing, so model Beacons that all pin the honest Server key produce exactly the bundles and attacker knowledge of Beacons with arbitrary pins. A1 and S3-beacon are statements about Beacons that pin the honest Server key, the deployment of the [threat model](../threat_model.md) with a compiled-in Server key. For S3-beacon the restriction is essential: a review run with the Beacon's pin check removed made it FALSE at K_reg = 1, as expected, since a Beacon that pins a key the attacker holds runs its key exchange with the attacker.

## Gates and wiring

This section describes the gates as P1 added them. Stages P2 and P3 added the two record scenarios to the same group, their runners, their checker targets and their pins, and updated the counts below; the [b2s guide](proverif-free-schedule-records-b2s.md#gates-and-wiring) gives the current figures.

- `check-proverif-fs` runs `$(PROVERIF_FS_CHECK_TARGETS)` with `-j1`; it depends on the transcript-fidelity test and is never a prerequisite of `check-proverif`. `PROVERIF_FS_SCENARIOS` holds `fs-registration` only; the parallel `PROVERIF_SCENARIOS` roster still has its 35 scenarios.
- `check-proverif-fs-registration` runs the checker regression test, then the checker with `--timeout $(PROVERIF_FS_TIMEOUT)` (1800), `--address-space-kib $(PROVERIF_FS_ADDRESS_SPACE_KIB)` (10485760) and, when `PROVERIF_FS_LOG_DIR` is set, `--log-dir $(PROVERIF_FS_LOG_DIR)`. Without it, a failed target's log stays at the path its error message names, and the checker regression test checks this for a non-zero exit, a wrong receipt and a timeout. Every target writes its own log file (`R1'` writes `R1prime.log`), and the checker rejects a manifest in which two targets would share one.
- `verify-in-shell` and `verify-proverif-in-shell` run `check-proverif-fs` right after `check-proverif`.
- The checker loads, in this order, `production-transcript-interface.pvl`, `crypto.pvl`, `extraction/lib.pvl`, `fs-common.pvl`, the consumed-set library, the binding library, `fs-registration.pvl` and the bound file, then the query file. It never loads `environment.pvl`. The legacy rule that the interface and `crypto.pvl` appear once in the Makefile is unchanged, because the fs loader lives in the checker.
- New transcript-fidelity tests: `free_schedule_roster_and_serial_wiring_are_pinned`, `free_schedule_rust_fidelity_annotations_are_exact`, `free_schedule_vocabulary_and_registration_model_are_pinned`, `free_schedule_checker_loader_and_targets_are_pinned` and `proverif_declarations_are_allowlisted`. Each also applies mutations and requires them to be rejected. The declaration test strips comments as ProVerif does (nested, each comment a token separator), so a declaration keyword glued to a comment is found, and it also scans the string literals of the Python files under `proofs/pro-verif`, which write ProVerif text at run time; [the policy](../formal-verification-analysis.md#proverif-declaration-policy) states exactly what that scan covers.
- `check-inventory.sh` records 124 handwritten ProVerif files and 25 validation files, the new `_to_bitstring` counts (18 and 21), and tripwires for the serial fs group, its timeout, its place in `verify-in-shell` and the absence of `axiom`, `restriction` and `elimtrue` declarations.

## Deviations from the plan

- **R4 has an honest-bundle premise.** The plan's R4 has no corruption condition, so attacker identities alone would falsify it. A variant with the corruption disjunct `|| attacker(k)` gave "cannot be proved" (ProVerif finds the trace but cannot confirm it). R4 therefore adds the premise `FsBeaconStarted(s2, b, init, rid)`, which selects honest bundles, without the disjunct; it is FALSE with a confirmed trace that is specific to honest bundles.
- **R4 is classed `limitation`**, the plan's "documented limitation (expected attack)", because it is neither a security result, a witness, a control nor a definitional check.
- **S3 (Server form) is stated on `FsServerCommitted`**, as in the plan. A stronger form on `FsServerAccepted` (also covering dropped tokens) cost 12 s at K_reg = 2 against 1 s, which projects beyond the per-target cap at K_reg = 3. A dropped token's root is never used by any output of the model.
- **W3 is added** as the witness that attacker identities are served.
- **No all-zero check** in the model under `crypto.pvl` (step 3 above).
- **`verify-proverif-in-shell` also runs the fs group**, so that the ProVerif-only recipe checks every ProVerif result.
- **No CI target.** The fs group needs a 10 GiB address space per run and took about 45 minutes per pass in P1 (about two hours since P2 added the record scenario); it is not added to the GitHub workflow.
- **P1 ran before the L6 review.** The plan's precondition for P1 and G0 section 10 item 8 ask for a review of the L6 event-meaning draft before P1, at least of its items 1-4. By orchestrator decision of 2026-10-04, P1 went ahead with the P0 draft (scratch `/tmp/bc-arc-scratch/pv-work/p0/l6/event-meaning.md`) not separately reviewed, following G0 item 8 only in part: the draft's items 1-4 were applied in P1, the allocation meaning of `FsSent` and the witness-only event `FsReceiveRejected` in `fs-common.pvl`, A2 and R1' left free of the Beacon pin, and, for registration, authentication recorded as shown for fresh application payloads (step 6; item 4 for the record scenarios is an open item below). The P1 fidelity review checked the fs events against the Rust code. A separate L6 review is scheduled at the start of P2, before any record claim relies on it. The draft is now committed as [the fs event-meaning reference](../proverif-fs-event-meaning.md), with every citation re-checked at `9e588c6` and the corrections listed in [its change record](../proverif-fs-event-meaning.md#changes-from-the-p0-draft). The separate review was made at the start of P2 and its findings are applied there ([review record](../proverif-fs-event-meaning.md#review-record)).

## Open items for P2

Stage P2 delivered the Server-to-Beacon record scenario, the written arguments for the v2 coins and for the Server-to-Beacon direction split, the fail-stop measurement and the decision on adversary-chosen plaintexts for that direction ([records guide](proverif-free-schedule-records.md)); the Beacon-to-Server items below are stage P3.

- The record scenarios `fs-records-s2b` and `fs-records-b2s`: send and receive step macros with the far-target branch, the claims C1-C5, S1, S2 and S4, A1 and A2 re-proved in their processes, the witness A3, and the controls C-RETAIN, C-NOGATE, C-STALE and C-FAILMUT. Each joins `PROVERIF_FS_SCENARIOS`, gets its own targets in the checker and its citations in the transcript-fidelity table.
- Written justifications for the record model steps that G0 measured: early-fresh Server coins (v2) and, if used, fail-stop receive workers.
- L6 item 4: an attacker-chosen plaintext send step for A1 and C1-C3, or a recorded restriction to fresh application plaintexts ([record-model forms](../proverif-fs-event-meaning.md#record-model-forms-and-event-meaning)); the reference lists the other record items it found, in its [open items](../proverif-fs-event-meaning.md#open-items).
- The record-form C-UKS target UKSr, which replaces C2 (G0 section 7).
- The paper obligations L1 (accept and build scheduling, including case (iv)) and L5 (Beacon lifecycle), which every Rust reading of the registration results relies on. The review of L6, committed as [the fs event-meaning reference](../proverif-fs-event-meaning.md), was made at the start of P2.
- Stage P4: the all-zero check and a witness that distinguishes it, once a theory with low-order points is used.
- CI wiring of the fs group, and the stale handwritten-ProVerif count in the baseline of `beaconcrypt-core/proofs/trusted-boundary.md` (P8 integration). The fs gate, its files, the nx heuristic and the cost of a pass are already described there and in `beaconcrypt-core/README.md`.
