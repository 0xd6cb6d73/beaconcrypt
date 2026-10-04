# Free-schedule ProVerif records, Server to Beacon (fs-records-s2b)

This guide records stage P2 of the staged ProVerif plan for audit findings F2, F13 and F11: the `fs-records-s2b` scenario, in which Server objects register Beacons and then send them records (taskings) under an attacker-chosen schedule, its targets, controls and witnesses, its result checker and the transcript-fidelity and inventory gates that pin it. It follows the [fs-registration guide](proverif-free-schedule-registration.md) of stage P1, whose vocabulary, serial verification group, checker and declaration policy it extends. The plain-English explanation of every result is in [What beaconcrypt's formal verification proves](../formal-verification-analysis.md#free-schedule-proverif-records-server-to-beacon-fs-records-s2b), and the meaning of every fs event as a Rust API outcome, with what each claim says about Rust, is in [the fs event-meaning reference](proverif-fs-event-meaning.md).

Every fs result is a symbolic result (Dolev-Yao attacker, free constructors, ideal hash, KDF and AEAD) for a bounded process. None of them is a computational bound. Cap'n Proto is out of scope: messages are abstract byte strings that each side can decode. libsodium is a black-box functional contract. Persistence is out of scope, and the proof Server has perfect key management and no backup or restore (owner decision OD2). No axiom, restriction, lemma or proof-only process is used. Reading the results as statements about the Rust API rests on the paper arguments listed under [Pending paper arguments](#pending-paper-arguments); until they are written and reviewed, each result is cited as a symbolic result for the fs process, which models the Rust interface under these pending abstraction steps.

## Basis and decisions

The Rust basis is branch `codex/full-proof-composition` at `9e588c6`, whose Rust sources are identical to `959cdab` (the basis of the plan and of the P0 spike) and to `533901f` (the P1 basis): `git diff 959cdab 9e588c6 -- beaconcrypt/src beaconcrypt-core/src` is empty. The Rust code is authoritative: where the model and Rust differ, the model follows Rust. The decisions applied here are those of gate G0, the owner and the orchestrator for P2:

- OD1: bounded results are the ProVerif deliverable. OD2: one live Server state per identity key; the proof Server is idealised. OD7: at most 1800 s per target and a 10 GiB address space per run, the fs group serial and alone on the machine, about 3 h for the whole group. OD11: the serial run is the verification record.
- Theory `crypto.pvl`, the self-contained `fs-common.pvl` and the single allowlisted selection heuristic nx, all as in P1.
- The "v2" early-fresh form of the Server ephemeral secret and KEM coins, accepted with the written justification of [step 2](#model-steps-and-their-justifications).
- Bounds (K_s, K_r, T_max) = (2, 3, 3) with the far branch, and one bundle per Server object (K_reg = 1); witnesses and controls at the smallest K_r that exhibits them.
- C5 witnesses written as correspondences that are expected to be FALSE, because ProVerif 2.05 rejects time inequalities in reachability queries (G0 section 7).
- `FsReceiveRejected` emitted only in the rejection branches that the witnesses need ([step 9](#model-steps-and-their-justifications)).
- C-STALE, C-FAILMUT and the replay-rejected witness measured, with C-FAILMUT to be dropped under the plan's rule if ProVerif could not decide it within the caps. ProVerif decides it in seconds at K_r = 2, so it is kept.
- The fail-stop form of the receive worker measured ([Fail-stop measurement](#fail-stop-measurement)), but C1 and C3 kept in the form in which failures are interleaved; no target uses fail-stop.
- L6 item 4 (adversary-chosen plaintexts): a tasking form with whole adversary-chosen plaintexts for the authentication claims if it fits the caps. It fits (C1, the largest, uses 63% of the time cap and of the memory cap), so it is used ([step 5](#model-steps-and-their-justifications)).
- The record-form A1 together with C-NOGATE covers the HB-95 class (the sequence-one gate), and C-NOGATE keeps its application-prefix input.

## Pending paper arguments

The ProVerif verdicts are exact statements about the fs process. Their Rust readings rest on the following arguments of the plan, which are not settled unless stated:

- **L1, accept and build scheduling (pending).** In this scenario only the drop and the adjacency of accept and build on one object matter, because each object takes one bundle; case (iv), a token built on another live object with the same key, stays open as in P1.
- **L2, one registration per record object (pending).** A Rust Server object can install many peers and route records to each; the model gives every Server object one bundle and one peer, all with the key ID `fs_kid(1)`, and lets the attacker deliver a frame to any receive attempt. The argument must show that every Rust run of a multi-peer object maps to a run of the model with several objects that share the identity key (OD2), with the same events.
- **L3, failure neutrality and the far-target collapse (pending).** A failed receive keeps the exact entry state; Rust admits t ≤ r + 51 − |C|, which the model over-approximates above T_max by the far branch, after which the worker stops (OD4).
- **L4, the send relation (pending).** `FsSent` is the allocation of a sequence; the model outputs the frame even when Rust's seal or snapshot fails, which only strengthens the attacker.
- **L5, Beacon lifecycle (pending).** At most one bundle, at most one finish, and a failed finish aborts for good.
- **L6, event projection: reviewed** at the start of P2 ([review record](proverif-fs-event-meaning.md#review-record)).
- **E20 (v2) and E19 (direction split): written here** ([steps 2 and 4](#model-steps-and-their-justifications)), not yet separately reviewed.

## Files

| File | Role |
| --- | --- |
| `beaconcrypt-core/proofs/pro-verif/fs-records-s2b.pvl` | The Server object (one registration in Rust order, the response build, then the taskings), the honest Beacon (bundle, finish that opens sequences 1 to T_max before the gate, receive attempts) and the main process |
| `fs-records-s2b-receive.pvl` | The far-chain function, the Beacon receive step macro `FS_S2B_RECV_STEP` and the stop process |
| `fs-records-s2b-kr1.pvl`, `-kr2.pvl`, `-kr3.pvl` | The expansions for K_r = 1, 2 and 3 receive attempts |
| `fs-records-s2b-window.pvl`; `fs-control-retain.pvl`, `fs-control-stale.pvl`, `fs-control-failmut.pvl` | How a receive attempt changes the receive state after a successful cached open and after a failed open, and the three receive-state controls |
| `fs-records-s2b-gate.pvl`; `fs-control-nogate.pvl` | What the finish does after it opened a later frame (the sequence-one gate aborts), and the control C-NOGATE |
| `fs-records-s2b-taskings.pvl`; `fs-records-s2b-taskings-chosen.pvl` | The two Server taskings with fresh application plaintexts behind an adversary-chosen prefix, and the form in which the adversary may also choose whole plaintexts |
| `fs-records-s2b-<claim>.pv` (11 files) | One query per file: `a1`, `a2`, `a3`, `c1`, `c3`, `c4`, `c5a`, `c5b`, `c5c`, `s1`, `s4` |
| `fs-common.pvl` | Comments only: the field kinds and the use of failure-cause events by controls, aligned with the reviewed L6 reference |
| `check-free-schedule.py`, `test-free-schedule-checker.py` | The checker now holds both scenarios, selected with `--scenario`, and its regression test covers the record targets |
| `declaration-allowlist.tsv` | Four new `[precise]` entries |
| `beaconcrypt-core/tests/proverif_transcript_fidelity.rs` | The fs roster, the 84 new Rust citations, the record model and hook libraries, the record target manifest, and a new mutation test |
| `beaconcrypt-core/Makefile` | `fs-records-s2b` in `PROVERIF_FS_SCENARIOS` and its runner `check-proverif-fs-records-s2b`; the registration runner now passes `--scenario fs-registration` |
| `beaconcrypt-core/proofs/check-inventory.sh`, `reviewed-inventory.txt` | New file hashes and counts, and two tripwires for the record runner |

## Running

Inside the locked proof shell, `make -C beaconcrypt-core check-proverif-fs` runs the transcript-fidelity test and then, one ProVerif process at a time, every fs-registration target followed by every fs-records-s2b target. `make -C beaconcrypt-core check-proverif-fs-records-s2b` runs the record targets alone, and `PROVERIF_FS_LOG_DIR=<dir>` keeps every log. To run the checker directly:

```sh
python3 beaconcrypt-core/proofs/pro-verif/check-free-schedule.py --scenario fs-records-s2b --list
python3 beaconcrypt-core/proofs/pro-verif/check-free-schedule.py --scenario fs-records-s2b --only s2b-C1 --log-dir /tmp/fs-logs --timeout 1800 --address-space-kib 10485760
```

The fs group needs the machine to itself ([Results](#results-of-the-serial-verification-pass) gives the time of a pass).

## Model structure and Rust mapping

Unbounded Server objects share the one honest Server identity and own key ID. Each object processes one registration bundle, builds the response when the attacker schedules it, and then sends two taskings to the peer it installed. Unbounded honest Beacons run alongside: each draws fresh keys, sends one bundle, finishes at most once and then makes K_r receive attempts. The attacker builds its own identities from public constructors, and the same Server code serves them. Every attacker input is `[precise]`, and honesty appears only in the queries.

Server object (`FsS2bServer`):

| Model step | Rust |
| --- | --- |
| Fresh ephemeral secret and KEM coins, drawn at object start (v2) | `server.rs:368`, `:373` |
| Read one bundle; identity tag; three signatures and role tags; `init`; registration ID | `server.rs:332-354`; `pqxdh.rs:325-345`, `:195-204` |
| Consumed check: always `Fresh` with one bundle per object | `server.rs:355-360` |
| Identity conversion and DH1-DH4; root input and root | `server.rs:374-414`; `pqxdh.rs:391-405` |
| Insertion, then `FsServerAccepted` | `server.rs:415-421` |
| Any attacker input schedules the build; key ID `fs_kid(1)` | `server.rs:424-439`; `pqxdh.rs:838-844` |
| Ratchet start, associated data, fresh payload, binding, seal at sequence 1 | `server.rs:440-479`; `pqxdh.rs:877-880`, `:928-947` |
| `FsServerCommitted` and `FsSent(…, 1, binding ‖ payload)`, then the response | `server.rs:489-501` |
| Taskings at sequences 2 and 3: one attacker input each, `FsSent`, then the sealed frame | `server.rs:224-228`, `:504-514`; `ratchet.rs:414-444`; `concrete.rs:133-155`, `:171-182`, `:206-209` |

Beacon (`FsS2bBeacon`):

| Model step | Rust |
| --- | --- |
| Fresh identity, prekey, ML-KEM key, one-time key; `FsBeaconStarted`, then the bundle | `beacon.rs:65-83`, `:301-305`, `:335-357`, `:398`; `pqxdh.rs:304-321` |
| Decode the response, convert the Server identity, decapsulate, DH1-DH4, pin check, root, receive chain, associated data | `beacon.rs:402-461`; `pqxdh.rs:545-547`, `:552-555` |
| General receive on the fresh ratchet: frame with the pinned Server ID as sender, sequence t | `beacon.rs:462-467`; `ratchet.rs:499-536` |
| t = 1: open, binding check, pin checks, `FsBeaconEstablished`, `FsReceived(…, 1, binding ‖ payload)`, then the receive attempts from r = 1 with an empty cache | `beacon.rs:468-509`; `pqxdh.rs:616-628` |
| t = 2 or 3: open, `FsBeaconFinishOpenedLater`, then the gate library: the gate aborts | `beacon.rs:468-470`, `:488-491` |
| t = 0 or t > T_max: abort without the witness event | `beacon.rs:468-470`; `concrete.rs:264-274` |

Receive attempt (`FS_S2B_RECV_STEP`, state r and `cached_2`):

| Case | Model | Rust |
| --- | --- | --- |
| Frame does not parse or its sender is not the pinned Server ID | state unchanged, no event | `ratchet.rs:505-516`; `record.rs:35-61` |
| t ≤ r, t = 2 and cached | open with the material of position 2; success: `FsReceived`, the key is removed; failure: `FsReceiveRejected`, entry state | `concrete.rs:270-280`, `:436-454`; `refined.rs:317-330`, `:700-721`; `control.rs:435-461` |
| t ≤ r otherwise (sequence 0, 1, consumed or never cached) | `FsReceiveRejected`, entry state, no open | `concrete.rs:270-274` |
| t = 2 > r | open; success: `FsReceived`, r := 2; failure: `FsReceiveRejected`, entry state | `concrete.rs:282-300`; `refined.rs:755-778`; `concrete.rs:440-443` |
| t = 3 > r | open; success: `FsReceived`, r := 3, and position 2 cached when r was 1; failure: `FsReceiveRejected`, entry state | as above |
| t > T_max | far branch: open with `ratchet_material(fs_far_chain(chain_4, t))`; success: `FsFarAccepted` and the worker stops; failure: entry state, no event | `control.rs:223-245` (admission over-approximated) |

The transcript-fidelity test `free_schedule_rust_fidelity_annotations_are_exact` now holds 143 citations, 84 of them in the record files; each first cited line must start with the annotation's anchor text, and a range is at most 40 lines.

## Model steps and their justifications

1. **One bundle per Server object (pending L2).** The record scenarios give each Server object one registration and one peer, with the key ID `fs_kid(1)`. Several model objects with the one identity key stand for one Rust object with several peers; the attacker delivers frames to any receive attempt, which over-approximates Rust's routing by the claimed sender.
2. **Early fresh Server coins (v2, E20).** Rust draws the ephemeral key pair at `server.rs:368` and the KEM coins at `:373`, after the bundle has been decoded and checked; the model draws both names when the object starts, before its first input. The justification, at one bundle per object: (a) neither name occurs in any input, test, event or output before the point where Rust draws it, and the attacker cannot know a restricted name before it is output, so moving `new n` above an input or a test that does not mention n gives the same labelled transitions (the attacker's input cannot contain n, because n has not been output); (b) if any check before `server.rs:368` fails, the Rust call returns `None` and the model object stops, and the names drawn early are never used, so the visible behaviour of both forms is the same; (c) with one bundle per object, each object draws exactly one ephemeral secret and one set of coins, as Rust does for that bundle. The two forms therefore have the same traces, events and attacker knowledge. The reorder changes only ProVerif's internal naming of the two names, which no longer carry the bundle as a session argument, and that made the C5 witnesses fit in memory in P0. P0 also measured that the Rust-ordered form (v1) gives the same verdicts wherever it terminates. This is a paper argument written here, not yet separately reviewed; with K_reg > 1 it would not apply, and fs-registration keeps the Rust order.
3. **The build input carries no test.** Any attacker input schedules the build, and withholding it is the dropped token. With one bundle per object, the object takes no further input after a drop, so a test on the input value, as in fs-registration, would select no further behaviour; measured on C4, such a test made saturation about 1.7 times slower for about the same number of clauses.
4. **Direction split (E19).** The scenario has no Beacon send worker and no Server receive worker. The argument for the Server-to-Beacon claims: (a) a Beacon send would output frames sealed under the Beacon-to-Server chain, which is `hkdf_second_32` of the root's HKDF output (`crypto.pvl:77-80`), whereas every Server-to-Beacon key comes from `hkdf_first_32` and its successors; in the free-constructor theory no term built from the second projection yields the first or a successor of it, so these frames give the attacker no Server-to-Beacon key and no Server-to-Beacon frame; (b) such frames carry the Beacon's assigned key ID as sender, which the Beacon's receive refuses, and a relabelled frame fails the CTX commitment, which binds the sender ID; (c) a Server receive outputs nothing in the model (the `Some`/`None` bit is not published) and changes only the receive fields of the peer state, which no Server send reads (`concrete.rs:171-182` against `refined.rs:700-778`); (d) the removed workers' events (`FsSent` and `FsReceived` in the other direction) do not occur in any query of this scenario, and the claim C3, whose direction is a variable, is only about Beacon acceptances here. Removing the workers therefore removes neither a Server-to-Beacon event nor any attacker knowledge that a Server-to-Beacon claim depends on. This is a paper argument written here for s2b, not yet separately reviewed; the b2s direction is stage P3.
5. **Two tasking forms (L6 item 4, E7).** Rust lets the application send any nonempty bytes. `fs-records-s2b-taskings.pvl` sends, at sequences 2 and 3, an 8-byte prefix chosen by the adversary (any binding-shaped value included) followed by fresh bytes; without that prefix the C-NOGATE mutant could not fail, because a fresh name never parses as a binding followed by a payload. `fs-records-s2b-taskings-chosen.pvl` lets the adversary choose, for each tasking, either that form or a whole plaintext of its choice, so every trace of the fresh form is also a trace of the chosen form. The authentication claims A1, C1, C3 and C4, and A2, run in the chosen form, so they cover adversary-chosen plaintexts at either sequence. The secrecy result S1 and the witness S4 run in the fresh form, because with an adversary-chosen plaintext the attacker knows the plaintext and S1 would be false by construction. The witnesses and the controls also use the fresh form, which P0 measured and which is cheaper. Adversary-chosen plaintexts are any terms; a term that denotes the empty byte string would be refused by Rust before allocation (`ratchet.rs:421-423`), so the model has extra sends there, which only adds traces.
6. **Fresh registration payload.** As in fs-registration (its step 6), the response payload is a fresh name per build, so the sequence-one plaintext is the public binding followed by fresh bytes. The default payload `REGISTRATION_WITNESS` of a build without data is not covered.
7. **The finish opens sequences 1 to T_max.** Rust's finish opens the response frame with the general receive on a fresh ratchet, which admits t in 1..51, and then aborts unless t = 1 (`beacon.rs:462-470`). The model opens t = 1, 2 and 3; for t = 2 or 3 it emits the witness `FsBeaconFinishOpenedLater` and continues with the gate library, whose real form ends the Beacon. A frame with t = 0 or t > T_max ends the Beacon without an open: in Rust such an open may succeed for t ≤ 51, but the gate aborts either way and nothing observable differs, so only the witness range is smaller (E14).
8. **Receive state and capacity.** The receive state is r and the flag `cached_2`: after the finish r = 1 and the cache is empty, so position 2 is the only position that can be cached below T_max = 3. Rust admits a target t > r if t ≤ r + 51 − |C| (`control.rs:223-245`); here |C| ≤ 1 and r ≥ 1, so every t ≤ T_max is admitted and the capacity never binds below T_max. Above T_max the far branch over-approximates admission: it accepts every t > T_max with material derived from the chain at T_max + 1 by a public function, which no process outputs; it emits only `FsFarAccepted` and the worker stops, so no claim says anything about a peer direction after its first far acceptance (OD4, pending L3). C4 shows that this never happens here.
9. **Where `FsReceiveRejected` is emitted (E22).** The event is emitted for every parsed frame from the pinned Server ID that is rejected at a target t ≤ T_max: an old target that is not cached (rejected before any open, `concrete.rs:270-274`), a failed cached open and a failed future open at 2 or 3. It is not emitted for a failed far open, which no witness needs. In this scenario the event therefore means a rejection at t ≤ T_max. The event carries no frame, so a witness built from it does not say which frame was rejected.
10. **Bounds for witnesses and controls.** The security results run at K_r = 3. Witnesses and controls run at the smallest K_r that exhibits them: A3, S4 and C-NOGATE at K_r = 1 (they need no receive after the finish), C5a, C5b and C5c at K_r = 2, C-RETAIN and C-STALE at K_r = 3 (a replay needs three attempts), and C-FAILMUT at K_r = 2, the bound of the witness C5b that it controls. Each receive attempt waits for an attacker input, so a trace at a smaller K_r is also a trace at a larger one, and running a witness or a FALSE control at a smaller bound is not a weakening. C-FAILMUT is TRUE; its statement holds for K_r = 2 only, the bound at which C5b is witnessed.
11. **Control hooks.** The receive-window, gate and taskings libraries are hooks loaded before the process, like the consumed-set and binding hooks of fs-registration. The window hooks are three `letfun`s whose real bodies return the success state (`false`: the cached key is removed) and the entry state (r and `cached_2`) after a failed open; ProVerif inlines them. C-RETAIN keeps the cached flag after a successful cached open. C-STALE makes a failed open at t ≤ T_max restore the state left by the finish (r = 1, nothing cached); with K_r = 3 that is exactly "the state from before the previous success" of the plan: after one earlier success it is the state before that success, after none it is the entry state, and after two successes the restored state is that of the third and last attempt, which is never used. C-FAILMUT makes a failed open at t ≤ T_max consume its target as a success would: the cached key is removed, or r := t with position 2 cached when it is skipped; the far branch is unchanged. C-NOGATE replaces the gate's abort by the binding check and the commit, which is the behaviour of the branch `vcvio`.
12. **Fail-stop (E21): measured, not used.** In the fail-stop form a failed open of a parsed frame ends the receive worker. It was measured for C1, C3 and C4 ([Fail-stop measurement](#fail-stop-measurement)); every target runs in the form in which failures are interleaved, so no result relies on the fail-stop trace-mapping argument.
13. **Names, heuristic and precision.** Names keep their session arguments (the "na" form is not used). The selection heuristic nx and the `[precise]` inputs are those of P1 ([the heuristic paragraph](../formal-verification-analysis.md#the-fs-selection-heuristic-nx), [the precision settings](../formal-verification-analysis.md#proverif-precision-and-approximation-settings)); neither restricts traces.

## Claims, classes and bounds

ProVerif renames some query variables in its result lines (`root` to `root_2`, `obj` to `obj_2`, `init` to `init_2`); the checker holds the exact lines.

| Target | Class | K_r | Taskings | Query file and mutant | Expected | Meaning |
| --- | --- | --- | --- | --- | --- | --- |
| s2b-A1 | security | 3 | chosen | `fs-records-s2b-a1.pv` | TRUE: `inj-event(FsBeaconEstablished(s,b,init_2,kid,root_2,ad,p)) ==> inj-event(FsServerCommitted(obj_2,s,b,init_2,kid,root_2,ad,p)) is true.` | Registration agreement with later taskings: every Beacon finish is matched by its own build (injective) |
| s2b-A2 | security | 3 | chosen | `fs-records-s2b-a2.pv` | TRUE: `event(FsServerAccepted(obj_2,s,ed_public(k),init_2,rid,root_2)) ==> event(FsBeaconStarted(s2,ed_public(k),init_2,rid)) \|\| attacker(k) is true.` | Bundle origin, re-proved in the record process |
| s2b-C1 | security | 3 | chosen | `fs-records-s2b-c1.pv` | TRUE: `inj-event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m)) ==> inj-event(FsSent(server_to_beacon,s,b,kid,root_2,t,m)) is true.` | Record agreement: every Beacon acceptance of (t, m) is matched by its own allocation of t for m (injective) |
| s2b-C3 | security | 3 | chosen | `fs-records-s2b-c3.pv` | TRUE: `event(FsReceived(d,s,b,kid,root_2,t,m1))@i && event(FsReceived(d,s,b,kid,root_2,t,m2))@j ==> i = j is true.` | No sequence is accepted twice in one session |
| s2b-C4 | security | 3 | chosen | `fs-records-s2b-c4.pv` | TRUE: `not event(FsFarAccepted(server_to_beacon,s,b,kid,root_2,t)) is true.` | No far acceptance |
| s2b-S1 | security | 3 | fresh | `fs-records-s2b-s1.pv` | TRUE: `event(FsSent(server_to_beacon,s,ed_public(k),kid,root_2,t,m)) && attacker(m) ==> attacker(k) is true.` | Secrecy of fresh response payloads and taskings for peers whose identity secret the attacker does not hold |
| s2b-A3 | witness | 1 | fresh | `fs-records-s2b-a3.pv` | FALSE: `not event(FsBeaconFinishOpenedLater(s,b,t)) is false.` | The finish opens a later genuine frame before the gate |
| s2b-C5a | witness | 2 | fresh | `fs-records-s2b-c5a.pv` | FALSE: `event(FsReceived(server_to_beacon,s,b,kid,root_2,3,m3))@i && event(FsReceived(server_to_beacon,s,b,kid,root_2,2,m2))@j ==> i > j is false.` | Sequence 3, then the cached sequence 2 |
| s2b-C5b | witness | 2 | fresh | `fs-records-s2b-c5b.pv` | FALSE: `event(FsReceiveRejected(server_to_beacon,s,b,kid,root_2,t))@i && event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m))@j ==> i > j is false.` | A forged frame at t rejected, then the genuine t accepted |
| s2b-C5c | witness | 2 | fresh | `fs-records-s2b-c5c.pv` | FALSE: `event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m))@i && event(FsReceiveRejected(server_to_beacon,s,b,kid,root_2,t))@j ==> i > j is false.` | A frame at an accepted sequence rejected (replay-rejected witness) |
| s2b-S4 | witness | 1 | fresh | `fs-records-s2b-s4.pv` | FALSE: `not (event(FsSent(server_to_beacon,s,b,kid,root_2,2,m)) && attacker(m)) is false.` | An attacker-registered peer reads its tasking at sequence 2 |
| s2b-C-RETAIN-C1 | control | 3 | fresh | `fs-records-s2b-c1.pv` with `fs-control-retain.pvl` | FALSE: `inj-event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m)) ==> inj-event(FsSent(server_to_beacon,s,b,kid,root_2,t,m)) is false.` `(but event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m)) ==> event(FsSent(server_to_beacon,s,b,kid,root_2,t,m)) is true.)` | Cached key kept after a successful open: C1 false |
| s2b-C-RETAIN-C3 | control | 3 | fresh | `fs-records-s2b-c3.pv` with `fs-control-retain.pvl` | FALSE: `event(FsReceived(d,s,b,kid,root_2,t,m1))@i && event(FsReceived(d,s,b,kid,root_2,t,m2))@j ==> i = j is false.` | Cached key kept after a successful open: C3 false |
| s2b-C-NOGATE | control | 1 | fresh | `fs-records-s2b-a1.pv` with `fs-control-nogate.pvl` | FALSE: `inj-event(FsBeaconEstablished(s,b,init_2,kid,root_2,ad,p)) ==> inj-event(FsServerCommitted(obj_2,s,b,init_2,kid,root_2,ad,p)) is false.` `(even event(FsBeaconEstablished(s,b,init_2,kid,root_2,ad,p)) ==> event(FsServerCommitted(obj_2,s,b,init_2,kid,root_2,ad,p)) is false.)` | No sequence-one gate: A1 false (HB-95) |
| s2b-C-STALE | control | 3 | fresh | `fs-records-s2b-c3.pv` with `fs-control-stale.pvl` | FALSE: `event(FsReceived(d,s,b,kid,root_2,t,m1))@i && event(FsReceived(d,s,b,kid,root_2,t,m2))@j ==> i = j is false.` | A failed open restores the state before the previous success: C3 false |
| s2b-C-FAILMUT | control | 2 | fresh | `fs-records-s2b-c5b.pv` with `fs-control-failmut.pvl` | TRUE (inverted control): `event(FsReceiveRejected(server_to_beacon,s,b,kid,root_2,t))@i && event(FsReceived(server_to_beacon,s,b,kid,root_2,t,m))@j ==> i > j is true.` | A failed open consumes its target: the C5b correspondence true |

A FALSE result must come with exactly one reconstructed trace, a TRUE result with none. The C5 witnesses are correspondences expected to be FALSE. C-FAILMUT is an inverted control: its mutant must make the C5b correspondence TRUE, which shows that keeping the entry state after a failed open is what makes C5b reachable. Its class is control; the checker accepts a TRUE line without a trace only for a control marked as inverted, and the manifest has exactly one.

Measured traces of the FALSE results (all in one honest session unless stated): A3, the genuine sequence-3 tasking is spliced into the response in place of the sequence-one frame, and the finish opens it before the gate; S4, an attacker identity registers, the Server builds its response and sends it the sequence-2 tasking, which the attacker opens; C5a, the Beacon accepts 3 (caching 2) and then 2 from the cache; C5b, a forged frame at 3 is rejected and the genuine 3 is accepted; C5c, the genuine 3 is accepted and then an adversary frame at 3 is refused, so the refused frame is not the genuine one, which is why C5c is read together with C3 (E22); C-RETAIN, 3 is accepted, 2 is accepted from the cache, and the same frame at 2 is accepted again; C-STALE, 3 is accepted (caching 2), a forged frame at 2 fails the cached open and restores the state left by the finish, and the genuine 3 is accepted again; C-NOGATE, the Server's later tasking carries the prefix `RegistrationKeyIdBinding(sender_id_le64(a))` for an adversary value `a`, the attacker withholds the response and delivers one with outer key ID `a` and the sequence-3 tasking in place of the sequence-one frame, and the gate-less finish opens it, accepts the binding and commits (the HB-95 substitution, as in P0).

## Results of the serial verification pass

The verification record is one serial run of `make -C beaconcrypt-core check-proverif-fs`, the registration targets followed by the record targets, recorded with the commit after the one that adds this scenario. Before it, every record target ran once as its own ProVerif process, one after another, in development runs with the checker's loader, the shared ProVerif lock, the 1800 s timeout and the 10 GiB address-space cap (`ulimit -v`), timed by GNU `time`; each gave its exact expected result lines and trace count. The C1 and C4 runs used the same model before the receive step was moved into its own file, which changed only the file layout.

| Target | Class | K_r | Verdict | ProVerif time (s) | Peak RSS (KiB) |
| --- | --- | --- | --- | --- | --- |
| s2b-A1 | security | 3 | TRUE | 0.70 | 135932 |
| s2b-A2 | security | 3 | TRUE | 0.77 | 132016 |
| s2b-C1 | security | 3 | TRUE | 1138.57 | 6631280 |
| s2b-C3 | security | 3 | TRUE | 982.00 | 6111364 |
| s2b-C4 | security | 3 | TRUE | 247.66 | 2043420 |
| s2b-S1 | security | 3 | TRUE | 0.50 | 125220 |
| s2b-A3 | witness | 1 | FALSE (reachable) | 0.16 | 33832 |
| s2b-C5a | witness | 2 | FALSE (reachable) | 20.40 | 671808 |
| s2b-C5b | witness | 2 | FALSE (reachable) | 26.31 | 945956 |
| s2b-C5c | witness | 2 | FALSE (reachable) | 18.16 | 671076 |
| s2b-S4 | witness | 1 | FALSE (reachable) | 0.12 | 27564 |
| s2b-C-RETAIN-C1 | control | 3 | FALSE (expected) | 517.13 | 4397480 |
| s2b-C-RETAIN-C3 | control | 3 | FALSE (expected) | 389.97 | 4096096 |
| s2b-C-NOGATE | control | 1 | FALSE (expected) | 0.39 | 52728 |
| s2b-C-STALE | control | 3 | FALSE (expected) | 401.60 | 4104360 |
| s2b-C-FAILMUT | control | 2 | TRUE (expected, inverted) | 23.65 | 888228 |

The record targets took 3768.1 s of ProVerif time in these runs (62.8 minutes). The largest runs, the security results C1 and C3 in the chosen tasking form, peaked at 6.63 and 6.11 million KiB resident, about 63% and 58% of the 10 GiB cap, and C1 used 63% of the 1800 s cap. At K_r = 2 the C5 witnesses and C-FAILMUT take seconds, where P0 needed 1369 s and 92% of the memory cap for C5b at K_r = 3.

## Fail-stop measurement

The fail-stop form (E21) ends the receive worker after a failed open of a parsed frame (a failed cached open, a failed future open or a failed far open); a rejected old target keeps the worker running, because it is rejected before any open. G0 asked for a measurement in s2b. It was made on a scratch copy of the receive step, in the configuration of the security results (chosen taskings, K_r = 3), on 2026-10-04 under the same lock, timeout and cap as every other run:

| Query | Failure-interleaving form (used) | Fail-stop form (measured only) |
| --- | --- | --- |
| C1 | TRUE, 1138.57 s, 6631280 KiB | TRUE, 270.89 s, 2570020 KiB |
| C3 | TRUE, 982.00 s, 6111364 KiB | TRUE, 219.29 s, 2349528 KiB |
| C4 | TRUE, 247.66 s, 2043420 KiB | TRUE, 71.05 s, 1006156 KiB |

Fail-stop is about four times cheaper here and gives the same verdicts. It is not used: the failure-interleaving form fits the caps, it needs no trace-mapping argument (E21, which rests on the pending failure neutrality L3), and it is the only form that can express C5b, C5c, C-STALE and C-FAILMUT. If later stages need the time, fail-stop is the measured option for the claims that do not mention `FsReceiveRejected`, together with a written E21 argument. The times in the first column are those of the development runs listed above.

## What the bounds do not cover

The security results hold for unbounded Server objects, honest Beacons and attacker identities, each Server object processing one bundle and sending two taskings, and each Beacon making three receive attempts after its finish, with positions up to T_max = 3 materialised. A Server object's third or later tasking, a Beacon's fourth or later receive, and anything after a peer direction's first far acceptance are not covered; the arbitrary-depth facts are the Lean side's (OD1), and these bounded results do not discharge global closure item 1 (arbitrary reached committed states). The scenario has no Beacon-to-Server records (stage P3), no compromise or reveal (stage P7), and no strong secrecy (stage P5). The theory is `crypto.pvl`, so the results say nothing about same-role DH equalities, X25519 encoding aliases, low-order points or ML-KEM implicit rejection (F13, stage P4). The response payload is fresh; S1 and S4 are about fresh tasking bytes behind any prefix, and the adversary-chosen prefix itself is never secret. Every model Beacon pins the honest Server key and ID, and every Server object has the modelled identity key and `server_kid` (E3, E23).

## Beacon pins

In this scenario a Beacon outputs nothing after its bundle: its finish and its receive attempts publish nothing (the `Some`/`None` bit is not published). The P1 argument therefore carries over: model Beacons that all pin the honest Server key produce exactly the bundles and the attacker knowledge of Beacons with arbitrary pins, so A2 (whose `FsBeaconStarted` pin is left free) and the Server-side S1 and S4 read as statements about any Beacon. A1, C1, C3 and C4 are about Beacons that pin the honest Server key, the deployment of the [threat model](../threat_model.md).

## Gates and wiring

- `PROVERIF_FS_SCENARIOS` holds `fs-registration` and `fs-records-s2b`; `check-proverif-fs` runs both runners with `-j1`, so every target of the group runs one after another. The parallel 35-scenario roster is unchanged.
- `check-proverif-fs-records-s2b` runs the checker regression test and then `check-free-schedule.py --scenario fs-records-s2b` with the fs timeout, address-space cap and optional log directory; `check-proverif-fs-registration` now passes `--scenario fs-registration`. Without `--scenario` the checker runs every target.
- The checker loads `production-transcript-interface.pvl`, `crypto.pvl`, `extraction/lib.pvl`, `fs-common.pvl`, the window, gate and taskings libraries, `fs-records-s2b-receive.pvl`, the bound file and `fs-records-s2b.pvl`, then the query file. It rejects a record target that loads two mutants, a control that loads none, a security result below K_r = 3, S1 or S4 with adversary-chosen plaintexts, an inverted target that is not a control, a query file of another scenario, and any record query file that no target uses.
- The transcript-fidelity test now has 24 tests. `free_schedule_records_s2b_model_is_pinned` checks the Rust order of the Server object, the Beacon and the receive step, the exact text of every hook and control library and of the bound files, the counts of each event in the receive step, and ten mutations. The other fs tests now also pin the record roster and runner, the 84 record citations and the record target manifest with its classes, bounds and forms.
- `check-inventory.sh` records 148 handwritten ProVerif files, the `_to_bitstring` counts 20 and 23, 24 transcript-fidelity tests, and tripwires for the record runner and its place in the serial fs roster.

## Deviations from the plan

- **Files.** The plan named one shared `fs-records.pvl` with the send and receive macros and a single `fs-records-s2b.pv`. P2 uses scenario-specific libraries (the receive step, the bound files, the hook libraries and the process) and one query file per target, in the style of P1; P3 may factor out what the two record scenarios share.
- **Witnesses and controls at K_r = 1 or 2.** P0 ran every s2b query at K_r = 3. Following the orchestrator's decision, witnesses and controls run at the smallest K_r that exhibits them ([step 10](#model-steps-and-their-justifications)); this cut the cost of C5b from 1369 s at the memory edge in P0 to under a minute.
- **The build input carries no test** ([step 3](#model-steps-and-their-justifications)), unlike fs-registration, whose objects continue after a drop.
- **`FsReceiveRejected` is not emitted for a failed far open**, unlike the P0 spike, which emitted it in every rejection branch ([step 9](#model-steps-and-their-justifications)).
- **C-STALE restores the state left by the finish**, which is the plan's "state from before the previous success" at K_r = 3 ([step 11](#model-steps-and-their-justifications)).
- **C-FAILMUT is an inverted control.** The plan keeps it only if ProVerif proves the unreachability; its expected verdict is therefore TRUE, which the checker allows only for a control marked as inverted. Its mutant leaves the far branch unchanged.
- **The replay-rejected witness is named C5c**, and the s2b half of S4 is stated at sequence 2, so that it witnesses a later tasking rather than the registration payload.
- **A2 is re-proved** in the record process (G0 section 3.5), in the chosen tasking form.
- **Adversary-chosen plaintexts** (L6 item 4) are covered by a per-tasking choice between the fresh form and a whole adversary-chosen plaintext; the plan's single attacker-input send step would have covered only one sequence.
- **`fs-common.pvl` comments** were aligned with the reviewed L6 reference (field kinds, and the use of failure-cause events by controls). No declaration changed.
- **The registration runner** now passes `--scenario fs-registration`, so that each runner checks only its own targets. The fs-registration targets and their expected results are unchanged.
- **The fail-stop form was measured but not used** ([step 12](#model-steps-and-their-justifications)).

## Open items for P3

- The record scenario `fs-records-b2s`: the Beacon send worker and the Server receive worker with routing on the claimed sender, C2, C3 and C4 for Server receives, UKSr, S2, the b2s half of S4, the record-form C-UKS on UKSr, and A1 and A2 re-proved. It can reuse the receive-window hook style and the checker's scenario selection of P2. Adversary-chosen Beacon plaintexts (E7) can follow the chosen tasking form here, with S2 and UKSr kept on fresh plaintexts (the L6 review's finding 1).
- E3 for the b2s Server-side security claims: Beacons send frames after a pin-dependent finish, so pin independence is open there, A2 re-proved in b2s included.
- The b2s half of the direction-split argument E19, and a review of the two arguments written in this guide (E20 and the s2b half of E19).
- The paper obligations L1 to L5, on which every Rust reading of the fs results rests.
- The budget: the record targets take about an hour of serial ProVerif time and the registration targets about 44 minutes, so the fs group needs about 1.8 h of the 3 h of OD7, which leaves about 1.2 h for `fs-records-b2s` (G0 measured 5 to 44 minutes for its formulations). The final pass of this stage records the exact figure.
- Stage P4 (the all-zero check and a theory with low-order points) and stage P5 (strong secrecy, which must publish the `Some`/`None` bit of receives and finishes).
