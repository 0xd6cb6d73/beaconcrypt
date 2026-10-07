# Handoff item 3: design of the common computational/symbolic experiment (plan, revision 2)

Snapshot of the working plan, copied on 2026-10-08 from the scratch file `/tmp/bc-arc-scratch/common-experiment/plan.md` (SHA-256 `a4da496e70b1e8a661d7a4820793973be80d11294b5870086933759d324396f9`). The authoritative decisions are in its numbered decision sections (sections 19 to 32); later changes live in the scratch copy until the next integration.

Status: design plan only. Revision 1 was written on 2026-10-06 from a read-only survey of the central worktree `/tmp/beaconcrypt-authenticated-root-completion` at `bccd853e` (branch `codex/full-proof-composition`; status shows only the three owner dirt paths), the two maps in this directory (`map-computational.md`, `map-symbolic.md`) and the item 2 plan `/tmp/bc-arc-scratch/extract-design/plan.md` (revision 2 with its §16 owner decisions). Revision 2, written the same day, answers the adversarial critique `critique.md` in this directory. Every critique point was re-verified against the source at `bccd853e` before it was adopted (section 18), and the re-check found four further facts that change the design (N1-N4 in section 18). Nothing was edited, committed or pushed outside this scratch directory. Revision 1 ran one scratch Lean probe, `probe/CommonProbe.lean` with log `probe/CommonProbe.log`, under `/tmp/bc-arc-scratch/lean.lock` with Lean 4.34, `-j1 -M8000`, timeout 180, the stage D `LEAN_PATH` (`/tmp/bc-arc-scratch/accept-cut-join/stage-d/leanpath`) and no `-o` output; it failed only on one guessed VCVio name (`probEvent_uniformFin`), on which nothing depends. Revision 2 ran no Lean, ProVerif or Nix command: every new citation below was read from source with its namespace and line checked.

Prefixes: `C/` is `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/`; `PV/` is `beaconcrypt-core/proofs/pro-verif/`; `VC:n` is line n of `PV/verdict-classes.tsv` (line 1 is the header); `R/` is `beaconcrypt/src/` and `K/` is `beaconcrypt-core/src/` of the central worktree (the authoritative Rust basis, which contains the sequence-one fix `5cbd76e`; `main` and `vcvio` do not). "source14" is `PqxdhRegistrationJointRevealSchedule.Spec` (9 schedule kinds plus 5 Beacon field reads). "CE" is the common experiment designed here. "Family A/B/C" follow `map-computational.md` §0: A is the R1 registration line (ServerAuth, source14, T1-T6), B is the HB-111/112 generated-target line (fixed HKDF, correlated Extract family), C is the record and CTX components over supplied role states. T4 is `actual_le_real`, T5 `authenticated_selected_kem`, T6 `branchRaw_opaque`; T7/T8 are item 2's ideal-key transfer and its composition with T5.

## 0. Summary

1. CE is one game, the approved deployment experiment. It has a single protected Server identity (generated seed, never disclosed), dynamically created honest Beacons with adversary-chosen pins, raw scheduling of accept, build and finish, record send and raw receive on every installed Server peer and every established Beacon, the two restricted random oracles of route R1 (zero-salt 192-byte Extract slice and BLAKE2b), a public transcript, optional test and fresh-message commands, and an adaptive final output. Every adversary query is answered by the production code paths already modelled in Lean: source14 for registration, `RawCtxServerMixed.serverImpl` and `RawCtxBeaconLifecycle.beaconImpl` for records. Four fidelity deviations are recorded (section 3.9): `create` runs runtime initialization only at Server birth, public getters are omitted, snapshot APIs and pre-Phase-1 helpers are omitted, and the build payload is adversary-chosen.
2. The approved reveal profile is empty for honest secrets (Π = ∅): no Server state, pending token, Beacon field or ratchet state is ever disclosed to the CE adversary, and CE has no reveal command at all. The only compromise in scope is static: identities the adversary generates itself and Beacons it pins to such identities (AnyPin). Under Π = ∅ the handoff's "approved reveals and freshness, compromise timing within scope" requirement is met vacuously, and the cut-time versus whole-run freshness question of `doc/impl/registration-accept-kem-join.md` is moot rather than resolved; any later approved reveal class reopens it. The per-class timing rules are kept only as documentation (section 6).
3. The central technical decision is to define CE natively and prove one compile lemma (CE-3): the CE game for adversary `A` equals, on the public transcript and CE's local record logs, the source14 initialized game for a compiled program `compile A`. That program parses pins itself, performs every record operation locally on copies that it reconstructs from public data plus one source14 kernel read per installed peer or established Beacon, and never reads an identity, KEM, prekey or one-time field. Because T4, `KemRawCertified.ideal_close`/`real_le_ideal`, T6, item 2's T7 and the Phase-1 report machinery are stated for an arbitrary source14 program and decision, they apply to CE at theorem level. Reconstruction of a Beacon's 153-byte associated data needs its identity public key, whose only public source is its bundle bytes; CE-3 therefore needs the existing codec law `Phase1ReadBack`, so far approved only for the negative controls (owner input 14). The internal reads are proof devices that are never answered to the CE adversary (owner input 3).
4. Targets are designated by the public pair `g = (i, k)` of raw-accept ordinal (equal to the public session handle returned by `accept`) and KEM creation index. A deterministic public function `designate` maps a test or claim to at most one `g`; on the Beacon side it now also requires that the PQ key verified by accept `i` is the Beacon's own published key. Session selection is charged as the exact sum over the `N = qAccept·(count+1)` pairs, coefficient one per pair. The owner's `N·Adv(B_guess)` wording is available only if each hop also gets a signed-difference form (owner input 5). Record selection inside a session is an exact sum over keys. A1 over all Beacons is a sum over `count+1` creation indices of distinct reductions.
5. Phase-1 provenance (A2) costs no selection factor and needs no public detector: every successful raw accept is already reported at every generated index (`PqxdhRegistrationJointRawReports.report`), `PqxdhRegistrationJointAttemptOrigin.raw_origin` classifies every reached accept as issued or forged, and `PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum` bounds the monitor flag by `Σ_{t<count+1}` joint-use weak-EUF advantages with coefficient one. A2 is stated against each owner's chronological signing history, because a Beacon whose Phase-1 writer fails after signing stays Fresh and signs a new tuple on retry, in Rust and in Lean. The published-tuple readings (A2 as publication, R1', and A1's target embedding) hold on runs with no failed Fresh bundle call, a public condition, or unconditionally if the owner extends the existing control law `phase1Total` (owner input 15).
6. Version 1 has one live Server object. Several same-seed objects (OD2, ProVerif A1-delayed's cross-object builds, L1 case (iv)) cannot be compiled into single-object source14, so they form an optional extension CE-M that needs owner input and a re-proof of the source14 line over an object-indexed Server.
7. Claims are delivered in this order: deterministic replay facts (R1, C3) and authentication (A2, R1', A1 over all Beacons); the per-target key transfer (T4, IND-CCA, T6, T7) into an ideal-keys CE world; then, after items 4 and 5 and on an un-compiled CE-level ideal world (CE-11), record origin (L2, S2b, C1, C2, C4, UKSr) and weak secrecy of fresh honest messages (App, S1, S2). Left-or-right secrecy (SSX, SS) additionally needs a two-sided form of T4 only: the KEM hop is already two-sided (`KemRawCertified.ideal_close`) and T6 is an equality. Root secrecy as `attacker(root)` is not covered by a key transfer; an optional root-guess endpoint CE-RG is proposed (owner input 16).
8. Effort for item 3 proper is about 78-128 agent-days, plus 3-6 for the two-sided T4, plus 8-14 for headline assembly after items 4 and 5, plus optional stages (CE-RG 4-8, a retry-capable ServerAuth variant 10-20, the multi-object extension CE-M 30-50). Given the 40-60% underrun of the previous join, the range must be re-estimated after the widened CE-3 spike. Item 2 is implemented afterwards as its plan describes, with an empty `Ext` and with its optional stages S7 and T (owner input 6).

## 1. Facts re-checked for this plan (central `bccd853e`)

Registration core.
- source14's request type is `create pin keyId`, `bundle owner`, `accept raw`, `build session payload`, `finish owner raw`, `hmac key message`, `hash bytes`, `reveal keyId` (`C/PqxdhRegistrationSchedule.lean:125-133`). `.create` takes a parsed `Word32` pin and replies `Nat`; `accept` replies `Option Nat` (`:126,:135-143`). The handler takes one `serverSeed` and runs one shared native Server (`:146-158`; probe). The typed `create` "does not establish the preceding runtime/public-key parser admission" (`:111`).
- The raw constructor surface `PqxdhRegistrationScheduleSurface.rawCreate` runs `ensureInit` on the runtime coordinate at every call, then the 32-byte width parse `parsePin` (`= toWord32`, `C/PqxdhRegistrationScheduleSurface.lean:15-20,23-34`). `PqxdhRegistrationJointInitializedSchedule.source` runs `ensureInit` once, at Server birth, and keeps the runtime result outside the program (`C/PqxdhRegistrationJointInitializedSchedule.lean:50-60`). Rust `Beacon::try_new` calls libsodium-rs 0.2.4 `ensure_init` (a `sodium_init() < 0` check) on every call (`R/beacon.rs:65-66`).
- The session handle is the raw-accept ordinal. `nativeAccept` sets `index := state.sessions` and increments the counter before the prefix runs, on every attempt (`C/PqxdhServerAuthNative.lean:565-580`). T5's `index` counts rejected accepts too (`accept_lt`), so the public handle of a successful accept equals T5's raw-accept ordinal.
- The Server build reads the peer map only through `(state.server.peers next).isSome` (`C/PqxdhServerRegistrationPublication.lean:187` and the other occupancy sites) and inserts the new peer by `Function.update` in `publish` (`:93-99`). `revealKernel` returns the installed peer kernel and nothing else (`C/PqxdhServerAuthExperiment.lean:509-511`; probe). Restriction 3 (`:27`) and `reveal_post_registration` (`:2377`) state that this kernel stores neither chain_0 nor the sequence-one material.
- `nativeBuild` appends every successful sequence-one seal callback, including those whose writer then fails, to the native ghost inside source14's state (`C/PqxdhServerAuthNative.lean:505-520`). A source14 program never sees this ghost.
- The Beacon kernel read `JointLiveRead.localValue .kernel` returns exactly the established kernel and `none` in other phases (`C/PqxdhRegistrationJointLiveRead.lean:27-32`; probe). It is part of source14 (`C/PqxdhRegistrationJointRevealSchedule.lean:14`; probe). source14 has no read of a public key: the only field reads are identity seed, KEM secret, prekey scalar, one-time scalar and kernel (`C/PqxdhRegistrationJointLiveRead.lean:15-24`).
- `revealedAt` is defined over identity-pool reveal observations only (`C/PqxdhRegistrationJointRoutedReveals.lean:12-17`). Kernel reads cost no private-pool request (`readCap`, `C/PqxdhRegistrationJointRevealCosts.lean:23`). That a `.kernel` read and a Server `.reveal` leave the report history and the KEM transcript unchanged is still to be proved (risk 2).

Phase-1 bundles and provenance.
- Rust `get_registration_bundle` signs prekey, one-time and PQ key (`R/beacon.rs:349-354`) before `write_message(...).ok()?` (`:357`). A failure returns `None` before `mem::replace` (`:362`), so the Beacon stays `Fresh`, and a retry draws a new one-time key and signs a new tuple (`:301-302`). After a success the state is `InitSent`, so at most one bundle is ever returned. `doc/proverif-fs-event-meaning.md:114` records the same and assigns it to the pending lifecycle argument L5.
- The Lean model is the same: "the whole source continuation retains the same original state until all three signatures and serialization succeed" (`C/PqxdhLivePhase1Bundle.lean:41-54`), and its header says repeated requests "do not justify the single-bundle three-message hypothesis" (`:4`). `codec.write1` is a free function (`C/PqxdhServerAuthExperiment.lean:83-98`).
- Every successful raw accept is reported immediately, at every generated index, from its unchanged public bytes (`C/PqxdhRegistrationJointRawReports.lean:4,12-33`): "key collisions never become an ownership assumption".
- `PqxdhRegistrationJointAttemptOrigin.raw_origin` (`:34`) shows that a literal successful raw accept from any reached initialized source state either carries a complete earlier tuple of the addressed owner or has an unissued original field, "including chronological failed-writer history" and with no successful-bundle premise.
- `PqxdhJointPhase1Reports.fieldOrigin_advantage_le_sum` (`:330`) bounds the probability that the report monitor's `occurred` flag is set by `Σ_{target<count+1}` joint-use advantages, "without a field, report-position or session factor". `FieldOriginFailure` (`:87-94`) is address-free: it names a generated index whose public key verifies the candidate, unrevealed in the report history, with an unsigned field.
- `native_origin_bound` (`C/PqxdhRegistrationJointNativeOriginBound.lean:25`; probe) bounds the owner-addressed tuple-origin event of a program returning `FinalCandidate.Choice = Nat × Bytes`. `PqxdhRegistrationJointAcceptCutEuf.selected_report_bound` (`:28`) gives the same bound for the program `AcceptCut.selected work index owner fallback`, which stops at the `index`-th raw accept; `PqxdhRegistrationJointAcceptOrigin.protected_bound` (`:202`) is its cut-time KEM-key form.

Codec laws.
- `Codec` has the Phase-1 reader and writer, the Phase-2 reader and writer and the record frame reader and writer `frameRead`, `frameWrite` (`C/PqxdhServerAuthExperiment.lean:83-98`).
- `Phase1ReadBack` (Phase-1 writer output reads back to the written identity, PQ, prekey and one-time keys), `Phase2ReadBack` and `FrameReadBack` are defined in `C/PqxdhServerAuthNegativeControl.lean:55-73`. `ControlLaws.phase1Total` (`:86`: the Phase-1 writer succeeds on every candidate) is a field of the negative-control law structure. `Phase1ReadBack` and `phase1Total` are used only by the negative-control and witness modules; `Phase2ReadBack` and `FrameReadBack` are premises of `generated_authentication` (A1).
- `RawCtxServerMixed.serverImpl senderId route decode` takes its own header router and frame decoder (`C/RawCtxServerMixed.lean:42-47`). `RawCtxServerRouting.DecoderAgreement route decode` (`:59-61`) is the definition that successful full decoding agrees with header routing; it is not a premise of anything CE would reuse.

Record handlers.
- `RawCtxServerRouting.State` is a Server (`identity`, `peers : U64 → Option Peer`, `metadata`) plus `rawAttempts`; a `Peer` holds `identity`, `kernel` and `metadata` (`C/RawCtxServerRouting.lean:41-54`). source14's Server state holds a `RawCtxServerRouting.Server` (`C/PqxdhServerRegistrationPublication.lean:60-65`), whose metadata includes the identity-pool index (`C/PqxdhRegistrationJointInitializedSchedule.lean:59`).
- `RawCtxBeaconLifecycle.State` is a Beacon (`identity` seed, `identityKeyId`, `serverIdentity`, `phase`) plus `rawAttempts`; the established phase holds `control : pqxdh.BeaconEstablished`, the 153-byte associated data and the kernel (`C/RawCtxBeaconLifecycle.lean:24-42`). `beaconImpl` reads only `identityKeyId`, the phase and `rawAttempts` (`:68-78`). It is source14's `Owner` type (`C/PqxdhRegistrationSchedule.lean:19-20`).
- `pqxdh.BeaconEstablished` is the server binding and the assigned key ID (`K/pqxdh.rs:632-635`). The associated data is `build_associated_data(server identity key, beacon identity key)` (`K/pqxdh.rs:928-947`). After finish, `identityKeyId` is the assigned key ID (`R/beacon.rs:503`; `C/PqxdhBeaconPhase2Publication.lean:116,208`).
- `LivePublicObservation.Request` has `send`, `openRaw` (actual optional plaintext) and `deliver` (success bit only) (`C/LivePublicObservation.lean:16-24`).

KEM, root and authentication theorems.
- T4 `actual_le_real` (`C/PqxdhRegistrationJointKemRawBridge.lean:291`) and T6 `branchRaw_opaque` (`C/PqxdhRegistrationJointKemRawOpaque.lean:318`) are stated for arbitrary `work : OracleComp (SourceSpec KemSK) X` and `decision : X → Bool`, which reads only the program's result. T4 is one-sided (`≤`); T6 is an equality.
- `KemRawCertified.ideal_close` (`C/PqxdhRegistrationJointKemRawCertified.lean:124-135`) is already two-sided: `|Pr[sourceReal] − Pr[branch false]| ≤ Adv^{IND-CCA} + correctnessError`. `real_le_ideal` (`:140-152`) is its one-sided form, and `KemRawGame.ideal_close` (`C/PqxdhRegistrationJointKemRawGame.lean:194`) is the same bound for the plain adversary. The signed identity `oneKey_indCCAAdvantage_eq_branchDist` is used at `KemRawCertified.lean:97-110`.
- `Decided`, `GoodKem` and `KeyMatchFinal` read only the final source result (`C/PqxdhRegistrationJointKemRawBridge.lean:26-37`). The KEM game's decision reads only the public outcome and the stop status (`C/PqxdhRegistrationJointKemGame.lean:14-17`).
- T5 `authenticated_selected_kem` (`C/PqxdhRegistrationJointAuthenticatedSelectedKem.lean:252`) and `authenticated_selected_opaque` (`C/PqxdhRegistrationJointKemRawOpaque.lean:328`) both carry the `Σ_{count+1}` EUF term (probe).
- `generated_authentication` (`C/PqxdhRegistrationR1Authentication.lean:46`; probe) is singleton-only. It runs `rootExperiment … none`, with premises `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, `ReadWritable`, `Phase2ReadBack` and `FrameReadBack`, and bound Gap-DH + `(Q choose 2)·64/2^256` + `Σ_j` (record loss + schedule loss) + joint EUF. The underlying `common_authentication_with_resources` is at `C/PqxdhServerAuthCommonAuthentication.lean:64` (probe).
- In ServerAuth, `Partner` is identical root derivation by a session index before the snapshot (`C/PqxdhServerAuthExperiment.lean:616-640`). ServerAuth publishes the target's Phase 1 once, at game start, through the same bundle program, and has no target-signing oracle (`:13`). `win_frozen` (`:2254`; probe), `seal_once_per_session` (`:2350`), `build_consumes` (`:2358`) and `finish_single_shot` (`:2419`) are ServerAuth facts. Restrictions 2, 5, 9, 10 and 11 are at `:26-35`.

Replay facts.
- ServerAuth level: `PqxdhRegistrationAdmission.no_reacceptance` (`C/PqxdhRegistrationAdmission.lean:347`) is stated over ServerAuth's `acceptOracle` and `authHandler` (probe); `AdmissionStep` and `admission_invariant` are at `:280-307`.
- source14 level (namespace `PqxdhRegistrationSchedule`): `handler_admission` (`C/PqxdhRegistrationScheduleState.lean:117`), `program_consumed` (`:130`: the consumed list is a prefix-monotone, duplicate-free list across every adaptive source14 program), `build_consumes` (`:174`: the pending handle is consumed on every build result, including writer failure), `no_rebuild` (`:196`), `handler_consumed_count` and `program_consumed_count` (`C/PqxdhRegistrationScheduleLedger.lean:84,103`), `finish_terminal` (`C/PqxdhRegistrationSchedule.lean:224`) and `no_retry` (`:399`).
- Records: `PqxdhFirstRecordReplay.no_reacceptance` (`:1144`) and `first_beacon_record_integrity_replay` (`:1392`); `RawCtxKdfBudget.begin_remaining` (`C/RawCtxKdfBudget.lean:29`).

Generic tools and names.
- No generic uniform-guess selection lemma exists in `C/` or in the VCVio package of the stage D path. That package has `uniformFin` facts (`VCVio/OracleComp/ProbComp.lean:57-85`) and `probEvent_exists_finset_le_sum` (probe).
- `C/` already has five family-B `PqxdhCommon*` modules. The prefix `PqxdhDeployment*` and the name `UniformTargetSelection` are unused at `bccd853e` and are proposed below.

Rust (authoritative).
- Server: `Server` holds `consumed_registrations` per object (`R/server.rs:26-32`); `try_new` takes `(server_kid, id_seed)` (`:154-168`); `get_shared_secret` (`:332-422`) checks the consumed set, reserves, encapsulates, computes DH and runs `server_accept` and `derive_root_key_input`, and inserts the registration ID only after success; `build_registration_response` (`:424-502`) takes the token by value, checks occupancy, seals sequence one, writes and commits, and inserts the peer only on full success; core `server_prepare_commit` rejects a token whose binding differs from the building object's (`K/pqxdh.rs:847-858`); `encrypt_message` and `decrypt_message` (`R/server.rs:224-250`) route a receive by the claimed sender; the `*_and_update` and `*_json` variants additionally return ratchet snapshots. Public getters: `identity_key_kid`, `identity_pk`, `server_kid`, `pk_by_kid`, `ratchet_status` (`:173-209`).
- Beacon: `finish_registration` runs only in `InitSent` and aborts on every failure; every other phase, including `Fresh` and `FreshWithCoins`, returns `None` with no change (`R/beacon.rs:402-510`). Record operations require `Established` (`:152-174`). Public getters: `identity_key_kid`, `identity_pk`, `server_id`, `server_kid`, `pq_pk`, `associated_data`, `ratchet_status`, `get_prekey_pk`, `get_onetime_pk` (`:84-206`); `identity_pk`, `pq_pk` and `get_prekey_pk` are available before any bundle.
- Ratchet: `encrypt_message_with_ratchet` returns without a state change on empty plaintext or an exhausted sender, and otherwise advances the kernel even if the seal fails (`R/ratchet.rs:414-444`); `decrypt_message_with_ratchet` restores the entry kernel on every rejection (`:499-532`).

ProVerif inventory: 185 `security` lines at `bccd853e`. By checker: `check-general-registration.py` 61, `check-results.awk` 58, `check-free-schedule.py` 20, `check-phase2-x25519-alias.py` 12, `check-kem-controller-auth.py` 9, `check-primitive-fidelity.py` 4, `check-exact-interface-strong.py` 4, `check-tasking-origin.py` 3, `check-registration-provenance.py` 3, and 2 each for record-origin, exact-far, delayed-response, application-secrecy and active-strong-secrecy, plus 1 for registration-set. The `check-results.awk` lines are active-classical 2-15, baseline 34-47, compromise 48 and 52, failed-receive 53-58 and 69, failed-receive-compromise 70 and 73-75, live material and private application 127, 130, 132, 134 and 135, passive-classical 162-167 and passive-quantum 168-173; the active-quantum lines 16-19 are `limitation` lines, not `security` lines.

## 2. Scope fixed by owner decisions, as reflected in the design

| Decision in force | Design consequence |
| --- | --- |
| Production Rust authoritative | Every CE command is a public Rust method with its file:line anchor (section 3). Failed calls, replay and consumption follow Rust (section 5). The four deviations D1-D4 are listed in section 3.9 and need confirmation (owner input 10). |
| Ideal Server: no backup/restore, perfect key management; same-seed objects are one identity; replay claims per live state | One protected identity, generated seed (`supplied = none`). R1/R1' are stated per live Server object. Version 1 has one object; CE-M adds several (owner input 1). |
| No attacker access to running code, the ideal Server's keys or its secret state | CE has no reveal command. Internal kernel reads inside compiled programs and reductions are proof devices only (owner input 3). |
| Persistence, snapshots and codec internals out of scope | Only `encrypt_message`/`decrypt_message` are modelled, not the snapshot-returning variants. The codec is the abstract `Codec`; one codec serves registration and records (section 8 item f). The codec laws CE needs are listed in owner input 14; none is a fact about Cap'n Proto. |
| Primitives trusted | Functional contracts appear only where already approved for their lines; extensions to CE are listed per headline in owner input 13. libsodium's initialization, which has no effect after a success except on a lock-error path treated as a process-level failure, justifies deviation D1. |
| P7 not approved | Π = ∅, and the reveal command is not part of `CESpec`, so no CE theorem can be instantiated with a non-empty profile. |
| Bounded tier-B ProVerif is the symbolic deliverable | Sections 11 and 12 map targets to CE endpoints. It is a documented event/capability correspondence, not a computational-soundness theorem (owner input 18). |
| Freshness read at the accept | A2's protection is read at each accept, in the report history. Under Π = ∅ it holds for every generated owner whose identity is not read, and `compile A` reads none. |
| Fixed public target for the item 1 theorem; adversary-chosen sessions in item 3 with factor at most `qAccept·(count+1)` | Section 7: exact sum over `N = qAccept·(count+1)` designations; A2 uses no factor; A1 uses `count+1`. |
| R1 Extract-ROM extended to this line; HMAC-PRF and Extract-on-uniform accepted; `SourceFullCorrect` allowed | CE's random oracles are exactly the R1 slice and BLAKE2b. All other HMAC/HKDF evaluations are real. Item 2's T7 is instantiated through CE-3 (section 9). |
| No new assumptions without approval; never weaken or delete theorems | Every assumption CE uses is listed per headline (owner input 13) and every codec law separately (owner input 14). Where an approval is pending, the plan gives the statement that holds without it. Every statement is new; no existing statement changes. |

## 3. Oracle interface

The adversary is `A : PublicInput → OracleComp CESpec CE.Output`. `PublicInput` is the protected Server's identity public key and its key ID `serverKid` (a universally quantified parameter). `CESpec = unifSpec + Commands`. Each command below gives its Rust counterpart and the source operation that answers it in the native semantics (section 8).

### 3.1 Server construction

| Command | Rust | Native answer | Notes |
| --- | --- | --- | --- |
| (initialization, not a query) | `Server::try_new(server_kid, None)`, `R/server.rs:154-168` | `PqxdhRegistrationJointServerBirth` / `InitializedSchedule.source` with `supplied = none`; `ensureInit` runs here once | A constructor failure ends the run with no outcome, as in source14. A supplied seed is not used for any security statement (owner input 11). |
| `newServer` (CE-M only) | `Server::try_new(server_kid, Some(seed))` with the protected seed | New object with its own `control`, peer map and consumed set | Not in version 1 (owner input 1). |

### 3.2 Registration

| Command | Reply | Rust | Native answer |
| --- | --- | --- | --- |
| `create pinBytes keyId` | `Option Nat` (owner handle) | `Beacon::try_new(server_kid, server_id_pk)`, `R/beacon.rs:65-82` | Width parse `toWord32 pinBytes` (`PqxdhRegistrationScheduleSurface.parsePin`). A wrong width replies `none` with no state change and no draw. Otherwise source14 `.create pin keyId` (identity, prekey and KEM in production order) and reply `some` of its `Nat`. Runtime initialization is not re-run (deviation D1). Any pin is allowed (AnyPin). |
| `bundle owner` | `Option Bytes` | `get_registration_bundle`, `R/beacon.rs:300-399` | source14 `bundle`: generation and all three signatures precede publication; a failure keeps the owner unchanged, so a Fresh owner may sign again on a later call (section 5). |
| `accept raw` | `Option Nat` (session handle = raw-accept ordinal) | `get_shared_secret`, `R/server.rs:332-422` | source14 `accept`: an index is allocated on every attempt; the ID is consumed only on success; the pending token is stored under the handle. |
| `build session payload` | `Option Response` (serialized bytes and assigned key ID) | `build_registration_response`, `R/server.rs:424-502` | source14 `build`: the token is removed on every outcome (moved); the peer is inserted only on full success. `payload = none` selects `REGISTRATION_WITNESS` (deviation D4). |
| `finish owner raw` | `Option Bytes` (application suffix) | `finish_registration`, `R/beacon.rs:402-510` | source14 `finish`: `InitSent` only; every failure aborts; every other phase returns `none` with no change. |

### 3.3 Records (both directions)

| Command | Reply (mode O / mode P) | Rust | Native answer |
| --- | --- | --- | --- |
| `serverSend kid plaintext` | `Option Encrypted` | `Server::encrypt_message(b, k)`, `R/server.rs:224-228` | `RawCtxServerMixed.serverImpl` send on `⟨server.server, serverRaw⟩` with `senderId := identityKeyId` |
| `serverRaw raw` | `Option Decrypted` / `Bool` | `Server::decrypt_message(b)`, `R/server.rs:229-250` | `serverImpl` raw receive: route by claimed sender; every failure keeps the whole Server; `rawAttempts` increments |
| `beaconSend owner plaintext` | `Option Encrypted` | `Beacon::encrypt_message`, `R/beacon.rs:152-163` | `RawCtxBeaconLifecycle.beaconImpl` send (`Established` only) |
| `beaconRaw owner raw` | `Option Decrypted` / `Bool` | `Beacon::decrypt_message`, `R/beacon.rs:164-174` | `beaconImpl` raw receive (`Established` only; inactive attempts are counted) |

Mode O returns the actual optional plaintext (`LivePublicObservation.openRaw`). Mode P returns only the success bit (`deliver`), as the App and SSX projections do. The mode is a parameter of the game, not a choice of the adversary. Finish replies return the optional payload in both modes; that payload is adversary-chosen through `build` (or the public witness), so returning it reveals nothing the adversary did not choose. A screened mode R (plaintext except for records produced by `test` or `fresh`) is a later option (owner input 4).

### 3.4 Primitive oracles (R1)

| Command | Reply | Semantics |
| --- | --- | --- |
| `hmac key message` | 64-byte block | `publicFamily`: the lazily sampled shared table when `key = zeroSalt` and `|message| = 192`; the real HMAC-SHA-512 otherwise. The table is shared with every honest root derivation. |
| `hash bytes` | BLAKE2b-512 digest | Programmable classical random oracle, one lazily sampled cache shared with every CTX commitment. |

There is no DH, signing or KEM oracle. Public HKDF outside the slice is computed by the adversary itself with the real function, which the theorem quantifies after `setup`. This is the inherited random-oracle caveat (item 2 plan §7).

### 3.5 Reveals

CE has no reveal command. The approved profile is Π = ∅ (owner input 2). The timing rules that would apply to an owner-approved reveal class are recorded in section 6 as documentation only; adding a class would require a new interface, a new compile lemma case and owner approval, and is not a parameter of any CE statement.

### 3.6 Secrecy commands

| Command | Reply | Semantics |
| --- | --- | --- |
| `test side handle m0 m1` | `Option Encrypted` | Requires `|m0| = |m1| > 0`. The first `test` call fixes the single test session `(side, handle)` and draws the hidden bit `b`; later calls must name a handle of the same designated session (either side of it), otherwise they return `none` with no state change. The call is then exactly `serverSend kid m_b` or `beaconSend owner m_b`. Its allocation, failure and rollback behaviour is that of a send. |
| `fresh side handle ℓ` | `Option Encrypted` | Requires `ℓmin ≤ ℓ ≤ ℓmax`. The experiment samples a uniform `ℓ`-byte message `m*`, keeps it private and sends it on the handle. The ciphertext and a fresh-record handle are recorded. |

Both commands are wrappers over send, which is what lets the compiled program implement them itself (section 8). Tests and fresh messages are used only in mode P (owner input 4). CE-LOR is a single-test-session game: a statement with several test sessions needs a further hybrid over test sessions (owner input 7).

### 3.7 Final output

`CE.Output := Option CE.Claim × Bool`. The names avoid the family-B HB-114 `Decision` (`C/PqxdhAdaptiveTargetPost.lean:15`) and `PqxdhRegistrationJointFinalCandidate.Choice`, which CE-A2's fallback route uses. Interpretation per claim family:

| Claim family | What the adversary outputs | Winning event |
| --- | --- | --- |
| Authentication and replay (A1, A2, R1, R1', C3, origin, C4, UKSr) | Nothing | Predicates of the public transcript and CE's local record logs (section 4); A1 and A2 additionally use analysis state inside their own reductions (section 10) |
| Key transfer (S3, A1-root) | Arbitrary bit `D` | Compared between the real and ideal-keys worlds |
| Root guess (optional CE-RG) | `some (handle, r)` | `r` is the root of the designated session |
| Fresh-message secrecy (App, S1, S2) | `some (freshHandle, guess)` | `guess = m*` of an eligible fresh record |
| Left-or-right secrecy (SSX, SS) | `b'` | `b' = b`, counted only if the test session was eligible (section 7) |

### 3.8 Query classes and budgets

The classes `coin 0`, `create 1`, `bundle 2`, `accept 3`, `build 4`, `finish 5`, `hmac 6` and `hash 7` keep source14's numbering (`C/PqxdhRegistrationScheduleResources.lean:16-25`). CE adds `serverSend`, `serverRaw`, `beaconSend`, `beaconRaw`, `test` and `fresh`.

Budgets are all-reply caps on every attempt, rejected ones included: `qCoin`, `qCreate`, `qBundle`, `qAccept`, `qBuild`, `qFinish`, `qHmac`, `qHash`, `qSS`, `qSR`, `qBS`, `qBR`, `qTest`, `qFresh`, and a total fresh-message length `qFreshBytes ≥ Σ ℓ` (or, equivalently for the bills, `ℓmax` with `qFreshBytes = qFresh·ℓmax`). They give:
- `S = qSS + qBS + qTest + qFresh` and `R = qSR + qBR`;
- `count + 1 ≥ 1 + qCreate`, which is T5's `capacity` with `supplied = none`;
- `N = qAccept · (count + 1)`.

### 3.9 Fidelity deviations from production Rust

| # | Deviation | Justification | Status |
| --- | --- | --- | --- |
| D1 | `create` does not re-run runtime initialization; `ensureInit` runs once at Server birth. Rust calls `ensure_init()` in every `Beacon::try_new` (`R/beacon.rs:66`). | libsodium is a trusted primitive. In the vendored libsodium (libsodium-sys-stable 1.24.0, `src/libsodium/sodium/core.c`, `sodium_init`), a call after a successful initialization returns 1 without effect, and libsodium-rs 0.2.4 maps only a negative result to an error. The only remaining failure is the critical-section lock or unlock error path, which libsodium marks as excluded from coverage; D1 treats it as a process-level failure, like the allocation and RNG failures that `try_new`'s documentation already leaves outside the recoverable errors (`R/beacon.rs:62-64`). So CE omits one failure path that production has. | Owner input 10. The formal alternative is an `ensureInit` idempotence law, which is a new contract. |
| D2 | Public getters are omitted: Server `identity_key_kid`, `identity_pk`, `server_kid`, `pk_by_kid`, `ratchet_status`; Beacon `identity_key_kid`, `identity_pk`, `server_id`, `server_kid`, `pq_pk`, `associated_data`, `ratchet_status`, `get_prekey_pk`, `get_onetime_pk`. | As in ServerAuth restriction 11 and the event-meaning capability table, each returns a value the adversary computes from public replies and its own inputs once the Beacon's bundle is public (each `ratchet_status` is to be checked in CE-13). The exception is availability: Rust exposes a Beacon's identity, PQ and prekey public keys before its first bundle; CE does not. No CE proof uses the secrecy of a public key, but CE's adversary is weaker by this early knowledge. Adding these getters later is not possible under CE-3 without a public-key read in source14 (fallback (b) of section 8), because source14's only field reads are secret reads, which would falsify `revealedAt` or `GoodKem`. | Owner input 10. |
| D3 | Snapshot-returning record APIs (`*_and_update`, `*_json`) and the Beacon pre-Phase-1 helpers (`new_onetime_keypair`, `delete_onetime_keypair`, `delete_pq_keypair`, `R/beacon.rs:222-296`) are omitted. | Snapshots are out of scope. The helpers only replace coins before Phase 1 or abort, which a garbage finish also achieves (ServerAuth restriction 11). With the helpers omitted, `FreshWithCoins` is unreachable in CE. | Owner input 10. |
| D4 | The adversary chooses the build payload. | Stronger than Rust, where the host chooses it (ServerAuth restriction 6). | Recorded. |

## 4. State, ghost and public transcript

```text
structure CE.State (KemSK) where
  joint     : PqxdhRegistrationJointSchedule.State KemSK
              -- private identity/KEM service pools and handles; shared NativeState:
              -- R1 slice cache, BLAKE2b cache, the Server object (peers, control, identityKeyId, consumed),
              -- pending tokens by session, session counter, native registration ghost; owners (with rawAttempts)
  serverRaw : Nat                                      -- RawCtxServerRouting.State.rawAttempts of the Server
  links     : List (Nat × Option Std.U64)              -- public: build replies (session handle ↦ assigned key ID)
  test      : Option (Bool × Designation × Nat)        -- hidden bit, designated session, number of tests
  fresh     : List (FreshHandle × Side × Handle × Bytes)  -- private messages m*
  logs      : CE.Logs
structure CE.Logs where
  transcript : List CE.PublicEntry                     -- (request, mode-projected public reply), chronological
  produced   : List (Side × Handle × Seq × SealContext)  -- every successful record seal callback, failed writers included
  published  : List (Side × Handle × Seq × Bytes)      -- only successfully returned record ciphertexts
  received   : List (Side × Handle × Bytes × Option (Seq × Bytes × Frame))  -- every raw record attempt with optional decode
```

The public transcript is the projection seen by the adversary: coins, every request and its reply after the mode projection. In ProVerif terms this is the frame. Bundle bytes, build responses and send ciphertexts are outputs on the public channel (event-meaning V1). Plaintext replies are local returns (V2); they are public only in mode O, which is stronger than the symbolic observer. The Some/None bits are E11.

`CE.Logs` concerns records only. `compile A` reproduces it exactly, because it runs the same record handlers locally and answers their seal callbacks itself (section 8). The native registration ghost inside `joint` (sequence-one seals by session, including writer-failed ones, and the ServerAuth-style touch log) is not reproducible by `compile A`. It is not part of the CE-COMPILE projection and is used only by the A1 reduction `R_c` through ServerAuth's own ghost (section 10). No root value or root coordinate is a CE observable.

Public functions of the transcript used below (each a CE-5 obligation):
- `phase c`: `Fresh` after `create`; `InitSent` after a `some` bundle; `Established` after a `some` finish in `InitSent`; `Aborted` after a `none` finish in `InitSent`.
- `owner k`: the handle whose `create` drew KEM creation index `k` (every source14 `create` draws one KEM pair and nothing else draws one; to be confirmed in CE-5).
- `NoBundleFailure c`: no `bundle c` call made while `phase c = Fresh` replied `none`. `NoBundleFailure` is the conjunction over all owners.
- `designate` (section 7).

## 5. Replay, consumption and failed-operation rollback

| Operation | CE representation (inherited from the native handler) | Lean source | Rust |
| --- | --- | --- | --- |
| Bundle | Generation and three signatures precede the writer. Any failure keeps the owner unchanged, so a Fresh owner may sign several tuples (one per attempt) but returns at most one bundle. Failed attempts' keys and signatures are never output. | `C/PqxdhLivePhase1Bundle.lean:4,41-54`; signing history used by `raw_origin` | `R/beacon.rs:300-399` |
| Accept | A session index is allocated on every attempt. The consumed-ID status is checked in the prefix. The registration ID (identity/one-time pair) is consumed only on success, in the live Server object's `consumed` list. A rejected accept leaves no token. | `C/PqxdhServerAuthNative.lean:565-580`; source14 `PqxdhRegistrationSchedule.handler_admission`, `program_consumed` (`C/PqxdhRegistrationScheduleState.lean:117,130`) | `R/server.rs:353-421` |
| Build | The token is removed before building, on every outcome (moved). A diagnostic result keeps the old Server. The peer is inserted only on full success. The key ID comes from this object's counter; occupancy is checked. | source14 `build_consumes`, `no_rebuild` (`C/PqxdhRegistrationScheduleState.lean:174,196`) | `R/server.rs:424-502` |
| Finish | `InitSent` only. Every failure aborts and erases the prekey, one-time and KEM fields. Every other phase (`Fresh`, `FreshWithCoins`, `Established`, `Aborted`) returns `none` with no change. No retry is possible. | `finish_terminal`, `no_retry` (`C/PqxdhRegistrationSchedule.lean:224,399`) | `R/beacon.rs:402-510` |
| Send | An empty plaintext or an exhausted sender returns `none` with no change. Otherwise the allocation is consumed even if the seal or writer fails; production and publication are logged separately. | `C/RawCtxSourceSend.lean:5` | `R/ratchet.rs:414-444` |
| Raw receive | Routing by claimed sender inside the Server; Beacons check the stored Server key ID. Every rejection restores the entry kernel and the whole Server or owner; primitive effects (BLAKE2b cache entries) persist. Success consumes the slot. Every attempt increments `rawAttempts`. | `RawCtxServerRouting` header and `rawGame_cases` (`:130`); `RawCtxWholeOwner.lean:103-178` | `R/ratchet.rs:499-532`; `R/server.rs:233-250` |
| Replay | Record replay is a deterministic consequence of slot consumption on the same live owner (C3: zero loss). Registration replay is per live Server object (R1). Cross-object replay exists only in CE-M and is the expected R4 limitation. | HB-105 no-repeat/no-intersection facts; `PqxdhFirstRecordReplay.no_reacceptance` (`:1144`) as the first-record precedent | as above |

The ServerAuth facts `PqxdhRegistrationAdmission.no_reacceptance`, `seal_once_per_session`, `build_consumes` and `finish_single_shot` are proof templates only; CE-R1 and CE-C3 are new proofs over `CE.handler` (section 10). State ownership and replay history are execution premises of CE, not consequences of key secrecy (`doc/composition-assumptions.md:35`). Failed attempts are never free: every class counts attempts, so timing arguments count attempts rather than successes (`doc/impl/live-getter-source-profile.md:61`).

## 6. Freshness, eligibility and compromise timing

Compromise in scope is static. Adversary-generated identities exist from their first use as raw bytes; AnyPin Beacons are pinned at creation. No generated Beacon secret and no Server secret is ever disclosed to the CE adversary. Consequently:
- the handoff's "approved reveals and freshness" and "compromise timing within scope" are met vacuously under Π = ∅. They are moot, not discharged; a later approved reveal class reopens them, including the cut-time `Protected` versus whole-run `GoodKem` question of `doc/impl/registration-accept-kem-join.md`;
- `doc/composition-assumptions.md:33` still lists reveals of identity, root, current-chain and skipped-key state among the capabilities a composition theorem must cover. CE-13 must amend that text to say that the approved experiment has none, and only after owner input 2 confirms it.

Two facts about `compile A` replace revision 1's freshness lemmas (CE-5):
- `approved_goodkem`: `compile A` issues no KEM read, so `GoodKem k` holds over the whole run for every `k`.
- `kernel_reads_unrevealed` (risk 2): `compile A`'s `.kernel` reads and Server `.reveal` queries add no entry to the identity-reveal history of the report machinery. A2 needs this, because `FieldOriginFailure` requires the reported identity to be unrevealed.

Revision 1's `approved_protected` ("`Hit_g` implies `Protected`") is dropped. It is false for Beacon-side designations, because nothing ties session `i`'s identity to owner `k`, and section 9 uses T4, not T5.

`compile A` reads the designated session's kernels, so the component freshness predicates `RawCtxLiveLineage.Fresh`, `RawCtxSelectedMessageFreshness.Clear` and `RawCtxSelectedMessageReveals` are false when instantiated on `compile A`. They may be instantiated only on the CE adversary in the un-compiled ideal world of CE-11 (section 9, step 9.6).

Documentation only: timing rules if the owner later approved a reveal class. They follow the item 2 plan §8, `doc/composition-assumptions.md:35` and the existing predicates. None is part of `CESpec`.

| Class | Horizon | Effect on a target `g = (i, k)` | Existing predicate |
| --- | --- | --- | --- |
| Beacon identity of owner `c` | For A2: unrevealed at each accept under that identity (the cut-time reading). For A1: no Beacon secret is ever revealed (ServerAuth restriction 2; KCI is not claimed). | Secrecy of session `g` rests on the KEM secret, so an identity reveal does not break item 2's ideal keys. | `AcceptOrigin.Protected` (`C/PqxdhRegistrationJointAcceptOrigin.lean:40`); `FieldOriginFailure` |
| Beacon KEM key `k` | Whole run | Ends every claim about `g`. No forward secrecy against a later KEM disclosure. | `KemRawBridge.GoodKem` (`:30`); `PqxdhDynamicKemStopping.Good` |
| Beacon prekey, one-time | Never, for A1 (ServerAuth restriction 2) | Harmless to key secrecy (entropy from the KEM). | n/a |
| Beacon kernel, Server peer kernel of session `g` | At the read, with stopping | Discloses that chain and all its descendants; no post-compromise recovery. Retained skipped keys expose past targets. | `RawCtxLiveLineage.Fresh` (`:75`); `RawCtxSelectedMessageFreshness.Clear`; `RawCtxSelectedMessageStopping.Good` |

## 7. Target designation and selection

Designation. The public function `designate` returns `some (i, k)` exactly when the claim's session is one of the following, choosing the smallest such `i` (and the smallest `k` if several owners publish equal keys):

- **Server-side session** (a test or fresh record on a Server peer `kid`, or an origin claim on that peer). `links` gives the session `i` whose build returned `kid`. The verified candidate of `accept i` (`RawSignatures.verified` on the public accept bytes) carries the identity key and the PQ key read from the published bundle of `owner k` (codec readers on the public bundle bytes). With `Phase1ReadBack`, the PQ-key equality gives `KeyMatchFinal k`, and the identity equality matches the SSX s2b eligibility "accepted identity is the selected B".
- **Beacon-side session** (a test, fresh record or origin claim on owner `c`, with `k` the KEM creation index of `c`). `c` is established and pinned to `(S, serverKid)`. The ciphertext read from `c`'s accepted finish input equals the ciphertext read from the build response of session `i`, AND the PQ key verified by `accept i` equals the PQ key read from `c`'s published bundle. The second conjunct is new in revision 2: without it, an adversary that registers its own PQ key as session `i` and forwards `i`'s ciphertext to `c` makes `designate` return `(i, k)` while `KeyMatchFinal k` is false. With it and with `Phase1ReadBack` and `Phase2ReadBack`, `c` decapsulates exactly the challenge ciphertext of `(i, k)` under key `k`. No identity condition on session `i` is needed. With item 2's optional stage T (the owner of `k` decapsulates at most once) and S7 (every hidden entry ideal), `c`'s root is a hidden entry in the ideal-keys world whether or not `c` partners session `i` (owner input 6).
- **Other cases.** A session with no such `(i, k)`, for example an attacker identity on the Server side, an attacker-encapsulated ciphertext or an index outside the budget, is ineligible: `designate` returns `none`.

These designations are narrower than the symbolic eligibility notions. Section 9 gives corollaries that recover the symbolic ones with one global term each.

Selection policies by claim.

| Claim | Policy | Factor |
| --- | --- | --- |
| A2 (signing history) | No selection. Every successful accept is already reported in the report run; the monitor flag is bounded with coefficient one (section 10). | none; `Σ_{t<count+1}` joint EUF |
| A2 (publication), R1' | As A2, on `NoBundleFailure` runs (or unconditionally with `phase1Total`, owner input 15) | none |
| R1, C3 | Deterministic | none |
| A1 (all Beacons) | Sum over Beacon creation index `c` of distinct reductions `R_c` (the violation, "no partner", is not public) | `Σ_{c<count+1}` ServerAuth losses |
| Key transfer, origin, C4, UKSr, App, SSX, (RG) | Exact sum over designations `g` | `Σ_g` over `N = qAccept·(count+1)` terms |
| Record keys inside the designated session | Exact sum over key indices with coefficient one (`AdaptiveRawKeySelection`, HB-127 all-attempt sums) | none beyond the sum |

The generic lemma, new and assumption-free (CE-4, module `UniformTargetSelection`):

```text
-- split form (the headline form): designate is a function of the outcome; E ω → designate ω ≠ none
Pr[E ∧ elig | run] = Σ_g Pr[E ∧ designate = some g | run]
-- event form: run does not use g
Pr[E | run] = N · Pr[fun (g, ω) => E ω ∧ designate ω = some g | do let g ← $ᵗ Fin N; let ω ← run; pure (g, ω)]
-- advantage form: elig ω ↔ designate ω ≠ none, and b is drawn inside run at the first test
Pr[b' = b ∧ elig] − ½·Pr[elig] = Σ_g (Pr[b' = b ∧ designate = some g] − ½·Pr[designate = some g])
```

All three are exact. The headline composes the split form with the per-`g` hops, each of which is stated with an absolute advantage (`IND_CCA_Advantage`, `boolDistAdvantage`), so the headline is `Σ_g (…)`. Because `Σ_g |d_g| ≥ N·|avg_g d_g|`, the owner's `N · Adv(B_guess)` wording, where `B_guess` draws `g` uniformly and runs `B_g`, does not follow from absolute hops. It follows only if every hop on the path also has a signed-difference identity for the guessing reduction. One exists for the KEM hop (`oneKey_indCCAAdvantage_eq_branchDist`); none is stated for item 2's T7 hops or for items 4 and 5. CE-4 therefore delivers the `Σ_g` form, and the `N·Adv(B_guess)` form is an optional corollary that adds signed variants to the scope of CE-10 and CE-12 (owner input 5). The target domain is fixed before the run because `qAccept` and `count` are budget parameters.

## 8. Native semantics and the compile lemma

`CE.game mode A` runs `A` under `CE.handler`. Registration, `hmac` and `hash` are source14's initialized handlers on `joint`, with `create` as in section 3.2. Records are `serverImpl` and `beaconImpl` on the live native Server and owners, with their `NativeSpec` primitives answered by the same interpreter source14 uses for the honest ratchet: the shared BLAKE2b cache plus real HKDF and AEAD (`RawCtxSourceHkdf.response setup.source.crypto`). `test` and `fresh` are wrappers over send.

`compile A : OracleComp source14 X` does the following:
- it answers `create` by parsing the pin locally (`toWord32`) and issuing `.create pin keyId` only for a 32-byte pin;
- it samples the bit `b` and the fresh messages with its coins;
- it keeps a local `RawCtxServerRouting.State` whose identity is the public Server identity, whose metadata is a placeholder with `senderId = serverKid`, and whose peers are filled lazily: on the first record operation addressed to an installed key ID it issues `.reveal kid` once and installs the peer with the identity verified by the session's accept bytes (looked up through `links`) and a placeholder metadata;
- it keeps a local owner state per established Beacon `c`, filled at the first record operation on `c` by one `.kernel` read and the reconstruction of section 8 item (c);
- it runs `serverImpl` and `beaconImpl` on these copies, answers their CTX hashes by `.hash` queries, computes HKDF and AEAD locally with the real functions, and logs every seal callback and receive result into its own copy of `CE.Logs`;
- it evaluates `designate` and every CE winning event from its transcript and local logs.

Theorem CE-COMPILE (stage CE-3): `CE.game mode A` and the source14 initialized execution of `compile A`, both projected to (public transcript, `CE.Logs`, adversary output), have equal distributions. The proof is a per-handler simulation relation with these parts:

- **(a) Registration and `create`.** The registration fields of CE's native state and of `compile A`'s source14 state are equal. Registration handlers read peers only through `isSome` and never read a Beacon's established kernel. `compile A`'s local width parse followed by `.create` equals CE's `create` (deviation D1 is part of the CE definition, so this is an equality, not an approximation). `compile A` adds no `accept` or `create` query and reorders none, so raw-accept ordinals and KEM creation indices agree.
- **(b) Server-peer reconstruction.** The local Server differs from CE's native Server only in the metadata placeholders, in the peers not yet read, and in `rawAttempts`. A frame lemma shows that `serverImpl` reads the Server metadata only through `senderId` and never reads peer metadata. The peer identity used for the 153-byte associated data is the identity verified from the public accept bytes, which is the value the native build installed (same parser, same bytes). The native source14 kernel of a read peer is stale (it never advances, because source14 has no record command) and is never read again.
- **(c) Beacon-owner reconstruction.** For an established owner `c`, the local state is built from public data: `control = ⟨server binding (pin and keyId from create), assigned key ID read from c's accepted finish input with the same reader the native finish used⟩`; `associatedData = build_associated_data(pin, identity key read from c's published bundle)`; `identityKeyId` = the assigned key ID; `serverIdentity` = the pin; `identity` = a placeholder seed; `phase = established control associatedData kernel` with the `.kernel` reply; `rawAttempts` = the number of CE record attempts on `c` so far. The identity key read from the bundle bytes equals `c`'s identity public key only under `Phase1ReadBack`; this is the one place where CE-3 needs a codec law (owner input 14). A frame lemma shows that `beaconImpl` never reads `identity` or `serverIdentity` (`C/RawCtxBeaconLifecycle.lean:68-78`).
- **(d) Sampling swap.** `compile A` draws `b` and the fresh messages when CE does (at the first `test`, at each `fresh`); if an implementation draws them earlier, a sampling-swap lemma for independent draws is needed. It is trivial, but listed.
- **(e) Projection.** The projection contains only the public transcript, `CE.Logs` and the adversary output. The native registration ghost is excluded (section 4).
- **(f) Codec coherence.** CE fixes the record decoder to `codec.frameRead` and the record writer to `codec.frameWrite`, the functions source14 uses for the sequence-one seal and the finish opening, because Rust uses one codec. The Server header router `route` is either a free function with the premise `RawCtxServerRouting.DecoderAgreement route codec.frameRead`, or is defined from `codec.frameRead`, which is a deviation that needs `DecoderAgreement` to be observationally equal to production (owner input 14).
- **(g) Caches.** The shared R1 slice and BLAKE2b caches agree; records never touch the R1 slice, the pools or the tokens.

Budget transport (part of CE-3), from CE budgets to the fourteen source14 caps of `compile A`:

| source14 kind | Cap |
| --- | --- |
| `.inl 0` coin | `qCoin + qFreshBytes + 1` (the bit) |
| `.inl 1` create | at most `qCreate` (wrong-width pins issue no query) |
| `.inl 2` bundle … `.inl 6` hmac | unchanged (records never touch the R1 slice) |
| `.inl 7` hash | `qHash + S + R`, to be checked against the `S+R+H` cap of `RawCtxProtocolBudgets` |
| `.inl 8` reveal | at most `qBuild` |
| `.inr kernel` | at most `min(qCreate, qFinish)` |
| other field reads | 0 |

The local KDF work is `S + 51R` real derivations (`RawCtxKdfBudget`), charged as runtime and not as a query. No uniform work is hidden: the local AEAD and HKDF are deterministic, and the hash draws stay inside source14's `uniformCost` (64 per `.hash`).

Why this is legitimate under OD2: the CE adversary never receives a kernel. `compile A` is a program in the analysis, and the source14 theorems are quantified over all programs, including ones that read kernels. The ServerAuth bound already holds when the adversary reveals the partner's installed kernel (restriction 3). Owner input 3 asks for explicit confirmation.

Fallbacks if CE-3 fails or `Phase1ReadBack` is not approved (risks 1 and 12):
- (a) Define the advertised game directly as the source14 game of `compile A`. This is weaker fidelity: Beacon record semantics then use the associated data computed from the parsed bundle identity rather than the native one.
- (b) Extend source14 by an `Ext` of record commands and public-key reads, and re-prove T1-T6 and item 2 over `SourceSpec + Ext`. This is item 2's option (i) and its risk 14, at about +25-45 days. It would also allow the pre-bundle getters of deviation D2.

## 9. How T4-T7 instantiate into CE (reductions and losses)

For a fixed `g = (i, k)` and a CE event `E`, put `D_g := E ∧ designate = some g`. `E` must be computed by `compile A` from its public transcript, its local `CE.Logs`, its coins (`b`, `m*`) and the adversary's output; it may not mention roots, partnering or the native registration ghost. Write `W` for `compile A` and `Pr_actual` for the literal initialized execution of `tag W i`.

| Step | Statement | Source |
| --- | --- | --- |
| 9.1 | `Pr_CE[E ∧ designate = some g] = Pr_actual[Decided_{D_g} ∧ GoodKem k ∧ KeyMatchFinal k]` | CE-COMPILE; `tag_erase`; CE-5's `designate_keymatch` (with `Phase1ReadBack`) and `approved_goodkem`; `Decided` needs the selected accept to have returned a session, which `designate` requires |
| 9.2 | `≤ Pr[KemRawGame.sourceReal … D_g W … k i]` | T4 `actual_le_real`; `room` follows from `capacity` |
| 9.3 | `≤ Pr[KemRawGame.branch … false] + Adv^{IND-CCA}(KemRawCertified.adversary … D_g W … k i) + correctnessError` | `real_le_ideal`, the one-sided form of `ideal_close`; premise `FunctionalDecapsulation` |
| 9.4 | `= Pr[opaqueBranch … D_g W … k i false]` | T6 `branchRaw_opaque` |
| 9.5 | `≤ Pr[idealKeysBranch … D_g W … k i] + ε_item2(g)` | Item 2 T7 (two-sided), stated for an arbitrary `work`, here `W` |

In 9.5:
- `ε_item2(g) = (qHmac + qAccept + qFinish)/2^256 + Σ_{j<qRoot} Adv^{PRF}(indexedReduction_g j) + 4` key-schedule advantages (Ext-on-`uniform32`, PRF, Ext, PRF);
- with S7 and T, add four more key-schedule advantages for the second hidden entry;
- `qRoot = 2` with T, `1 + qFinish` without it.

In `idealKeysBranch` the kernels returned by `.reveal kid` for session `i` and by `.kernel` for owner `c` are built from the uniform `next32`/`right32` (item 2 plan §8). T5 and T8 are not used per target: they carry the `Σ_{count+1}` EUF term, and using them per `g` would cost `N·(count+1)` EUF copies. The public key match in `designate` replaces T5's authentication step, and A2 is charged once, globally, where eligibility needs it (the corollaries below).

Steps 9.6 and 9.7:
- **9.6 (precondition: CE-11).** Items 5 and 4 do not run on `idealKeysBranch(W)` directly, because `W` reads the target's kernels and the component freshness predicates are false on it (section 6). CE-11 first proves a second compile lemma in the ideal world: `idealKeysBranch(compile A)` equals the compile-image of an explicit un-compiled game `CE.idealGame g`, in which the CE adversary runs against native handlers and the target session's step functions are fed the uniform `next32`/`right32`. Items 5 and 4 then run on `CE.idealGame g`, where the subject is the CE adversary, which reads no kernel. The evolving hops are, per record position of session `g`, `stepExtract_hop` and `stepExpand_hop` on uniform chains, plus the skipped-key slots (at most 51 per receive). The CTX hops are `AdaptiveCtxDynamicKnownKeys` with the selected key equal to each target-session record key (summed) and every other key known. Their losses are `ε_evo(g)` and `ε_ctx(g)`.
- **9.7 (final terms).** A key transfer is the chain itself, with `Pr_ideal(g)[D_g]` kept on the right; it has no winning condition and no final term. For origin claims the final term is 0 (forgeries are inside `ε_ctx`). For fresh-message guessing it is `2^{-ℓmin}`. For left-or-right secrecy the final world has advantage 0, once the two-sided step CE-9b is available.

Composite for a one-sided event claim (origin, fresh-message secrecy), in the headline form:

```text
Pr_CE[E ∧ elig] = Σ_g Pr_CE[E ∧ designate = some g]
               ≤ Σ_g ( Pr_final(g)[D_g] + Adv^{IND-CCA}(B_g) + δ_corr + ε_item2(g) + ε_evo(g) + ε_ctx(g) )
```

The `N·(…)` form is available only under owner input 5 (signed hop variants).

Two-sided chain for left-or-right secrecy. The KEM hop is already two-sided (`KemRawCertified.ideal_close`), T6 is an equality and item 2's T7 is two-sided by design. Only T4 is one-sided. Stage CE-9b proves an equality or two-sided form of T4 for decisions that imply `accepted ∧ KeyMatchFinal ∧ GoodKem`: every execution that the proof of `actual_le_real` discards is excluded by such decisions. This is new statement work, not a new assumption (owner input 7).

Corollaries to the symbolic eligibility notions (H7). The CE claims are stated with CE eligibility. The symbolic targets use broader notions, recovered as follows, each by one global term with no selection factor:
- **Server side.** Symbolic: the accepted identity is an honest Beacon's (S3-server, SSX-s2b, App-s2b). CE: that identity AND the PQ key of the same owner. The symbolic set contains the CE set, and the difference consists of runs in which an accept under an honest identity carries a PQ key other than that owner's published key, which is a CE-A2 (publication) violation. Hence `|Adv_sym − Adv_CE| ≤ ε_A2` for left-or-right advantages (the sets are nested), and `Pr_sym ≤ Pr_CE + ε_A2` for events, on `NoBundleFailure` runs or unconditionally with `phase1Total` (owner input 15).
- **Beacon side.** Symbolic: an established Beacon pinning the honest Server key (S3-beacon, SSX-b2s, App-b2s). CE: additionally ciphertext-linked to a session with its own PQ key. The difference consists of established Beacons pinned to `S` with no eleven-field partner session that published the response, which is a CE-A1 violation (the eleven fields carry the ciphertext and the PQ key; the link then follows with `Phase2ReadBack`). Hence an added `ε_A1`, with A1's `NoBundleFailure_c` caveat.

Bills:
- the KEM reductions: `KemRawBills.adversary_bound` (exactly the caps of `KemReductionBills.adversary_bound`) at the transported caps of `W`;
- item 2: T8b with `KemBound setup caps` and `initBound`;
- `compile` overhead: the table in section 8;
- the optional guessing reductions add one `uniformFin` draw.

## 10. Per-claim reductions inside CE

| CE claim | Event | Reduction and loss | Stage |
| --- | --- | --- | --- |
| CE-A2 provenance (signing history) | Some successful accept carries a candidate that verifies under the identity key of a generated owner, unrevealed at that accept, whose decoded tuple is not in that owner's chronological signing history before the accept | The event is a property of `compile A`'s report run, with no output from `compile A`: `raw_origin` turns it into an unissued field at that accept; the raw-accept report at that accept then sets the monitor flag (new mid-run detection lemma, the analogue of `NativeOriginEvent.public_failure` and `FinalReportEvent.announce_hits` for the reports `PqxdhRegistrationJointRawReports.report` already makes); `fieldOrigin_advantage_le_sum` gives `ε_A2 := Σ_{t<count+1} Adv^{jointEUF}(red_t)`, coefficient one. No selection factor, no publicity requirement and no collision term (the address-free failure tolerates equal keys). Needs `kernel_reads_unrevealed` (risk 2). Fallback: per raw-accept ordinal `j < qAccept` through `selected_report_bound`, `Σ_j Σ_t` (within the owner's `qAccept·(count+1)` allowance, charged explicitly). | CE-7 |
| CE-A2pub (publication) | Some successful accept carries a tuple under generated owner `c`'s identity that is not `c`'s published tuple, on a run with `NoBundleFailure` | `ε_A2`: under `NoBundleFailure`, every signing attempt of an owner was published, so its signing history is its published tuple or empty (CE-7 lemma). Unconditional if the owner extends `phase1Total` and a CE-7 lemma shows that attempts failing before or during signing leave no complete unpublished tuple; otherwise the conjunct stays. | CE-7 |
| CE-R1 | One live Server object accepts one registration ID twice | Deterministic, zero loss. New proof over `CE.handler`: source14's `program_consumed` (prefix, no duplicates), a new per-accept lemma on `nativeAccept` (a successful accept's identity/one-time pair was absent and is appended; ServerAuth's `no_reacceptance` is the template), and a CE-2 frame lemma (record, `test` and `fresh` commands never touch `consumed`). | CE-6 |
| CE-R1' | Two successful accepts under one generated owner's identity, on a run with `NoBundleFailure` | `ε_A2`: under `NoBundleFailure` both accepts carry the owner's single published tuple, hence the same identity/one-time pair, which CE-R1 excludes. This is CE's reading of L5's "at most one bundle" (`doc/proverif-fs-event-meaning.md:114`). Unconditional only as for CE-A2pub. | CE-6 |
| CE-A1 initial response origin | A Beacon `c` pinned to `(S, serverKid)` accepts with no eleven-field common session that published the decoded record earlier, on a run with `NoBundleFailure_c` | `ε_A1 := Σ_{c<count+1} [GapDH(R_c) + (qAccept choose 2)·64/2^256 + Σ_{j<qAccept+1}(record + schedule) + jointEUF(R_c)] + ε_inj` at transported budgets, with the premises of `generated_authentication`. `R_c` is below. Injectivity (no two Beacons matched to one session): two such Beacons have equal identity public keys, so `ε_inj := Σ_{t<count+1} Adv^{jointEUF}(B^coll_t)`, where `B^coll_t` receives the challenge key at index `t`, generates the other `count` seeds itself and, on a collision, signs a fresh message with the colliding seed (no signing query, no new assumption). Without `NoBundleFailure_c`, A1 needs `phase1Total` or a retry-capable ServerAuth variant (owner input 15). | CE-8 |
| CE-C3 replay | An owner accepts one sequence twice | Deterministic slot consumption (HB-105 no-repeat lifted to every owner and peer over `CE.handler`); zero loss | CE-6 |
| CE-OR origin, near and far, both directions (L2, S2b, C1, C2, C2-chosen-fs, C4, far-C4) | Server side (`g` designates peer `kid_i`): a raw receive on `kid_i` accepts a frame that is not among the ciphertexts returned by `beaconSend`, `test` or `fresh` on `owner k`. Beacon side (`g` designates `c`): a raw receive on `c` accepts a frame that is not among the ciphertexts returned on `kid_i`. Any position up to 51 derivations ahead; position 1 is CE-A1's. | Section 9 chain with `D_g` = this public event, then the INT sums of `selected_integrity` over every raw attempt. The public counterpart replaces the ghost partner: under T and S7 the only possible partner of session `i` is `owner k` (the sole holder of KEM key `k`), and a non-partnered counterpart uses an independent ideal key, so accepting its frame is itself an INT event of the designated key. A publication-versus-production term covers frames equal to produced but unpublished seals (`CE.Logs.produced`; owner input 9). | CE-12, after items 4 and 5 |
| CE-UKS (UKSr) | A frame returned by a send on handle `h2` is accepted by a receive on handle `h1` that is not `h2`'s designated counterpart | As CE-OR, with the associated data and claimed-sender binding inside the CTX event | CE-12 |
| CE-KT key transfer (S3-server, S3-beacon, A1-root) | Any decision `D` computed by `compile A` | Section 9 steps 9.1-9.5 per `g` (one-sided); two-sided with CE-9b. A transfer between worlds, not a secrecy claim. | CE-9 / CE-10 |
| CE-RG root guess (optional) | The adversary outputs `(handle, r)` and `r` is the root of the designated session | `compile A` evaluates the public proxy "the installed kernel recomputed from `r` by the real key schedule equals the kernel read for `g`", which the true root satisfies. Section 9 chain, then the ideal-world probability of the proxy, which needs either items 4 and 5 (session `g`'s records independent of its chains, final term about `2^{-256}`) or an extra test hop at the uniform chain within the accepted PRF and Extract-on-uniform games | CE-RG, after items 4 and 5 (owner input 16) |
| CE-APP fresh-message secrecy (App, S1, S2) | The adversary outputs `m*` of an eligible fresh record | Section 9 chain plus `selected_privacy` (IND$) for every target-session key and INT to simulate the receive bits, then `2^{-ℓmin}`; symbolic-eligibility corollary adds `ε_A2` or `ε_A1` | CE-12, after items 4 and 5 |
| CE-LOR left-or-right secrecy (SSX, SS) | `b' = b` on the single eligible test session, mode P | Two-sided section 9 chain (CE-9b), then the ordered all-key IND$ hybrid over test records (`2·IND$` per key) and INT for the receive bits; both directions of that session in one game (stronger than the separate symbolic directions, M11); symbolic-eligibility corollary adds `ε_A2` or `ε_A1` | CE-12 |

The reduction `R_c` for CE-A1 is a ServerAuth adversary:
- **Target Beacon.** It maps the CE adversary's `c`-th `create` to ServerAuth's target Beacon if its pin and key ID are the protected binding, and aborts otherwise. Generation is moved to the start, which is a distribution equality because the draws are independent. The first CE `bundle c` returns `AuthInput.phase1`. If that is `none`, `NoBundleFailure_c` is false and `R_c` stops, because ServerAuth has no second target bundle. `finish c` maps to ServerAuth `.finish`.
- **Other Beacons.** They are generated and run locally. Their roots are computed through ServerAuth `.hmac` (counted in `qH`), their records locally.
- **Server.** Accept and build map to ServerAuth `.accept` and `.build`. Server records are simulated through one ServerAuth `.reveal` per peer, as in restriction 5.
- **Stop.** It stops at the target's acceptance, which `win_frozen` makes sufficient.

`generated_authentication` covers only the singleton through `PqxdhRegistrationR1Restriction.route`, so this multi-owner embedding is new work.

## 11. ProVerif ideal operations and their CE endpoints

"Planned" marks an endpoint that depends on items 4 or 5 and is not yet a precise computational endpoint. "Symbolic-only capability" marks a capability the symbolic adversary has and the CE adversary lacks.

| # | Symbolic operation (site) | CE endpoint | Selection | Query class / bill | Loss | Status |
| --- | --- | --- | --- | --- | --- | --- |
| O1 | Fresh Beacon names (`PV/record-origin.pvl:153`, `PV/registration-provenance.pvl:51-58`) | `create` | Creation index `< count+1` | `create`; `qInit+64+keygenCost` | No A2 collision term; A1 injectivity via `ε_inj` (joint EUF, zero-query reduction) | Present; `ε_inj` in CE-8 |
| O2 | `sign`/`verify_signature` (`PV/crypto.pvl:20-23`) | `bundle`; attached verification inside `accept` | none (reports cover every accept) | `3·qBundle` signing; `qFinish+qAccept` converted DH per reduction | Joint-use weak-EUF, `Σ_{count+1}` | Present (raw reports, `raw_origin`) |
| O3 | Ed→X conversion, `x25519_shared`, role DH (`PV/crypto.pvl:27-36`) | Inside `accept`/`finish`; no adversary DH oracle | none | `qH` (Gap-DH decisions) | Gap-DH, class/spread laws, `(Q choose 2)·64/2^256` | Present for one object (ServerAuth) |
| O4 | ML-KEM (`PV/crypto.pvl:46-53`) | Inside `accept`/`finish`; routing by creation index (`postDecapsulation`) | `k` in `g` | `KemRawBills` | IND-CCA + correctness error; T0 cross-key injectivity is not imported | Present (T4/T6) |
| O5 | `pqxdh_root` (`PV/crypto.pvl:67-68`) | R1 slice table (`hmac`, honest roots) | entry 0 (and the second entry with S7) | `qHmac`, `qAccept`, `qFinish`, `qRoot` | `(qHmac+qAccept+qFinish)/2^256 + Σ PRF` | Planned (item 2 S1-S2) |
| O6 | Initial chains (`PV/crypto.pvl:72-80`) | Inside build and finish | none | Item 2 G2 | 2·Ext(`uniform32`) + 2·PRF | Planned (item 2 S3-S4) |
| O7 | `ratchet_next`, `ratchet_material` (`PV/crypto.pvl:61-65,82-96`) | Inside sends and receives, on `CE.idealGame g` | Record position (sum) | `S+51R` local derivations | Ext + PRF per step | Planned (item 5) |
| O8 | `seal_frame`, AEAD/CTX, BLAKE2b (`PV/crypto.pvl:98-141`) | Sends; `hash` ROM | Key index (sum) | `qHash+S+R`; `qSeal < 2^96` | IND$ + `qHash/2^128` + `2ΣINT` + `qRaw/2^512` | Planned (item 4; component exists) |
| O9 | `open_frame` (`PV/crypto.pvl:143-185`) | `serverRaw`/`beaconRaw` (mode O plaintext, mode P bit) | Key index (sum) | `R`; `51R` derivations | As O8 | Planned (item 4) |
| O10 | Fresh application name (`PV/record-origin-sends.pvl:7,16`) | `fresh` | `g` | `qFresh`, `qFreshBytes` | IND$ + `2^{-ℓmin}` | CE-12 |
| O11 | `choice[l,r]` (`PV/exact-interface-strong-b2s-sends.pvl:7,16`) | `test` (send of `m_b`) | `g`; records summed | `qTest` | `2·IND$` per key + INT | CE-9b + CE-12 |
| O12 | Replicated accept (`PV/record-origin.pvl:31`) | `accept` (the consumed-set check is kept; the projection omits it, M7) | `i < qAccept` | `accept`; `96+encapsCost` | none of its own | Present |
| O13 | One-use pending token and delayed build (`PV/record-origin.pvl:16-28`) | `build session payload` (same object; moved token) | Fixed by the token | `build`; 64 | none | Present; cross-object only in CE-M |
| O14 | `fail_build`, `fail_seal` flags | Actual failure branches (occupancy, writer `none`, empty plaintext, exhaustion) | none | counted | none; failures are deterministic in public inputs, so tests require equal nonempty lengths | Present |
| O15 | Fixed chain disclosures: `PV/delayed-response.pvl:33-34`; `PV/record-origin.pvl:34-36` (`ratchet_next(server_to_beacon_chain(root))` and `ratchet_next(ratchet_next(beacon_to_server_chain(root)))` for every accepted session, the selected one included); `PV/exact-interface-strong-b2s*.pvl:34-36` (same pattern) | None for the CE adversary; inside `compile`/`R_c` as kernel reads (proof device) | none | `.inl 8` and `.inr kernel` inside proofs only | none | Symbolic-only capability |
| O16 | Root release for non-selected identities (`PV/record-origin.pvl:35`) | No oracle; simulated in reductions (R1 table + Gap-DH decisions) | none | `qH` | Gap-DH | Symbolic-only capability |
| O17 | AnyPin creation (`PV/fs-records-b2s.pvl:397-399`) | `create` with any pin | none | none | none | Present |
| O18 | `fs_far_chain` | Not imported; the general receive with at most 51 derivations | none | `51R` | as O7/O9 | Planned (items 4 and 5) |
| O19 | OD5 `fs_strong_partner` | Public counterpart from `designate` (`owner k` on the Server side, session `i` on the Beacon side); the ghost `Partner` (root-input equality) is used only inside `R_c` | none | none | none | CE-12 |
| O20 | Material service create/alias/import/seal/open/reveal (`PV/live-private-application-service.pvl:50-98`) | Selected key vs `KnownCall` inside the item 4 hop | Key (sum) | as O8 | as O8 | Planned (item 4) |
| O21 | SSX full-response lookup | Lookup by session handle (`links`) and eleven-field agreement; raw response equality is not used | none | none | none | CE-12 |
| O22 | Dolev-Yao deduction | Local real computation; only the R1 slice and BLAKE2b go through oracles | none | `qHmac`, `qHash` | ROM caveat | Present |
| O23 | `ProvDhService` (`PV/registration-provenance.pvl:14-28`): a DH service on honest identity seeds | Inside the joint-use game only, for reductions; the CE adversary has no DH oracle | none | `qFinish+qAccept` | EUF | Symbolic-only capability |
| O24 | Events (L6) | Public transcript and `CE.Logs` (section 12.4) | none | none | none | CE-1 |
| O25 | Quantum capabilities (`PV/quantum-capabilities.pvl`: classical secret recovery from Ed25519 and X25519 public keys) | None. CE is classical (classical programmable ROMs, Gap-DH, joint Ed25519 EUF; `doc/composition-assumptions.md:59`) | none | none | none | Symbolic-only, no computational endpoint |
| O26 | Identity key output at allocation (`PV/registration-provenance.pvl:51-56`) | Only through the bundle (deviation D2) | none | none | none | Symbolic-only capability |
| O27 | Two published triples per owner (`two_triples`, `PV/registration-provenance.pvl:57-58`) | One published bundle per Beacon, as in Rust; failed attempts sign without publishing (section 5) | none | none | none | Symbolic-only capability |

## 12. Security-class ProVerif targets and their CE endpoints

"Computational" names the CE claim that covers the same property at parametric budgets. "Symbolic-only" is what remains supported only by the bounded symbolic result. No row is a computational-soundness transfer: the CE claim and the ProVerif target are related by the event and capability map of sections 11 and 12.4, and neither is a premise of the other (owner input 18). "Partial" means the CE claim covers a weaker or different property.

### 12.1 Source-scope ledger targets (18 lines)

| Target (VC) | CE endpoint | Computational side | Selection / queries / loss | Symbolic-only |
| --- | --- | --- | --- | --- |
| A2-provenance (3161) | CE-A2 (signing history); CE-A2pub (publication) | Raw reports + `raw_origin` + `fieldOrigin_advantage_le_sum` on `compile A` (CE-7) | No selection factor; `3·qBundle`, `qFinish+qAccept`, `(count+1)(qAccept+1)` reports; `ε_A2`. Publication reading on `NoBundleFailure` runs or with `phase1Total`. | The T0 occurrence/target-key reflection argument. Capabilities beyond CE: identity key output at allocation (O26), `ProvDhService` (O23), two triples per owner (O27). |
| A2-beacon-key (3162), A2-server-key (3163) | none (auxiliary) | Implicit: the reductions never need these seeds | none | Identity secrecy in the stronger process; not advertised |
| A1-delayed (3167) | CE-A1 | ServerAuth via `R_c`, `Σ_c` (CE-8) | `ε_A1`, on `NoBundleFailure_c` runs unless owner input 15 | Builds on a different same-binding object (until CE-M); injectivity from distinct fresh names |
| A1-root (3168) | Partial: CE-KT; optional CE-RG | Section 9 (CE-9/10) | `Σ_g`; T4 + IND-CCA + corr + `ε_item2` | Root secrecy as `attacker(root)`. A key transfer has no root-recovery winning condition, so this stays symbolic-only unless CE-RG is built. |
| L2-origin (3179) | CE-OR b2s | Items 4/5 + CE-12 | `Σ_g`; records summed; `qBR`, `qHash`, `51·qBR` | Near positions 1/2, Ks2/Kr3, first-far cutoff; paper injectivity via T0 equal-root (CE uses cache consumption and ServerAuth W3) |
| L2-identity (3180) | none (auxiliary) | — | — | Auxiliary |
| S2b-origin (3183) | CE-OR s2b | Items 4/5 + CE-12 | as L2 | Near positions 2/3 |
| S2b-initial (3184) | CE-A1 | CE-8 | as A1-delayed | Same-process paper argument |
| S2b-identity (3185) | none (auxiliary) | — | — | Auxiliary |
| App-b2s (3188), App-s2b (3189) | CE-APP (mode P) | Items 4/5 + CE-12 | `Σ_g(… + 2^{-ℓmin})`; on symbolic eligibility add `ε_A1` (b2s) or `ε_A2` (s2b) | Fresh-name secrecy without a finite-byte bound; the no-echo application, which CE builds in by mode P |
| SSX-b2s (3192), SSX-s2b (3193) | CE-LOR (mode P, single test session) | CE-9b + items 4/5 + CE-12 | `Σ_g`; `2·IND$` per key + INT; on symbolic eligibility add `ε_A1` (b2s) or `ε_A2` (s2b) | Kr3/Ks2 windows; separate directions; paired-context paper proof |
| SSX-b2s-origin (3194), SSX-s2b-origin (3195) | No endpoint as stated | Replaced by eleven-field agreement and handle lookup (O21) | — | Exact full-response equality, which is false under X25519 encoding aliases (`doc/composition-assumptions.md:23-27`) |
| far-b2s-C4 (3174), far-s2b-C4 (3175) | CE-OR at far positions | Items 4/5 + CE-12 | as CE-OR, with every future position idealized | Legacy-process transfer: L1, L2, E19, L3 global induction, L4 and L5 accounting |

### 12.2 Legacy fs targets and close relatives (26 lines)

| Target (VC) | CE endpoint | Computational side | Symbolic-only |
| --- | --- | --- | --- |
| A1 (597), s2b-A1 (613), b2s-A1 (631), encoding-A1 (649) | CE-A1 | CE-8 | Adjacent build on one object (E4); `fs_kid(1)` merge (L2); K_reg bounds |
| A2 (598), s2b-A2 (614), b2s-A2 (632), encoding-A2 (650) | CE-A2 / CE-A2pub | CE-7 | As above; publication reading conditional as in 12.1 |
| R1 (599), encoding-R1 (651) | CE-R1 | CE-6, zero loss | R4 is an expected limitation (same-seed objects) |
| R1' (600), encoding-R1' (652) | CE-R1' | CE-6, on `NoBundleFailure` runs unless owner input 15 | L5 lifecycle collapse: the symbolic model has one signing per Beacon; CE has one publication, with failed signing attempts handled by the `NoBundleFailure` condition |
| S3-server (601), S3-beacon (602) | Partial: CE-KT; optional CE-RG | CE-9/10 | `attacker(root)` form stays symbolic-only unless CE-RG is built; on symbolic eligibility add `ε_A2` (server) or `ε_A1` (beacon) |
| s2b-C1 (615) | CE-OR s2b | CE-12 | Allocation-based `FsSent` (CE uses publication, which is stronger) |
| b2s-C2 (633), b2s-C2-chosen-fs (634) | CE-OR b2s | CE-12 | Fail-stop E21; E3 pin-independence |
| s2b-C3 (616), b2s-C3 (635) | CE-C3 | CE-6, zero loss | none of substance |
| s2b-C4 (617), b2s-C4 (636) | CE-OR far | CE-12 | `fs_far_chain` (L3/OD4) |
| s2b-S1 (618), b2s-S2 (637) | CE-APP | CE-12 | Fresh-name secrecy |
| b2s-UKSr (638) | CE-UKS | CE-12 | `fs-control-uks` profile |
| SS-b2s (3155), SS-s2b (3156) | CE-LOR | CE-9b + CE-12 | K_r = 1; OD5 private partner channel (a public counterpart in CE, O19) |

### 12.3 Remaining security-class lines (141 lines, grouped)

| Group (VC) | Lines | CE endpoint | Remark |
| --- | --- | --- | --- |
| `check-results.awk` fixed schedules: active-classical (2-15), baseline (34-47), failed-receive (53-58, 69), passive-classical and its equivalence (162-167) | 41 | Covered by the claims above where they coincide (A1, A2, C1-C4, secrecy) | Their scope says "exact symbolic query only; no unbounded common-experiment lift". They stay regression evidence. |
| `check-results.awk` passive-quantum and its equivalence (168-173) | 6 | None | Symbolic-only. CE is classical; none of its experiments proves quantum-random-oracle or post-quantum security (`doc/composition-assumptions.md:59`). |
| `check-results.awk` compromise (48, 52), failed-receive-compromise (70, 73-75) | 6 | None under Π = ∅ | Chain/skipped-key reveal schedules lie outside the approved profile (P7 not approved). Symbolic-only. |
| `check-results.awk` live material and private-application services (127, 130, 132, 134, 135) | 5 | Planned: item 4 component (selected key vs `KnownCall`) inside CE-OR and CE-APP | Ideal single-key service shapes |
| `check-general-registration.py` generated initial targets (707-3128) | 61 | Sequence-one admission (HB-95) inside CE's finish; no separate claim | Conditional correspondence or rejection per initial target 0-52; symbolic regression; they do not prove admission at 2..51 |
| `check-phase2-x25519-alias.py` canonical / projected (689-692, 697-704) | 12 | CE-A1 uses eleven-field agreement, never raw-byte origin | One-session exact byte-level origin; not alias invariant |
| `check-kem-controller-auth.py` (658-666) | 9 | Supports CE-A1 and CE-A2: no KEM algebra is needed | CE routes by creation index and never uses KEM injectivity |
| `check-registration-set.py` (271) | 1 | CE-A2 | Local replicated admission |

### 12.4 Event projection (L6) to CE observables

| Symbolic event | CE observable |
| --- | --- |
| `FsBeaconStarted` | `bundle` reply `some` (transcript) |
| `ProvPublished`, `ProvAccepted` | Bundle bytes; `RawSignatures.verified` of `accept` bytes. Signing attempts without publication exist only in the analysis (report history), not as an observable. |
| `FsServerAccepted` | `accept` reply `some i`; the consumed set is in source14's state |
| `FsServerCommitted` | `build` reply `some`; `links`. The sequence-one seal is in the native registration ghost and is used only by `R_c`. |
| `FsBeaconEstablished` | `finish` reply `some`; `phase c = Established` |
| `FsSent` | `CE.Logs.produced` (allocation, which advances even on a failed seal) |
| `L2Published`, `S2bPublished` | `CE.Logs.published` (returned ciphertexts only) |
| `FsReceived`, `FsReceivedFrame` | `CE.Logs.received` with frame and optional plaintext |
| `FsReceiveRejected` | `CE.Logs.received` entry with `none` |
| `L2SelectedIdentity`, `S2bSelectedIdentity` | `designate = some g` |
| `…FreshPublished` | `fresh` entries |
| `A1Root`, OD5 partner | Not CE observables. `A1Root` has no CE endpoint (CE-RG optional); the partner is the public counterpart of `designate` (O19), and ServerAuth's `Partner` appears only inside `R_c`. |
| Failure-cause witnesses (`FsServerReplayRejected`, …) | None (witnesses only, E2) |

## 13. What stays open: items 4, 5, 6 and 7

CE supplies the interface, the designation `g`, the selection lemma, the compiled ideal-keys world `idealKeysBranch(compile A)`, the un-compiled ideal world `CE.idealGame g` (CE-11) and the bridging lemmas. The following remain.

- **Item 4 (CTX lift).**
  - What CE provides: the global adaptive raw receive of `CE.idealGame g`, with `rawAttempts` counting every attempt and the mode-dependent reply.
  - Still open: a compiler that, for each target-session key index, routes that key to the `AdaptiveCtxDynamicKnownKeys` challenger and computes every other key itself. It must preserve parser rejection, cached and future paths (at most 51), consumption, rollback and replay, and return the challenger's optional plaintext (mode O) or bit (mode P). It must also charge session selection (`Σ_g`, inherited) and record selection (exact sums). The existing family-C compilers (`RawCtxSelectedReceiveCompiler`, `RawCtxSelectedFamilyLiveCompiler`, `RawCtxSharedReceiveOwner`) are stated over supplied role states with real ratchet HKDF. The dynamic peer map and dynamic owner list need a dynamic-family version of `RawCtxProtocolRoles` (fixed `Fin S`, `Fin B` today).
- **Item 5 (evolving chain).**
  - Still open: the ordered per-step hybrids from the uniform `next32`/`right32` of `g` on `CE.idealGame g`, in both directions, including skipped-key slots and replayed or rolled-back receives; the alias and freshness assembly; and the refusal probability. Under Π = ∅ lineage freshness reduces to public aliases, that is, adversary HKDF evaluations at a hidden chain, which give guessing terms.
  - Family-B pieces: MarkedTransfer15's nonce-refusal comparison is on `codex/evolving-record-composition` (`94bc9538`), not on central, and the later-record alias exclusion is assumed there and still uncharged. Any HB-111/112 consumer must be re-instantiated with a ROM-world `prior` (item 2 plan I-5); the correlated-family `prior` must not be imported.
- **Item 6 (symbolic coverage).**
  - The ProVerif results remain bounded (Kr3/Ks2, near positions, one selected Beacon, legacy K_reg). CE's claims are parametric. The deliverable states each symbolic result on its own window next to the CE claim; nothing is transferred beyond the window. The quantum lines and the capabilities O15, O16, O23, O25-O27 stay symbolic-only.
  - Extending ProVerif towards CE (multi-object A1, both directions in one process, CE-like command sets) needs a new serial budget, because OD7 is about 96.5% used (`doc/impl/handover/pause-2026-10-05/README.md:181,215,308`), and must keep the existing queries, controls and mutation matrices.
  - The legacy obligations L1 case (iv), L2, the L3 global induction, L4 and E19 stay open for the legacy and exact-far results. CE discharges their computational counterparts only for its own claims; L5's computational accounting is discharged only on `NoBundleFailure` runs unless owner input 15 is approved.
- **Item 7 (production boundary).**
  - CE's native handlers run extracted functions for acceptance, root input, ratchet send and receive and the opening phases. They run hand-written Lean for the codec (abstract), the adapter wrappers (`get_shared_secret`/`build` ordering, `executeOpen` transcribing `execute_open`, B12) and publication.
  - The bridges `PqxdhHeadlineBridges`, `PqxdhOpenBridges` and `PqxdhReceiveHeadlineBridges` exist only for family B. A CE bridge inventory is needed covering acceptance, root, record, rollback/replay (`ReceiveTransition`), publication (writer after seal), associated data and the deviations D1-D4. It is listed as stage CE-14, but its proofs are item 7 work.
  - Compiler, storage, physical erasure, codec internals and native primitives remain external contracts.
- **Item 8.** The final validation matrix runs only after the merged result.

## 14. Stages, modules and effort

Effort is in agent-days for one agent using single-module checks under the shared Lean lock. It is calibrated, as in the item 2 plan, against the Server-authentication entry work (16 modules, about 6,400 lines). The previous join underran its estimate by 40-60%; the ranges below already widen the stages the critique identified, and they must be re-estimated after the CE-3 spike. All module names were checked as unused at `bccd853e`.

| Stage | Module(s) | Content | Effort | Depends on |
| --- | --- | --- | --- | --- |
| CE-1 | `PqxdhDeploymentInterface` | `CESpec` (no reveal command), replies, modes, `CE.Output`/`CE.Claim`, query classes and budgets (`qFreshBytes`), `PublicEntry`, `CE.Logs`, `phase`, `owner`, `NoBundleFailure`, `designate` | 3-5 | — |
| CE-2 | `PqxdhDeploymentNative` | Native handler (source14 registration with the D1 `create`, `serverImpl`/`beaconImpl` records with `codec.frameRead`/`frameWrite`, `test`/`fresh` wrappers, mode projection); frame lemmas (registration never reads kernels; records never touch the R1 slice, pools, tokens or `consumed`); router choice of section 8 (f) | 7-11 | CE-1 |
| CE-3 | `PqxdhDeploymentCompile`, `PqxdhDeploymentCompileBudget` | `compile`; CE-COMPILE with items (a)-(g) of section 8: local pin parse, Server-peer and Beacon-owner reconstruction from public data (with `Phase1ReadBack`), the identity-seed and metadata frame lemmas, the sampling swap, the split projection; budget transport | 18-30 | CE-2; owner input 14 |
| CE-4 | `UniformTargetSelection` (generic) | Split, event and advantage forms (section 7); optional signed-hop combinator | 2-4 (+1-2) | — |
| CE-5 | `PqxdhDeploymentEligibility` | Publicity of `phase`, `owner`, `NoBundleFailure` and `designate`; `designate_keymatch` and the Beacon ciphertext link (with the readback laws); `approved_goodkem`; `kernel_reads_unrevealed` | 5-8 | CE-3 |
| CE-6 | `PqxdhDeploymentReplay` | CE-R1 per live object (new proof over `CE.handler` from source14's `program_consumed` and a new per-accept `nativeAccept` lemma), CE-C3 for every owner and peer, CE-R1' (with CE-7) | 5-8 | CE-2, CE-7 |
| CE-7 | `PqxdhDeploymentProvenance` | CE-A2 over all accepts (mid-run report detection lemma with `raw_origin` and `fieldOrigin_advantage_le_sum`); the `NoBundleFailure` signing-history lemma for CE-A2pub; fallback per-ordinal route | 4-7 | CE-3, CE-5 |
| CE-8 | `PqxdhDeploymentServerAuth` | `R_c` embedding (lazy target with stop at a failed target bundle, local other Beacons, restriction-5 Server records, truncation by `win_frozen`); `Σ_c`; `ε_inj` by the zero-query joint-EUF reduction; ServerAuth premises and bills | 14-22 | CE-2 |
| CE-9 | `PqxdhDeploymentKemTransfer` | Section 9 steps 9.1-9.4 per `g`, with bills | 3-5 | CE-3, CE-5 |
| CE-9b | `PqxdhDeploymentKemTwoSided` | Two-sided or equality form of T4 for KeyMatch-implying decisions; the rest of the chain is already two-sided | 3-6 | CE-9; owner input 7 |
| CE-10 | (item 2 modules) | Item 2 S0a-S9 as planned, with `Ext` empty, plus T and S7; instantiation 9.5 for `W` | Item 2's 50-86 (+4-9) | Item 2 gate; CE-3 |
| CE-11 | `PqxdhDeploymentIdealKeys` | The un-compiled ideal world `CE.idealGame g` and the second compile lemma `idealKeysBranch(compile A) = compile-image of CE.idealGame g`; key-first and key-last forms (item 2 S6); the dynamic-family hand-off interface for items 4 and 5 | 8-14 | CE-10 |
| CE-12 | `PqxdhDeploymentHeadlines` | Headline theorems CE-KT, CE-OR, CE-UKS, CE-APP and CE-LOR over public events, with full bills; symbolic-eligibility corollaries with `ε_A2` and `ε_A1`; signed forms if owner input 5 asks for them | 8-14 | CE-11, items 4/5, (CE-9b) |
| CE-13 | — | Guide `doc/impl/deployment-experiment.md` (interface, deviations D1-D4, compile argument, selection, symbolic map of sections 11-12); plain-English section in `doc/formal-verification-analysis.md`; updates to `doc/composition-assumptions.md` (reveal capability text at `:33` after owner input 2, scope lists) and `doc/proverif-source-scope.md` (computational column); inventory rows, guards, guard liveness, scans, receipts; independent semantic review per stage | 7-11 | each stage |
| CE-14 | — | Production-boundary bridge inventory for CE handlers and deviations (item 7 input) | 2-3 | CE-2 |
| CE-RG (optional) | `PqxdhDeploymentRootGuess` | Root-guess endpoint with the recomputation proxy | 4-8 | CE-9, items 4/5 or an extra test hop; owner input 16 |
| CE-8r (optional) | ServerAuth variant | Retry-capable ServerAuth target (target signing of further bundles), re-proving the affected ServerAuth stages, for an unconditional A1 without `phase1Total` | 10-20 | CE-8; owner input 15 |
| CE-M (optional) | `PqxdhDeploymentObjects` and a re-proof of the source14 line | Several same-seed Server objects, `newServer`, cross-object builds, per-object consumed sets and counters | 30-50 | Owner input 1 |

Totals:
- Item 3 proper (CE-1 to CE-9, CE-11, CE-13, CE-14): about 78-128 agent-days (revision 1: 61-102).
- Plus CE-9b: 3-6 (revision 1: 8-14).
- Plus CE-12: 8-14.
- Optional: CE-RG 4-8, CE-8r 10-20, CE-M 30-50.

Item 2 and items 4 and 5 are separate.

Reviewable publication units:
1. CE-1, CE-2 and CE-4: definitions and generic lemma, no cryptography.
2. CE-3 and CE-5: the compile lemma, the critical path.
3. CE-6 and CE-7: deterministic claims and A2.
4. CE-8: A1 over all Beacons.
5. CE-9 (and CE-9b): the KEM transfer per target.
6. CE-10 and CE-11: the item 2 join and the un-compiled ideal world, published only after item 2's own reviews.
7. CE-12 (and CE-RG): after items 4 and 5.

Each unit gets its guide section, analysis paragraph and independent semantic review before integration (KEM join decision 5).

Critical path: CE-1, CE-2, CE-3, CE-5, CE-9, then item 2 (CE-10), CE-11, items 4 and 5, then CE-12. CE-4, CE-6, CE-7 and CE-8 run in parallel once CE-2 or CE-3 exists. Recommended order: CE-1, CE-2 and CE-4 first; then a 4-6 day spike of CE-3 that covers a Server peer's records, an established Beacon's records (including the reconstruction of item (c)) and `create`, before committing to the compile approach (risk 1).

## 15. Risks and fallbacks

1. **CE-3 (compile) is the linchpin.**
   - Hard parts: the stale-kernel simulation relation across all fourteen source14 kinds; the reconstruction of Server peers and Beacon owners from public data; the identity-seed and metadata frame lemmas; the report machinery's treatment of `.reveal` and `.kernel` reads; dynamic lazy reads; and elaboration memory under `-M8000`.
   - Mitigations: per-handler equalities with `map_run_simulateQ_eq_of_query_map_eq`; never unfold the whole program; and the widened spike.
   - Fallbacks: section 8 (a) or (b).
2. **Kernel reads and the report history.** `revealedAt` and `FieldOriginFailure` read identity-pool reveal observations only, and `GoodKem` reads the KEM transcript. It is still unproved that a `.kernel` read and a Server `.reveal` leave both untouched in the report-instrumented run. CE-A2 depends on it (`kernel_reads_unrevealed`). If it fails as a definitional fact, a projection lemma is needed.
3. **Publicity of eligibility and codec laws.**
   - Every predicate in `designate` must be a function of the transcript. The Server-side key match and the Beacon-side link imply `KeyMatchFinal` and the challenge-ciphertext routing only with `Phase1ReadBack` and `Phase2ReadBack`.
   - Beacon-side eligibility relies on item 2's T and S7. If the owner declines S7, Beacon-side tests need the alias-tolerant partner check through `X25519ClassLaw` (owner input 6), or they are restricted to Server-side tests only.
4. **One-sided T4.** Left-or-right secrecy waits for CE-9b, now limited to T4. Event-based claims do not.
5. **The A1 embedding (CE-8).**
   - It reorders target generation and simulates other Beacons through ServerAuth `.hmac`, which increases `qH` by one per other-Beacon finish.
   - ServerAuth's one-object restriction stays.
   - ServerAuth has one target bundle, so A1 carries `NoBundleFailure_c` unless `phase1Total` is extended or CE-8r is built.
6. **Single object.** ProVerif A1-delayed's cross-object builds and L1 case (iv) remain symbolic-only until CE-M. CE claims must say "per live Server object".
7. **Budget transport.** The per-operation hash counts must match the `S+R+H` ledger. Local HKDF and AEAD are runtime, not free, and must appear in the reductions' bills. Fresh-message coins need the numeric cap `qFreshBytes`.
8. **Family-B contamination.** No CE statement may cite `PqxdhCorrelatedExtractFamily.*`, `jointKdfView`, `fixedHkdfSha512JointStream`, `productionHiddenRoot`, `RawCtxSourceHkdf.rootResponse` or the other fixed-HKDF root consumers listed in item 2 plan §1. Apply the same exact-token and direct-reference scans (item 2 plan risk 9).
9. **Overclaim.**
   - The symbolic map is not a soundness theorem.
   - The SSX origin auxiliaries and the identity auxiliaries are not endpoints.
   - The later assigned-ID equality, which is false for production, must never appear.
   - CE-KT is a key-transfer statement and does not cover `attacker(root)`; CE-LOR is the only left-or-right secrecy claim, for one test session.
   - CE eligibility is narrower than the symbolic one; every comparison with a symbolic secrecy target goes through the corollaries of section 9.
   - The passive-quantum lines have no CE endpoint.
   - The published-tuple readings (A2pub, R1', A1) hold on `NoBundleFailure` runs only, unless owner input 15 is approved.
10. **Name collisions.** Avoid the family-B `PqxdhCommon*` prefix and short names such as `Spec`, `impl`, `resume`, `Decision` and `Choice`; use `CE.Output`, `CE.Claim` and qualified names.
11. **Compute.** Single-module checks only, no full `lake build` before the final matrix, Nix only through the minimal flake, and never `nix-collect-garbage` during proof work.
12. **Codec laws not approved.** If `Phase1ReadBack` is not approved for CE, CE-COMPILE fails for Beacon records (fallback (a) or (b) of section 8) and the public designation no longer implies `KeyMatchFinal`. If `DecoderAgreement` is not approved, the Server router stays a free parameter and the record codec is only partly tied to source14's.
13. **Effort.** The previous join underran by 40-60%. CE-3, CE-8 and CE-11 carry most of the uncertainty.

## 16. Points needing owner input

1. **Server objects.** Version 1 has one live Server object, with claims stated per live object. Should the multi-object extension CE-M (same seed and same `serverKid`, cross-object builds, L1 case (iv)) be built, and should several key IDs for one seed be excluded? Recommendation: one object now, CE-M later if wanted. Several key IDs per seed should stay excluded (E23, one `SERVER_KEY_ID`).
2. **Reveal profile.** Confirm Π = ∅: CE has no reveal command, the only in-scope compromise is the static one of section 6, and the handoff's reveal, freshness and compromise-timing requirements are therefore met vacuously. Confirm that `doc/composition-assumptions.md:33` (reveals of identity, root, current-chain and skipped-key state) may be amended accordingly in CE-13. Confirm also that no component-profile headline (kernel, chain or field reveals) is wanted, since P7 is not approved.
3. **Internal reads as proof devices.** Confirm that `compile A` and the ServerAuth embedding `R_c` may use source14's Server kernel reveal and Beacon kernel read internally (ServerAuth restriction 5 argument). They are never answered to the CE adversary, and `compile A` reads no identity, KEM, prekey or one-time field.
4. **Observation modes.** Mode O (public optional plaintext) for authentication claims and mode P (success bits) for secrecy claims, as recommended. Should the screened mode R be added later?
5. **Selection statement form.**
   - Session selection: the headline is the exact sum `Σ_g` over `N = qAccept·(count+1)` designations. The `N·Adv(B_guess)` wording needs signed-difference variants of the T7 hops and of items 4 and 5 (+1-2 days in CE-4, and additional scope in CE-10 and CE-12). Which form should be published?
   - A2 uses no selection factor (raw reports). Confirm, and confirm the per-ordinal fallback (`Σ_{j<qAccept}`, within the allowance) if the mid-run detection lemma fails.
   - Confirm A1's `Σ_c` over `count+1` distinct reductions and the exact record-key sums with coefficient one.
6. **Eligibility and item 2 scope.** Confirm the public eligibility rules of section 7, including the new Beacon-side PQ-key conjunct. This requires item 2's optional T (`qRoot = 2`) and S7 (every hidden entry ideal), which are item 2 owner inputs 3 and 7. The alternative is to use the existing `X25519ClassLaw` contract in a public alias check. Confirm that CE secrecy claims are published with CE eligibility plus the symbolic-eligibility corollaries (`+ε_A2` on the Server side, `+ε_A1` on the Beacon side).
7. **Secrecy deliverables.** Weak secrecy only (CE-APP: guessing a fresh honest message), or also left-or-right secrecy (CE-LOR), which requires CE-9b (+3-6 days). CE-LOR has one test session; is a multi-test-session statement wanted (a further hybrid factor)?
8. **Honest message model for CE-APP.** Experiment-sampled uniform messages of adversary-chosen length `ℓmin ≤ ℓ ≤ ℓmax`, with a `2^{-ℓmin}` term and a total budget `qFreshBytes`. What should `ℓmin` and `ℓmax` (or `qFreshBytes`) be? Should honest application messages instead be drawn from an arbitrary distribution with min-entropy `h`?
9. **Publication versus production.** Origin events stated on publication (matching ProVerif's `Published`), with unpublished productions bounded inside the INT sums and no new assumption.
10. **Fidelity deviations D1-D4 (section 3.9).**
    - D1: `create` runs runtime initialization only at Server birth. Justification: in the vendored libsodium a repeated `sodium_init` after success returns 1 without effect, except on its lock-error path, which D1 treats as a process-level failure under the trusted-primitive decision. The alternative is a formal `ensureInit` idempotence law, which is a new contract.
    - D2: the public getters listed in section 3.9 are omitted, including the Beacon's pre-bundle `identity_pk`, `pq_pk` and `get_prekey_pk`, which cannot be added without a source14 extension.
    - D3: snapshot APIs and the pre-Phase-1 helpers are omitted.
    - D4: the adversary chooses the build payload.
11. **Supplied Server seed.** Confirm `supplied = none` for every CE security statement; the supplied branch keeps only exact source equations.
12. **Family-B endpoints.** Confirm that HB-111/112/114 and the first-record theorems are not CE endpoints under R1 (item 2 owner input 9), and that only their backend-generic components are reused.
13. **Primitive games and idealizations in CE headlines.** Confirm the scope extension to CE of each of the following, per headline:
    - CE-A2, CE-A2pub, CE-R1': joint Ed25519/X25519 weak-EUF (`PqxdhJointIdentity`), `shortRejects` with `setup.wiring`.
    - CE-A1: Gap-DH, the classical programmable R1 Extract-ROM, the classical programmable BLAKE2b ROM, joint weak-EUF, the record and schedule loss terms of `generated_authentication` (whatever primitive games they contain must be listed in CE-13), and its premises `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, `ReadWritable`, `Phase2ReadBack`, `FrameReadBack`.
    - CE-KT: ML-KEM IND-CCA with its correctness error and `FunctionalDecapsulation`, the R1 Extract-ROM, HMAC-PRF, Extract on `uniform32`, `SourceFullCorrect`, `prefixConsistent` inside `setup`.
    - CE-OR, CE-UKS, CE-APP, CE-LOR: the above plus the BLAKE2b ROM and the modified-nonce AEAD IND$ and INT-CTXT games of the CTX components, and whatever item 4's receive-side lift needs (for example `DecoderAgreement`).
    - CE-R1, CE-C3: none (deterministic).
14. **Codec laws.** These are abstract laws of the free `Codec`, not facts about Cap'n Proto, but they are assumptions for the CE line:
    - `Phase1ReadBack` (`C/PqxdhServerAuthNegativeControl.lean:55-60`), so far used only by the negative controls: needed by CE-3 (Beacon associated data) and by `designate`. Without it, see section 8 fallbacks.
    - `Phase2ReadBack` and `FrameReadBack`, approved for A1: extend to CE-3 and CE-5 (Beacon-side ciphertext link).
    - One codec for registration and records: record decoder `codec.frameRead`, record writer `codec.frameWrite`; the Server router either free with `DecoderAgreement`, or derived from `frameRead` (deviation that also needs `DecoderAgreement` to match production).
15. **Phase-1 writer failure after signing.** Choose one:
    - (a) Extend the existing control law `ControlLaws.phase1Total` (`C/PqxdhServerAuthNegativeControl.lean:86`) to the CE security line. CE-A2pub, CE-R1' and CE-A1 then become unconditional, subject to a CE-7 lemma about attempts that fail before or during signing.
    - (b) Default, no new assumption: publish CE-A2 on the signing history unconditionally, and CE-A2pub, CE-R1' and CE-A1 on `NoBundleFailure` runs (a public condition).
    - (c) Build CE-8r, a retry-capable ServerAuth variant (+10-20 days), for an unconditional A1 without (a).
    Recommendation: (b) now; (a) if the owner accepts the law.
16. **Root secrecy.** A1-root, S3-server and S3-beacon are `attacker(root)` targets that a key transfer does not express. Mark them partial (recommended now), or also build the optional root-guess endpoint CE-RG (+4-8 days, after items 4 and 5 or with an extra test hop).
17. **Collision terms.** Confirm that A2 has no collision term (the address-free report failure tolerates equal keys) and that A1's injectivity term is `ε_inj`, bounded by a zero-query joint-EUF reduction, so that no distributional property of key generation is assumed.
18. **Framing of the symbolic relation.** Confirm that the deliverable is a documented event/capability map (sections 11-12), with bounded tier-B results stated on their windows, the quantum lines and capabilities O15, O16, O23, O25-O27 symbolic-only, and no computational-soundness theorem.
19. **Ordering and parallelism.** Confirm the stage order of section 14, in particular the widened CE-3 spike before item 2's S1b, and whether items 4 and 5 may start against CE-11's interface before CE-10 is complete.
20. **Still-open earlier decisions.**
    - KEM join decision 5 (independent review before integration) and decision 6 (existential owner address, unread owner constant).
    - Item 2 inputs 3, 7, 9 and 10.
    - From the October 5 handoff: OD6, OD8 and confirmation of the Rust basis (central branch with `5cbd76e`).

## 17. What this plan does not claim

- It is not an end-to-end theorem, and it claims no completion of items 3 to 5. CE claims that depend on items 4 and 5 are scheduled, not proved.
- No computational-soundness transfer of any ProVerif result. No symbolic result is upgraded to a computational bound, and no computational selection or guessing term is attributed to the symbolic side.
- No root secrecy as `attacker(root)` unless CE-RG is built; CE-KT is a key transfer.
- No quantum or post-quantum authentication claim; CE is classical.
- No published-tuple provenance, R1' or A1 on runs with a failed Fresh bundle call, unless owner input 15 (a) or (c) is approved.
- No forward secrecy against a later disclosure of KEM key `k`, no post-compromise recovery, and no KCI.
- No reveal capability of any kind; the freshness and compromise-timing requirements are vacuous under Π = ∅, not discharged for any non-empty profile.
- No multi-object Server results before CE-M.
- No new primitive game. The codec laws of owner input 14, the optional `phase1Total` of owner input 15 and the scope extensions of owner input 13 are used only after approval; until then the plan states the conditional or fallback form. Item 2's R1 scope extension, its Extract-on-`uniform32` game and `SourceFullCorrect` are inherited exactly as the owner approved them on 2026-10-06.
- No persistence, snapshots, restoration, codec internals, running-code access or primitive implementation claims.
- No production Rust change, so no mutation testing applies.

## 18. Critique responses

Each point of `critique.md` was re-checked at `bccd853e` before it was adopted. The critique's citation check (its section 1) was confirmed; its additions are folded into section 1.

| Critique point | Verdict after re-check | Where addressed |
| --- | --- | --- |
| H1 `create` cannot be compiled | Accepted. `rawCreate` runs `ensureInit` on every call (`PqxdhRegistrationScheduleSurface.lean:23-34`), source14 `.create` takes a `Word32` and replies `Nat` (`PqxdhRegistrationSchedule.lean:126,136`), and the initialized source runs `ensureInit` only at birth (`PqxdhRegistrationJointInitializedSchedule.lean:50-60`). Option (a) is adopted: local width parse plus typed `.create`, reply `none` only for a wrong width, deviation D1 justified by the vendored `sodium_init`, which returns 1 without effect after a success except on its coverage-excluded lock-error path (libsodium-rs 0.2.4 `ensure_init` maps only a negative result to an error). Option (b) remains available as a law. | §3.2, §3.9 D1, §8 (a), owner input 10 |
| H2 owner and peer reconstruction | Accepted and extended. `beaconImpl` reads only `identityKeyId`, phase and `rawAttempts` (`RawCtxBeaconLifecycle.lean:68-78`); `BeaconEstablished` is the server binding and assigned ID (`K/pqxdh.rs:632-635`). Re-check found that the associated data needs the Beacon's identity public key, available to `compile A` only from the bundle bytes, so CE-3 needs `Phase1ReadBack` (N1). The spike now covers the Beacon side and `create`. | §1, §8 (b)-(c), §14 CE-3 (18-30) and spike (4-6), risks 1 and 12, owner input 14 |
| H3 signed-but-unpublished tuples | Accepted. Confirmed in Rust (`R/beacon.rs:349-362`), Lean (`PqxdhLivePhase1Bundle.lean:4,41-54`) and `doc/proverif-fs-event-meaning.md:114`. CE-A2 is restated on the signing history, which `raw_origin` already covers including failed writers. CE-A2pub, CE-R1' and CE-A1 carry the public condition `NoBundleFailure` unless the owner extends the existing law `phase1Total` (N3) or funds CE-8r. `R_c` stops at a failed target bundle. | §0 item 5, §4, §5, §10, §12.1-12.2, §14 CE-7, CE-8, CE-8r, owner input 15 |
| H4 A2 detector not public | Accepted; resolved by a route not listed in the critique (N2). Every successful raw accept is reported at every generated index (`PqxdhRegistrationJointRawReports.lean:12-33`), `raw_origin` (`PqxdhRegistrationJointAttemptOrigin.lean:34`) classifies every reached accept, and `fieldOrigin_advantage_le_sum` (`PqxdhJointPhase1Reports.lean:330`) bounds the monitor flag with coefficient one. `compile A` outputs nothing for A2, no publicity is needed and no factor is charged. The critique's per-ordinal `qAccept` union is kept as the fallback. The omitted getters are deviation D2. | §0 item 5, §7, §10 CE-A2, §14 CE-7, owner inputs 5, 10 |
| H5 events must be computable by `compile A` | Accepted. Root coordinates are removed from CE observables; `CE.Logs` (records only) is the reproducible part; the native registration ghost is excluded from the projection and used only by `R_c`; CE-OR and CE-UKS are restated over public data with the public counterpart from `designate`. | §4, §8 (e), §9 (definition of `D_g`), §10, §11 O19, §12.4 |
| H6 Beacon-side key match | Accepted (counterexample checked against `KeyMatchFinal`, `KemRawBridge.lean:33-37`). The PQ-key conjunct is added. `approved_protected` is dropped (false on the Beacon side and unused). | §6, §7, §14 CE-5 |
| H7 narrowed eligibility | Accepted. CE claims keep CE eligibility; corollaries add `ε_A2` (Server side, nested sets) or `ε_A1` (Beacon side) once, with no selection factor, and every affected section 12 row names the term. | §9 corollaries, §10, §12.1-12.2, owner input 6 |
| M1 root secrecy | Accepted. A1-root, S3-server and S3-beacon are marked partial; the optional CE-RG endpoint is designed with a recomputation proxy computable by `compile A`; "final ideal term is 0 for key transfer" is corrected. | §9.7, §10 CE-RG, §12.1-12.2, §14, owner input 16 |
| M2 quantum lines | Accepted. VC:168-173 are passive-quantum lines; they and `PV/quantum-capabilities.pvl` are symbolic-only. | §1, §11 O25, §12.3 |
| M3 KEM hop already two-sided | Accepted (`KemRawCertified.ideal_close`, `:124-135`; `KemRawGame.ideal_close`, `:194`). CE-9b is limited to T4 and re-estimated at 3-6 days. | §0, §1, §9, risk 4, §14 |
| M4 selection forms not equal | Accepted. The headline is the `Σ_g` form; `N·Adv(B_guess)` needs signed hop variants. | §0 item 4, §7, §9, §14 CE-4, owner input 5 |
| M5 replay facts cited from ServerAuth | Accepted in part. The ServerAuth facts are now cited as templates only, and CE-R1 is a new proof over `CE.handler`. Re-check found source14-level facts that the critique did not list (N4): `PqxdhRegistrationSchedule.handler_admission`, `program_consumed`, `build_consumes`, `no_rebuild` (`PqxdhRegistrationScheduleState.lean:117,130,174,196`) and `handler_consumed_count` (`PqxdhRegistrationScheduleLedger.lean:84`); CE-R1 reuses them. | §1, §5, §10 CE-R1, §14 CE-6 |
| M6 Π = ∅ makes freshness vacuous | Accepted. Wording changed to "moot, not discharged"; the reveal command is removed from `CESpec`; the timing table is documentation only and its A1 row now follows ServerAuth restriction 2; CE-13 amends `doc/composition-assumptions.md:33` only after owner confirmation. | §0 item 2, §3.5, §6, §14 CE-13, owner input 2 |
| M7 component freshness on `compile A` | Accepted. CE-11 now delivers the un-compiled `CE.idealGame g` and a second compile lemma, as an explicit precondition of step 9.6; re-estimated at 8-14 days. | §6, §9 step 9.6, §13, §14 CE-11 |
| M8 collision terms | Accepted. The A2 term is dropped (the report failure is address-free; `PqxdhRegistrationJointRawReports.lean:4`). The A1 injectivity term is `ε_inj`, bounded by a zero-query joint-EUF reduction under the approved joint game; no key-generation distribution property is assumed. | §10, §11 O1, owner input 17 |
| M9 coin cap not static | Accepted. `ℓmax` and `qFreshBytes` are added. | §3.6, §3.8, §8 budget table, owner input 8 |
| M10 scope list incomplete; codec coherence | Accepted. Owner input 13 now lists every primitive game and idealization per headline; owner input 14 lists the codec laws, and section 8 (f) ties the record codec to source14's `Codec`. | §2, §8 (f), owner inputs 13-14 |
| Lower 1: finish in `Fresh`/`FreshWithCoins` | Accepted. | §1, §3.2, §5 |
| Lower 2: A1 loss as `Σ_c` | Accepted. | §7, §10 |
| Lower 3: CE-LOR single test session | Accepted. | §3.6, §10, owner input 7 |
| Lower 4: sampling swap for `b` | Accepted. | §8 (d) |
| Lower 5: `Decision`/`Choice` names | Accepted: `CE.Output`, `CE.Claim`. | §3.7, risk 10 |
| Lower 6: further chain-release sites | Accepted (sites checked: `PV/record-origin.pvl:34-36`, `PV/exact-interface-strong-b2s.pvl:34-36` and its variants). | §11 O15, O16 |
| Lower 7: VC:3161 capability differences | Accepted (`PV/registration-provenance.pvl:14-28,51-58`). | §11 O23, O26, O27, §12.1 |
| Lower 8: items 4/5 rows are placeholders | Accepted; labelled "Planned". | §11 |
| Lower 9: omitted getters in owner input 10 | Accepted, with the pre-bundle availability caveat. | §3.9 D2, owner input 10 |
| §5 requirement check, §6 owner-decision check | Accepted. Each "at risk" item is now an explicit owner input (D1 and `ensureInit`, `phase1Total`, collision terms, ROM and AEAD scope, codec laws). | §16 |
| §7 effort | Accepted. Item 3 proper re-estimated at 78-128 days (from 61-102); CE-9b reduced to 3-6; CE-11 and CE-12 raised; re-estimate after the spike. | §0 item 8, §14 |

Further findings from the re-check, beyond the critique:
- **N1.** The Beacon's associated data and the public designation's key and ciphertext comparisons are tied to the native values only through the codec readback laws. `Phase1ReadBack` is defined (`C/PqxdhServerAuthNegativeControl.lean:55-60`) but used only by the negative-control and witness modules, so its use in CE is an assumption that needs owner approval (owner input 14).
- **N2.** The existing raw-accept reports make A2 factor-free over all accepts (H4 response).
- **N3.** A Phase-1 writer-totality law already exists as `ControlLaws.phase1Total` (`C/PqxdhServerAuthNegativeControl.lean:86`), approved for the negative controls; extending it is a scope decision, not a new law (owner input 15).
- **N4.** source14-level replay facts exist and are reused (M5 response).

## 19. Owner decisions (2026-10-06)

- **Codec laws approved** as explicit codec contracts of the common experiment, listed in both assumption lists: `Phase1ReadBack`, `Phase2ReadBack`, `FrameReadBack`, and one codec for registration and records with `DecoderAgreement`.
- **Bundle-writer failure:** option (b), conditional claims. CE-A2 is unconditional on the signing history; CE-A2pub, CE-R1' and CE-A1 hold on `NoBundleFailure` runs.
- **Recommendations accepted:**
  - one live Server object and one key ID per seed;
  - observation modes O (authentication) and P (secrecy);
  - the exact sum over targets;
  - weak secrecy first;
  - deviations D1-D4, including the omitted public getters;
  - `supplied = none` in every security statement;
  - root-secrecy targets marked partial;
  - the symbolic results as a documented event and capability map.
- **Compile-lemma trial:** run the CE-3 trial first, then re-estimate.
- **Reveal profile:** the classical core has no reveal command. Add a post-run "later quantum" reveal mode for harvest-now-decrypt-later confidentiality. After the run ends, every honest X25519 secret, every DH output and every honest Ed25519 identity secret is revealed, and only confidentiality of the run's records and keys is claimed. Authentication is not claimed in this mode. This mode is the computational counterpart of the passive-quantum ProVerif lines. Its cost must be designed and confirmed before it is built. `doc/composition-assumptions.md:33` is amended to describe exactly this profile.

## 20. Plan change after the CE-3 trial (2026-10-07)

- **Transported read caps (section 8 budget table).** The trial's `compile_bound` (`PqxdhDeploymentCompileBudget`, commit 28160a82 on `codex/deployment-experiment`) gives looser caps than the table: `.inl 8` reveal at most the budget of Server send plus Server raw-receive commands (not `qBuild`), and `.inr` kernel read at most the budget of Beacon send plus Beacon raw-receive commands (not `min(qCreate, qFinish)`). Cause: `peerKernel` and `ownerKernel` in `PqxdhDeploymentCompile` read whenever there is no local copy, including for uninstalled key IDs and non-established owners, and a `none` answer is stored as `none`, so the read repeats on later record commands. Soundness is unaffected: the review's probe instantiates T4 `actual_le_real` on `compile A` with `compile_bound` as `certified`, and `room` uses only the create cap. Decision: accept the looser caps as a plan change; every KEM, root or other bill that counts reveals or kernel reads (CE-9 and later) uses the record-command budgets. Recovering the table's caps would need the reads gated on the public log (for example `log.builds kid` and `log.finishes index`) and an amortized whole-run count instead of the per-command `FinitePartitionQueryBounds.weighted_bound` argument, with changes to the compile, records, invariant and budget modules; that is not a small change and was not done. The other rows of the table are unchanged (hash: `qHash` plus one per record command; identity, KEM, prekey and one-time reads 0).
- **Re-estimate (section 14).** Only CE-3 is revised on evidence: about 7-12 agent-days in total (4-6 spent, 3-6 remaining). All other stages keep their section 14 ranges, unrevised; item 3 proper becomes about 67-110 in total (63-104 remaining). F1 options (b) and (c) have no derived estimate; section 8 fallback (b), +25-45, is the only comparable planned figure.

## 21. Owner decisions (2026-10-07)

- F1: option (a). The common experiment's adversary takes no input and learns the Server identity key through the protocol. This is recorded as deviation D5 (central `4037fae3`).
- The main build continues in reviewed increments after the CE-3 trial, which is published on central at `4037fae3`.

## 22. Owner decisions and state (2026-10-07)

- Later-quantum profile: build LQ (the Beacon-side post-run reveal) now, as deviation D6: Server secrets are not revealed. Run a 3-5 day spike on LQ-F (the exact profile, including the Server identity seed and ephemeral scalars) and decide between LQ-S and LQ-F afterwards. The design is at /tmp/bc-arc-scratch/common-experiment/reveal-mode-design.md.
- Unit A is published (central `d42c4d3d`, branch `codex/deployment-unit-a`): 120 statements added, 250 in total. CE-9 is re-estimated at 5-10 days because `KeyMatchFinal` needs a new bundle-to-pool invariant. The coin and BLAKE2b cap loosening (+qTest+qFresh) is listed as a plan change next to §20, awaiting owner confirmation.

## 23. Owner decision and state (2026-10-07)

- Later-quantum: LQ-F, the exact profile, is chosen. The post-run reveal includes the Server identity seed and the Server ephemeral scalars, in addition to LQ's Beacon-side values; ML-KEM secrets are never revealed. Deviation D6 disappears once LQ-F lands. The spike branch is `codex/deployment-lqf-spike` (4bf12147, 109 statements, not yet reviewed), and about 7-16 days remain.
- CE-9 is published on central `e90d54d9`. It has 70 statements, and the deployment total is 526.

## 24. Owner decisions (2026-10-07, cooperation with Codex)

- Codex takes handoff items 4 and 5, under the coordination protocol in /tmp/bc-coord (PROTOCOL.md v2, brief tasks/codex-items-4-5.md). Input 19 = yes.
- The hand-off interface is Codex's `PqxdhRecordLiftInterface`, which CE-11 imports (this changes the §14 CE-11 row). Item 2's S7 reuses `PqxdhRecordLiftLazyTable`.
- The "ProVerif first" priority is superseded by the 2026-10-06 handoff ordering.

## 25. Owner ruling (2026-10-07, in Codex's session; relayed in /tmp/bc-coord message 17)

Failed registration receives stay in the CE/registration lane. Claude owns three things: the finish-time raw receives at sequences 2..51 that run before the sequence-one check (beacon.rs:462-469), their source proof, and their extra query accounting (up to 51 KDF callbacks and their shared-hash work per candidate receive). The record lift (Codex) consumes the post-registration seed through a CE-owned hook or a preceding equality/hybrid that preserves these effects. No noninterference premise may replace that proof.

## 26. CE-11 commitments to Codex (answer #26 in /tmp/bc-coord, 2026-10-07)

Full text: /tmp/bc-arc-scratch/coord-replies/r1-audit/reply-final.md §4 and §6.

CE-11 now includes:
- the erasure equality `CE.idealGame g = CE.idealGame° g`. In the ° game, an invalid sequence-one finish raw on a hidden entry rejects with no derivation and no hash. The global part is the lazy-sampling erasure of a BLAKE2b query whose answer is unused;
- the split of H4's 108 bytes into env-owned `FirstMaterial` and a world seed drawn lazily at the first `.hidden` install;
- the env_g definition;
- C1-C6.

In item 2, S3b/S4b keep `PqxdhServerAuthSendFactor.factored` and `PqxdhServerAuthBeaconFactor.factored` for hidden entries.

The interface's provisional freeze (v1) applies once Codex removes the candidate items and imports `PqxdhRecordLiftSeed`. The full-freeze conditions are F1-F6, the doc boundary, `Caps.derivations = sends + 51·receives`, and an analysis projection hidden from env.

## 27. Owner decision (2026-10-07): LQ-F profile exceptions

LQ-F's post-run reveal is stated as "every honest X25519 secret and every honest Ed25519 identity secret, except two kinds of scalar that are never published or used": (a) the one-time scalars of failed Beacon bundle attempts, and (b) the Server ephemeral of an accept that fails the PQ-key parse. These are documented with the reason, and no further proof work is done for them.

## 28. Interface v1 frozen (2026-10-07)

Claude acked the provisional typed v1 freeze of `PqxdhRecordLiftInterface` at `8129cd49` (message 35 in /tmp/bc-coord). The CE-11 shape note is amended to the v1 types; the full text is in /tmp/bc-arc-scratch/coord-replies/v1-check/ack.md §C:
- envG's state holds (key32, nonce12); the world draws `Seed`;
- install calls take `.hidden j`, and the role comes from the operation;
- startup maps `construct` to `Option (Created Unit × EnvG)`;
- C1 targets `program envG … A` composed with C7;
- C2a is a per-class allowanceG with hash = 1 at build and finish;
- C4 is `B.hash + S + R + envTotal`, and the generic Frame-to-envTotal transport is Codex's (R2);
- C6 shows that revealOf reads only envG's copy, because the world also receives the full `Created`.

## 29. C4 cross-review (2026-10-07, message 56 in /tmp/bc-coord)

Codex's `PqxdhRecordLiftBudget` (sha aa528550...) is acked with notes; evidence is in /tmp/bc-arc-scratch/coord-replies/c4-review/. `program_bound` instantiates for CE-11 without conversions: coin `(qInit+32) + transported coin + E(.coin)`, hash `B.hash + qBuild + qFinish`. The per-class wrapper matrix charges each test or fresh as a send twice, so it gives `S + R + qTest + qFresh` and cannot reach `Caps.derivations = sends + 51·receives`. Codex was asked for a joint send bound (predicate kind ∈ {8,10}). Until it lands, CE-11 states C4 as `transported(.inl 7) + qBuild + qFinish` and tightens it afterwards; if the joint bound fails, `Caps.derivations` gains `qTest + qFresh` in a v2 note.

## 30. CE-8 review fix pass and the Beacon-side ciphertext link (2026-10-07, Claude decision)

- Correction to §9 and §10 (line "the eleven fields carry the ciphertext and the PQ key"): ServerAuth's `Session` has no ciphertext field, and the ServerAuth root input carries the KEM shared secret, not the ciphertext. The fix pass (c4ad86ff on `codex/deployment-server-auth`) shows the ciphertext link is not provable at the CE-A1 bound: with a KEM whose decapsulation ignores the ciphertext, a relayed build reply with a replaced ciphertext is accepted while the bound stays small. The root link cannot be stated on the outcome because the experiment keeps no roots.
- Decision: CE-8 keeps the public matching pinned to the Server identity (`A1NoPinnedMatch`, a strengthening of the headline event) and integrates without the ciphertext link. The ciphertext link moves to the Beacon-side symbolic-eligibility corollary of CE-12, which gains a term `ε_ct` next to `ε_A1`. `ε_ct` bounds "an established Beacon of owner `k` accepts with a ciphertext different from session `i`'s while its root input equals session `i`'s (ServerAuth's ghost `Partner`) and accept `i` verified `pk_k`". The route is a per-pair `(i, k)` IND-CCA reduction (the decapsulation oracle on the Beacon's ciphertext detects the shared-secret collision) plus the ideal-world probability of the same event, bounded statistically through R1 lazy sampling of the uniform key (the adversary and other Beacons query a point containing it with probability about `(qHash + qFinish)/2^256` per pair). IND-CCA is an existing assumption; no new assumption or contract. Detailed design at the start of CE-12. `designate` keeps its ciphertext-equality conjunct, so CE-9 is unaffected.
- Owner input 17 asked for a zero-query collision reduction for `ε_inj`. The fix pass built `B^coll_t` with one signing query; it is replaced by the zero-query variant (the reduction holds the colliding seed and signs itself) before integration.
- Note (2026-10-07, confirming review of CE-8 at `1170bf02`): the `ε_ct` event above is stated on root inputs (ServerAuth's ghost `Partner`), while CE-A1 bounds only the public pinned match (`A1NoPinnedMatch`), which states no root agreement because the experiment's outcome keeps no root. CE-12 must therefore also connect the public pinned match to ServerAuth's `Partner`. Options: (a) a ghost-level version of the CE-A1 chain, in which `root_failure` and `typed_root` carry the root inputs of the root-audited run through the embedding; (b) an `ε_ct` event stated on the public pinned match, whose root-mismatch branch (the matched session's root input differs from the Beacon's) gets its own bound. The earlier CE-8 remark that root agreement is not needed by the section 9 eligibility is withdrawn. The CE-12 estimate for `ε_ct` (roughly 3-6 agent-days, guide "CE-8: re-estimate") excludes this step. `ε_ct` and its IND-CCA route are planned, not proved, and the ciphertext counterexample of the first bullet is an informal argument recorded as a negative control, not a Lean statement.

## 31. C4 final (2026-10-07, message in /tmp/bc-coord answering 66)

Codex's joint send/raw bound (`PqxdhRecordLiftBudget` b9ede84b, `program_record_bound`) is acked. The interim C4 form of §29 is withdrawn. CE-11 uses `capsG B := ⟨B, B.hash + B.sends + B.receives + Caps.envTotal ⟨B,0⟩ allowanceG .hash⟩` (= qHash + S + R + qBuild + qFinish; derivations = S + 51R, frozen definition), with premises C2a `Frame envG (qInit+32) allowanceG` and `B.Respects A`. Codex's R2 proves the generic World support bounds (hash ≤ B.hash + S + R + envTotal allowance .hash, KDF ≤ caps.derivations) through a per-class weighted transport; CE-11 only instantiates allowanceG and proves C2a. Probe evidence: /tmp/bc-arc-scratch/coord-replies/c4-joint/.

## 32. CE-11 design and re-estimate (2026-10-07, Claude decision)

Design /tmp/bc-arc-scratch/common-experiment/ce11/design.md with adversarial critique critique.md (no blocking finding; 9 major, 12 minor, all accepted). CE-11 splits into CE-11a (generic over the registration handler: the lazy-oracle erasure engine `LazyOracleDiscard`, the pluggable native game `gameWith` taking the constructed Server, hidden-entry wrappers as instances of item 2's `Services.hiddenBuild`/`hiddenAfter` signatures, C7, the 108-byte split, envG state without record coordinates (commitment reply-final §4.4), C2a, C3, C1 and C6) and CE-11b (item 2's ideal registration, `CE.idealGame g`, C5's public slot/peer/owner maps, the second compile lemma, key-first/key-last). C4 follows §31. The real-registration instances (`envReal`, `c1_real`, `c6_real`, `frame_real`) are validation and are cut first under schedule pressure; per-command lemmas reused by CE-11b stay. Re-estimate: CE-11a about 27-48 agent-days, CE-11b about 17-32, so the §14 CE-11 row moves from 8-14 to about 44-80 and item 3 proper from 67-110 (§20) to about 103-176 nominal. Reason: the §25-§29 commitments (C7, the 108-byte split, envG, C1-C6) postdate the §14 row. Order: increment 1 (engine and layout) with a 3-day spike on `finish_erase_local`, `discard_erase` and the labelled-kernel identity (critique M3), then native game, C7 and split, then envG/C2a/C4, then C1/C6.
