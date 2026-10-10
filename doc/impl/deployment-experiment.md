# Common deployment experiment: interface, deviations, compile argument, selection and symbolic map

Status (Claude, 2026-10-10): this is the CE-13 guide of handoff item 3, the documentation stage of the common deployment experiment (plan section 14, row CE-13). It describes the experiment as it is stated in Lean on central `codex/full-proof-composition` at `529e2c8bf414f680ac57b159365280aab2e2f3f2` (CE-12 P1, P2, P2b, P3, P4 and D-ct, item 7 and the production composition of items 3 and 7 integrated), and it maps the security-class ProVerif targets to the computational statements proved there. It adds no Lean statement, no assumption, no contract and no Rust or test change. The stage-by-stage record of how the experiment was built (CE-1 to CE-12, the LQ-F upstream and every review) is the [common deployment experiment record](common-deployment-experiment.md); the plan is the committed snapshot [common-deployment-experiment-plan.md](common-deployment-experiment-plan.md); the production boundary and the authoritative D1-D6 ledger is the [PB-E ledger](production-boundary-ledger.md); the production forms of the headlines are described in [production-headlines.md](production-headlines.md). The per-row computational column is the section "Computational column: the common deployment experiment" of [the ProVerif source-scope ledger](../proverif-source-scope.md); the approved reveal profile and the assumptions of the headline claims are recorded in [the composition assumptions](../composition-assumptions.md); the plain-English summary is the section "Common deployment experiment, CE-13: what is computational now" at the end of [the analysis](../formal-verification-analysis.md). Receipt: [proof-receipts/common-deployment-experiment-ce13.json](proof-receipts/common-deployment-experiment-ce13.json).

## How to read this guide

Every claim below names the Lean statement that carries it; the code is authoritative: the Rust reference is `beaconcrypt/src` and `beaconcrypt-core/src` of the same central commit, and every Rust anchor below was read there. Module names are short: `PqxdhDeploymentX.name` stands for `BeaconcryptCore.Computational.PqxdhDeploymentX.name`. A statement is cited only for what its Lean text says. Where a symbolic target says more than any Lean statement, the difference is listed as symbolic-only; it is never called computational. Bounds are given with their exact terms; the abbreviations are defined in "The terms of the bounds" below.

Scope fixed by owner decisions and kept throughout: Cap'n Proto and every other codec internal are out of scope (the experiment uses an abstract codec whose read-back laws are explicit premises); persistence, snapshots, restoration and attacker access to running code are out of scope (the persistence-wrapped Server surface of the C, Go and Python bindings stays outside every claim); libsodium and the other native primitives are trusted; the proof Server is idealized (one live Server object with a generated identity seed, perfect key management, one key ID per seed).

## The experiment

### Construction and adversary

The classical experiment is `PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary`. It constructs the protected Server with `PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none`: a generated identity seed (`supplied = none`), runtime initialization once at Server birth, identity index 0 in every headline (a few earlier statements, such as CE-A1's `ce_a1` and the replay facts, hold for every index). A constructor failure ends the run with no outcome. The adversary `adversary : OracleComp (ModeSpec mode) X` takes no input (deviation D5): it learns the Server's identity key through the protocol. It runs against the CE handler, the secrecy ledger `PqxdhDeploymentSecrecy.ledgerImpl` on top of the native handler `PqxdhDeploymentNative.handler`, and returns its own output `X`; the headlines use `PqxdhDeploymentInterface.Output` (an optional fresh-message claim and a bit) or an arbitrary output type with an event and a claim read from the observation.

### Commands and their Rust counterparts

The commands are `PqxdhDeploymentInterface.Command` (public commands) and `PqxdhDeploymentInterface.Secrecy` (the two secrecy commands). Every reply is the production code path modelled in Lean: source14 (`PqxdhRegistrationSchedule`) for registration, `RawCtxServerMixed.serverImpl` and `RawCtxBeaconLifecycle.beaconImpl` for records.

| Command | Reply in mode O | Reply in mode P | Rust | Native answer |
| --- | --- | --- | --- | --- |
| `create pin keyId` | `Option Nat` (owner handle) | same | `Beacon::try_new` (`beacon.rs:65-82`) | width-only parse `parsePin` (32 bytes, no point check); a wrong width replies `none` before any draw; otherwise source14 `create` (identity, prekey and ML-KEM key pair in production order); runtime initialization is not re-run (D1); any pin (AnyPin) |
| `bundle owner` | `Option Bytes` | same | `get_registration_bundle` (`beacon.rs:300-399`) | generation and the three signatures precede the writer; a failure keeps the owner Fresh, so it may sign again; at most one bundle is returned |
| `accept raw` | `Option Nat` (session handle, the raw-accept ordinal) | same | `get_shared_secret` (`server.rs:332-422`) | an ordinal is allocated on every attempt; the registration ID is consumed only on success; the pending token is stored under the handle |
| `build session payload` | `Option Response` | same | `build_registration_response` (`server.rs:424-502`) | the token is moved on every outcome; the peer is installed only on full success; `payload = none` selects `REGISTRATION_WITNESS` (`server.rs:459`, `shared.rs:50`), any other payload is adversary-chosen (D4) |
| `finish owner raw` | `Option Bytes` (application suffix) | same | `finish_registration` (`beacon.rs:402-510`) | only in InitSent; every failure aborts; every other phase replies `none` with no change; the suffix is returned in both modes |
| `hmac key message` | 64-byte block | same | none (public computation) | the restricted programmable random oracle of route R1 on the zero-salt 192-byte Extract slice, shared with every honest root derivation; the real HMAC-SHA-512 otherwise |
| `hash bytes` | BLAKE2b-512 digest | same | none (public computation) | programmable classical random oracle, one lazily sampled cache shared with every CTX commitment |
| `serverSend keyId plaintext` | `Option Encrypted` | same | `Server::encrypt_message` (`server.rs:224-228`) | `serverImpl` send on the installed peer |
| `serverRaw raw` | `Option Decrypted` | `Bool` (success bit) | `Server::decrypt_message` (`server.rs:229-250`) | `serverImpl` raw receive, routed by the claimed sender; every failure keeps the whole Server |
| `beaconSend owner plaintext` | `Option Encrypted` | same | `Beacon::encrypt_message` (`beacon.rs:152-163`) | `beaconImpl` send (Established only) |
| `beaconRaw owner raw` | `Option Decrypted` | `Bool` | `Beacon::decrypt_message` (`beacon.rs:164-174`) | `beaconImpl` raw receive (Established only; every attempt counted) |
| `test handle left right` | `Option Encrypted` | same | modelled application request | admitted only if `left` and `right` have the same nonzero length and the handle names the test session (below); then exactly one send of `left` or `right` by the hidden bit |
| `fresh handle length` | `Option Encrypted` | same | modelled application request | admitted only if `min ≤ length ≤ max`; the experiment draws a uniform message of `length` bytes, keeps it private and sends it on the handle |

There is no DH, signing or KEM oracle, no reveal command, no public getter and no snapshot API. Public HKDF outside the R1 slice is computed by the adversary with the real function, which the theorems quantify over after the setup (the inherited random-oracle caveat).

### Observation modes

`PqxdhDeploymentInterface.Mode` has two values, fixed as a parameter of the game. Mode O returns the actual optional plaintext of every raw receive. Mode P returns only its success bit (`observeFull`, `project`). Secrecy headlines (CE-APP, CE-LOR) are stated for mode P only: in mode O a raw receive of a test or fresh ciphertext would return the hidden message. Authentication headlines hold in every mode. The ledger's transcript records the mode-O reply of every query in both modes, so in mode P the transcript is an analysis log, not the adversary's view; the view of an entry is `Entry.view mode`.

### Secrecy commands and the test session

The first admitted `test` draws the hidden bit with one experiment coin and fixes its handle as the test session; a later test is admitted only on the same handle or on a handle with the same public designation as the first (`PqxdhDeploymentSecrecy.SameSession`, computed on the transcript so far). An admitted test is exactly one send, with the send's allocation, failure and rollback behaviour. A `fresh` command draws one experiment coin per byte when it is issued, and its entry `⟨handle, message, reply⟩` is recorded in `Ledger.fresh` whether or not the send succeeds. Rejected secrecy commands change nothing but the transcript. CE-LOR is therefore a single-test-session game; both directions of that session can carry tests.

### What the events read

Every headline event is a function of `PqxdhDeploymentKemTransfer.Observed`: the adversary's output, the ledger (transcript, test session with its bit, fresh messages) and the produced frames (`Logs.produced`, every successful seal callback including those whose writer then failed). These are the experiment's own records in plan section 9's sense, not a public view: no event reads a root, a key, partnering or the native registration ghost. The reductions behind the loss terms evaluate the event and the claim (for CE-LOR also the filter and the guess), so the advantages are small under the contracts only when those functions are efficiently computable. The symbolic-eligibility events (`SymServer`, `SymBeacon` and the `*Sym` events) also read the final native owner identity keys (`PqxdhDeploymentPublishedTuple.ownerIdentities`) and the constructed Server's identity (`PqxdhDeploymentServerAuthEvent.protectedBinding`); they are the ProVerif-shaped eligibility conditions, not public functions of a view.

### Budgets

`PqxdhDeploymentInterface.Budget` caps every attempt, rejected ones included, in fourteen classes: coin, create, bundle, accept, build, finish, HMAC, BLAKE2b, Server send, Server raw receive, Beacon send, Beacon raw receive, test and fresh (`queryClass`, `Budget.cap`); `budget.Respects adversary` requires each class to stay within its cap on every execution path. Derived quantities: `S = Budget.sends` (Server and Beacon sends, tests and fresh messages), `R = Budget.receives` (raw receives), `Budget.capacity = qCreate + 1`, `Budget.targets = qAccept · (qCreate + 1)` and `Budget.freshBytes = max · qFresh`. The LQ-F post phase has its own `PqxdhDeploymentLater.PostBudget` (coins, HMAC and BLAKE2b, `qCoin₂`, `qHmac₂`, `qHash₂`).

## Reveal profile

### Classical core: no reveal command

The classical experiment has no reveal command (owner decision of 2026-10-06, plan section 19). No Server state, pending token, Beacon field, root, chain or ratchet state is ever disclosed to the adversary. The only compromise in scope is static: identities that the adversary generates itself, and Beacons it pins to such identities (AnyPin). Under this profile the handoff's freshness and compromise-timing requirements are met vacuously; they are moot, not discharged for any richer profile. Internal kernel reads inside the compiled program and inside the CE-A1 reductions are proof devices that are never answered to the adversary (`PqxdhDeploymentCompileSecrecy.compile_full_unread`: the compiled program issues no identity, KEM, prekey or one-time read).

### Later-quantum mode LQ-F

The owner's 2026-10-06 decision adds one post-run reveal mode for harvest-now-decrypt-later confidentiality, and its 2026-10-07 decisions chose the exact profile (LQ-F) with two exceptions (plan sections 19, 23 and 27). The game is `PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit 0 bounds mode first second`: the Server is constructed with a generated seed, the run-phase adversary `first` runs against the run-phase handler (the classical handler plus a finish snapshot and an ephemeral log), then the reveal is computed from the final state, then the post adversary `second : X → Reveal → OracleComp PostSpec Out` runs on the run's output and the reveal with post-run coins, the public HMAC and the BLAKE2b oracle as its only queries. The reveal (`PqxdhDeploymentLaterServerGame.Reveal`) is:

- for every created Beacon, in creation order, its Ed25519 identity seed and its X25519 prekey and one-time scalars, current or captured by the finish snapshot (`PqxdhDeploymentLater.revealOf`);
- the Server's Ed25519 identity seed (its X25519 identity secret is the production conversion of the seed) and the log of every Server ephemeral scalar, one entry per raw accept whose generation step was reached (`PqxdhDeploymentLaterServerSource.Reveal`).

Diffie-Hellman outputs are derived from the revealed scalars and public points, not listed. ML-KEM secret keys and shared secrets, the R1 Extract table, roots, chains, kernels, skipped keys and plaintexts are never revealed. The two approved exceptions (plan section 27) are scalars that are never published or used: (a) the one-time scalar of a failed Beacon bundle attempt, generated at `beacon.rs:302` and dropped when signing or serialization fails (`beacon.rs:349-357`), which is in no state and is not revealed; (b) the Server ephemeral of an accept that fails the PQ-key parse, generated at `server.rs:368` and dropped when the parse rejects (`server.rs:369-372`), before its public key is published or the scalar enters a Diffie-Hellman step. Later failures of the same accept before the ephemeral's first Diffie-Hellman step (the encapsulation at `server.rs:373`, the identity conversions and the first Diffie-Hellman step at `server.rs:374-378`) drop it in the same way; in every such case the Lean log records the generated ephemeral, so the Lean reveal contains it (no statement relies on that). In this mode only confidentiality of the run's records and keys is claimed (CE-KT-L, CE-APP-L, CE-LOR-L); no origin, unknown-key-share, binding or authentication statement is made, and none of the provenance theorem A2 or item 2's T5 and T8 is cited on the later compiled program. The post adversary is a classical oracle algorithm: this is not a quantum (QPT) or quantum-random-oracle (QROM) claim, and nothing is transferred from the ProVerif passive-quantum results.

## Deviations D1-D6

The authoritative ledger of the deviations is the section "Deviations D1-D6 and other abstractions" of the [PB-E ledger](production-boundary-ledger.md), which records each with its production site, its treatment (E: approved scope decision or contract; L: joined by a published Lean theorem; RT: reviewed transcription) and the boundary rows and theorems that join it. In summary:

| Deviation | Production site | Treatment in the ledger |
| --- | --- | --- |
| D1: runtime initialization runs once, at Server birth; `create` does not re-run it | `beacon.rs:66`, `server.rs:155` | E (approved 2026-10-06); RT-20 records the libsodium pin and the once-only initialization; no idempotence axiom; joined at PB-01 by `PqxdhBoundaryBirth.server_source` and `create_source` |
| D2: the public getters are omitted | the getters of the ledger's public-surface table | E; the getters' derivability is CE-13 evidence (below) |
| D3: the snapshot-returning record APIs and the pre-Phase-1 helpers are omitted | `beacon.rs:222-296`; `server.rs:131-142`, :504-532 | E; saved-state APIs excluded; no simulation of the omitted methods is asserted |
| D4: the adversary chooses the build payload | `server.rs:459` | L/RT: every concrete payload follows the production branch (`PqxdhBoundaryRegistrationBuild.build_exact`, the empty payload rejected after the initializer); a stronger application-choice experiment |
| D5: no initial Server public-key input | `server.rs:176` | E (owner decision F1(a)) |
| D6: the historical LQ omission of Server secrets | `server.rs:27`, :368, :422 | retired by LQ-F, which reveals them; the two approved exceptions (a) and (b) remain (`PqxdhBoundaryDeploymentLater.later` keeps the full `LaterState`) |

D2 evidence (the ledger leaves it to CE-13). The omitted getters return public keys and identifiers that the adversary already holds or computes from public replies once a Beacon's bundle is public (ServerAuth restriction 11), with one availability exception that the plan records: Rust exposes a Beacon's identity, PQ and prekey public keys before its first bundle, CE does not, so CE's adversary is weaker by that early knowledge; no CE proof uses the secrecy of a public key. For `ratchet_status` (Server `server.rs:207-209`, Beacon `beacon.rs:137-142`), which returns `send_sequence`, `receive_sequence` and `receive_cache_len` of the extracted `RatchetState` (`beaconcrypt-core/src/ratchet/control.rs:63-95`, through `ratchet.rs:203-209`), the derivability is a reviewed reading of the code, not a Lean statement: the state is a pair of counters and a cache of sequence numbers; a send changes it only when the plaintext is nonempty and the sender is not exhausted, and then advances it by one whether or not the seal and the writer succeed (`encrypt_message_with_ratchet`, `ratchet.rs:414-444`); a raw receive changes it only on success, by the planned advance for the frame's sequence number, and every rejection restores the entry state (`decrypt_message_with_ratchet`, `ratchet.rs:499-532`); an unknown key ID or a Beacon outside Established returns `None` with no change. Every input of these updates is public in CE: the handle and plaintext length of each send (the adversary's own inputs, or the public length of a test or fresh message), the success of each raw receive (in both modes) and the sequence number of its frame (read from the adversary's own bytes by the public frame decoder), and the initial counters fixed by a successful build or finish. So each component of `ratchet_status` is, by this reading, a function of the public transcript; it is recorded as reviewed-transcription evidence, like the ledger's other RT entries.

## The compile argument

The headlines are proved by composing published per-target steps; none of them reads the hidden state of the experiment directly. For a target `g = (i, k)` (raw-accept ordinal `i`, KEM creation index `k`) and an event with a claim, write `D_g` for "the event holds and the claim's budgeted designation is `g`".

1. CE-COMPILE (`PqxdhDeploymentCompileSecrecy.compile_full_game`, `compile_full_source`, CE-3): the complete experiment equals the merged initialized source14 execution of a compiled program, jointly over the Server's public data, the adversary's output, the whole ledger, the whole deployment state including the produced frames and the runtime state, under `Phase1ReadBack` and `Phase2ReadBack`. The compiled program parses pins itself, runs the record handlers on local copies reconstructed from public data plus one kernel read per installed peer or established Beacon, draws the hidden bit and the fresh messages at the same positions as the experiment, and issues no identity, KEM, prekey or one-time read (`compile_full_unread`); its query caps are transported from the budget (`compile_full_bound`, `PqxdhDeploymentCompileCaps.transported`; the reveal and kernel-read caps are the record-command budgets, plan section 20).
2. The per-target KEM transfer (`PqxdhDeploymentKemTransfer.kem_transfer`, CE-9; two-sided `PqxdhDeploymentKemTwoSided.kem_transfer_two_sided`, CE-9b): `Pr_CE[D_g]` is related to the KEM branch of the compiled program at target `g`, up to one ML-KEM IND-CCA advantage of the certified raw-ordinal adversary and the ML-KEM correctness error (`kemLoss_g`). The key match comes from the public designation (`designate_keys`, `keymatch_point`), not from an authentication theorem.
3. Item 2 at two slots (`PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`, with stage T and S7): the two hidden entries, the target session's root input and owner `k`'s challenge finish, become uniform values of item 2's two-slot table, two-sided, up to `slotLoss_g` (`PqxdhRegistrationJointKemKeyTransfer.allIdealLoss` at the transported caps).
4. The second compile lemma (`PqxdhDeploymentIdealCompile.ideal_compile`, CE-11): item 2's two-slot world at the compiled program equals the compile-image of the un-compiled ideal game `PqxdhDeploymentIdealSteps.idealGame` of `g`, in which the CE adversary runs against native handlers and the two hidden entries are fed the table's values.
5. The hand-off to the record lift (`PqxdhDeploymentIdealHandoff.ideal_world_view_slots`, CE-11b): the ideal game's decision is at most the view event with the ideal-slot conditions on the all-real chain world of the ideal environment `envGD` of the target, plus the Beacon-side anomaly, which `PqxdhDeploymentHeadlineAnomaly.beta` bounds by one IND-CCA advantage of the predict-then-compare adversary `ptc` plus the correctness error plus `2^-256` (`β_g`); Server-side claims have no anomaly term (`PqxdhDeploymentHeadlineChain.chain_server`).
6. The record lifts of items 4 and 5 (`PqxdhRecordLiftComposition.record_auth_lift` for integrity, `PqxdhRecordLift.record_lift` with privacy in mode P) move the view event to the ideal record worlds (`authLoss_g`, `recLoss_g`).
7. The final ideal-world facts: the origin, binding, fresh-guess and left-or-right statements of `PqxdhRecordLiftIdeal` (`OriginStatement`, `BindingTarget`, `FreshGuessStatement`, `LorStatement`) give the final terms `publicationTerm B`, `bindingTerm BI_g`, `2^-min` and an exact half; P2b's agreement fact `PqxdhDeploymentHeadlineAgree.agreement_statement` gives probability zero for the Server-pin and plaintext failures in `idealAuth`.
8. The exact split over targets (`PqxdhDeploymentHeadlineChain.split_named`, from CE-9b's `split_create`) sums the per-target bounds with coefficient one.

For CE-KT the chain stops after step 4 (or step 5 for the World forms): the ideal-game probability stays on the right. The symbolic-eligibility corollaries (CE-12 P2) add one global term per side: `server_gap_bound` (a Server peer that is symbolically eligible but not designated is a published-tuple forgery, `ε_A2pub`), `ce_a1_linked` (a Beacon that is symbolically eligible but not designated is a CE-A1 failure or has a ciphertext gap, `ε_A1 + ctGapTerm`), the identity-collision bound `identity_collision_game` (`ε_inj`) and the ciphertext-collision bound `PqxdhDeploymentHeadlineCtColl.ct_coll_le` (`ctCollTerm ≤ ε_ctcoll`). CE-12 D-ct closes the ciphertext-gap term: `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` (`ctGapTerm ≤ epsCt`), with the `_dct` restatements of every form that carried it.

The LQ-F chain has the same shape over the logged source: `PqxdhDeploymentLaterServerCompile.compile_server_source` (the later compile lemma), `PqxdhDeploymentLaterServerTransfer.kem_transfer_server` (`kemLossL_g`), `PqxdhDeploymentLaterServerItemKeys.later_slots_two` (`slotLossL_g`, whose R1 term counts the post-run HMAC queries with coefficient one), `PqxdhDeploymentIdealLaterCompile.ideal_compile_server`, and `PqxdhRecordLiftLaterLift.later_record_lift` (`recLossL_g`); the anomaly and every symbolic term are bounded on the classical run of `first` (`PqxdhDeploymentLaterServerGame.game_classical_event`).

The production composition (item 7 with the production composition of items 3 and 7) proves that the experiment, run at the production frame codec `codec′ = PqxdhBoundaryRecordPrelude.withReader codec reader` and router `route′ = RawCtxFrameDecoding.sender reader.model`, is the same random process as the source game that runs the Lean programs transcribed from the Rust adapter (`PqxdhBoundaryDeployment.sourceGame`, `PqxdhBoundaryDeploymentLater.laterSourceGame`); `PqxdhDeploymentProductionTransfer.chance` and `chance_later` move every probability of the experiment to that source game, read back through `unwrap`.

## The terms of the bounds

- `kemLoss_g` (`PqxdhDeploymentHeadlineChain.kemLoss`): one ML-KEM IND-CCA advantage of CE-9's certified raw-ordinal adversary for the per-target decision, plus `correctnessError setup`.
- `slotLoss_g` (`slotLoss`): `allIdealLoss` at the transported caps: the R1 statistical term `(qAccept + qFinish + qHmac)/2^256`, two HMAC-SHA-512 PRF advantages and the key-schedule bounds of the two hidden entries (Extract-on-uniform32 and HMAC-PRF advantages).
- `β_g` (`PqxdhDeploymentHeadlineAnomaly.beta`): one IND-CCA advantage of `ptc` (at most `qFinish + 1` decapsulations before the challenge, none after), plus the correctness error, plus `2^-256`. Only Beacon-side (owner) claims carry it.
- `authLoss_g e`, `recLoss_g e` (`authLoss`, `recLoss`): the losses of the explicit reductions of `record_auth_lift` and `record_lift` at the ideal environment of the target for the view event `e` (chain hops: Extract-on-uniform32 and HMAC-PRF per hybrid index; integrity: IND$ validation, `qHash/2^128`, twice the attempt-indexed INT-CTXT sum and `qRaw/2^512` per target key; privacy in mode P: IND$), at the bill input `BI_g`. `IS_g` and `ISs_g` are the ideal-slot conditions of the view (all slots, Server slots only).
- `publicationTerm B = 2·R·S/2^512` (`PqxdhRecordLiftIdeal.publicationTerm`), `bindingTerm BI_g = (R + S + H)·S/2^512` with `H = sharedHashTotal BI_g` (`bindingTerm`), `2^-min` per target with `min = FreshBounds.min` in bytes (one bit charged per byte of the shortest admitted fresh message; the sum carries `qAccept · qCreate · 2^-min`).
- `ε_A2pub` (`PqxdhDeploymentHeadlineGap.a2pubTerm`): the sum over the `qCreate + 1` generated identity positions of the joint Ed25519/X25519 weak-EUF advantages of the A2 reductions.
- `ε_A1` (`PqxdhDeploymentHeadlineGap.a1Term`, real-valued, entering as `ofReal`): the sum over the `qCreate` creation indices of the Server-authentication bound of the CE-A1 reduction `R_c` at the transported caps (Gap-DH, `C(Q, 2)·64/2^256`, record and schedule losses, joint weak EUF).
- `ε_inj` (`PqxdhDeploymentHeadlineCollision.injTerm`): the sum over the `qCreate + 1` identity indices of the joint weak-EUF advantage of the zero-query collider reduction; `ε_A1inj = ε_A1 + ε_inj` (`PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective`).
- `ctGapTerm` (`PqxdhDeploymentHeadlineGap.ctGapTerm`) and `ctCollTerm` (`PqxdhDeploymentHeadlineCollision.ctCollTerm`): explicit probabilities in the experiment of the public ciphertext-gap and ciphertext-collision events. Closed by `ctCollTerm ≤ ε_ctcoll = qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2·δ_corr + 2^-256)` (`PqxdhDeploymentHeadlineCtColl.ctCollEps`, `ct_coll_le`) and `ctGapTerm ≤ epsCt` (`PqxdhDeploymentHeadlineDctEvent.epsCt`, `ctgap_term_le`), with `epsCt = Σ_g (kemLoss_g + slotLoss_g of the decision (ctGapNamed, ctClaim) + ctStat)` and `ctStat = r1Cap/2^256 + C(ctxCap, 2)/2^512`, `r1Cap = qHmac + qAccept + qFinish`, `ctxCap = qHash + S + R + qBuild + qFinish`. The `2^-512` term is a birthday term, weaker than the design's linear term; this is an owner-visible note, not an assumption.
- Later terms: `kemLossL_g`, `slotLossL_g` (closed form `(qAccept + qFinish + qHmac + qHmac₂)/2^256` plus the PRF and key-schedule advantages, `PqxdhDeploymentLaterHeadlineBills.slotLossL_eq`) and `recLossL_g` (`PqxdhDeploymentLaterHeadlineChain`); `β_g`, `ε_A2pub`, `ε_A1`, `ctGapTerm`, `ctCollTerm` and `epsCt` at the run-phase adversary `first` on the classical experiment.

A bound is called fully closed when it carries neither `ctGapTerm` nor `ctCollTerm`: then it consists of attacker advantages of constructed reductions, statistical terms and, for CE-KT, the probability of the ideal game. The bills of every reduction are proved (`PqxdhDeploymentHeadlineBillsFull.target_bills`, `headline_bills`, `ctgap_term_billed`, the later `later_target_bills_full` and `later_headline_bills`); the `*_billed` forms conjoin them where the bound carries `β_g`. Bills count random coins and oracle calls, not running time.

## Selection

The target of a claim is the public pair `g = (i, k)`: `i` the raw-accept ordinal (equal to the session handle that `accept` returned) and `k` the KEM creation index. `PqxdhDeploymentTranscript.designate` (and its budgeted form `designateIn`) is a deterministic function of the transcript that returns at most one target:

- a Server peer `kid` is designated `(i, k)` when session `i` built it (`linkOf`), its accept bytes give a candidate that the attached verification accepts with keys `v`, and `k` is the smallest created owner whose published bundle carries the candidate's identity field and `v`'s PQ key (`Publishes`). There is no condition on owner `k`'s pin and no NoBundleFailure condition, so AnyPin owners are covered;
- an owner `c` is designated `(i, c)` when it is Established, was created with the pinned key ID `serverKid`, the KEM ciphertext of its accepted finish input equals the one of session `i`'s build response whose Server identity is its pin (`Linked`), the PQ key verified by `accept i` is `c`'s published PQ key, and `i` is the smallest such session. Owners pinned to another key ID are never designated.

On the support of a budget-respecting adversary every designation has `i < qAccept` and `k < qCreate` (`PqxdhDeploymentTargetRange.range_game_create`, `designated_create`), so the sums run over `Fin qAccept × Fin qCreate`, read in CE-9's domain `Fin qAccept × Fin (qCreate + 1)` through `castSucc`. Every summed headline is the exact split of the event over the targets (`split_named`): coefficient one per target, no selection factor, no guessing reduction. The owner's `N·Adv(B_guess)` wording is not stated (it would need signed-difference forms of every hop, plan section 7). Record keys inside a session are summed exactly inside `authLoss_g` and `recLoss_g`. CE-A1 is a sum over the `qCreate` creation indices of distinct reductions `R_c`; CE-A2 has no selection factor (every successful accept is reported at every generated index). CE-LOR's eligibility is anchored on the first admitted test (`firstTest`) and requires every admitted test to designate the same target. LQ-F uses the same split (`PqxdhDeploymentLaterTargetRange.split_create_later`).

## Symbolic map

The deliverable is a documented event and capability correspondence (owner input 18): no ProVerif result is transferred to a computational bound, and no computational term is attributed to the symbolic side. Each bounded symbolic result stays stated on its own window next to the CE claim, which is parametric in the budget.

### Event projection (plan section 12.4, updated)

| Symbolic event | CE observable or statement |
| --- | --- |
| `FsBeaconStarted` | a `bundle` reply `some` (`phase c = InitSent`) |
| `ProvPublished`, `ProvAccepted` | bundle bytes; the attached verification of the accept bytes (`candidateOf`, `acceptedKeys`); signing attempts without publication exist only in the analysis (the report history of CE-A2) |
| `FsServerAccepted` | an `accept` reply `some i`; the consumed set is source14 state |
| `FsServerCommitted` | a `build` reply `some` (`buildOf`, `linkOf`); the sequence-one seal is in the native registration ghost and is used only inside `R_c` |
| `FsBeaconEstablished` | a `finish` reply `some` (`phase c = Established`) |
| `FsSent` | `Logs.produced` (allocation; frames whose writer failed included) |
| `L2Published`, `S2bPublished` | `Entry.published` (returned ciphertexts only; `PublishedBefore`) |
| `FsReceived`, `FsReceivedFrame` | `Entry.received` with the decoded frame (`codec.frameRead`) and the optional plaintext |
| `FsReceiveRejected` | an `Entry.received` with no plaintext |
| `FsFarAccepted` | no separate event: every accepted raw receive at any position up to 51 derivations ahead is inside the origin events |
| `L2SelectedIdentity` | `SymServer` (`PqxdhDeploymentHeadlineGap`): the session that built the peer accepted a candidate verifying to an owner's final identity key, and that owner made no rejected bundle call in Fresh |
| `S2bSelectedIdentity` | `SymBeacon`: the owner is Established, created with (constructed Server identity, `serverKid`), and made no rejected bundle call in Fresh |
| `…FreshPublished` | `Ledger.fresh` entries |
| `A1Root`, OD5 partner | not observables; the partner is the public counterpart `cpart`/`CEPartners` (`PqxdhDeploymentHeadlineEvents`) or the symbolic counterpart sets `SymCpartB2s`/`SymCpartS2b`; ServerAuth's ghost `Partner` appears only inside `R_c` |
| failure-cause witnesses | none (witnesses only) |

Designation and the symbolic eligibility agree only up to the gap terms. On every run, a `SymServer` peer is designated or witnesses `ServerGap` (`server_gap`, bounded by `ε_A2pub`), and a `SymBeacon` owner is designated or witnesses `BeaconGap` (`beacon_gap`, bounded by `ε_A1 + ctGapTerm`, or `ε_A1 + epsCt` in the `_dct` forms); conversely a designated handle is symbolically eligible only on runs with no rejected bundle call in Fresh (`PqxdhDeploymentHeadlineSymbolicLor.designated_sym`). Beacon-side symbolic eligibility covers `(S, serverKid)` pins only; ProVerif processes whose Beacons pin the honest Server identity with another key ID (the AnyPin processes) reach Beacons that CE never designates, and those Beacons never establish with the one-key-ID Server (Rust aborts them, `beacon.rs:492-496`).

### Ideal operations (plan section 11, updated)

| # | Symbolic operation | CE endpoint now |
| --- | --- | --- |
| O1 | fresh Beacon names | `create`; identity collisions are `ε_inj` (`identity_collision_game`) |
| O2 | `sign`, `verify_signature` | `bundle` and the attached verification inside `accept`; CE-A2, CE-A2pub (joint weak EUF) |
| O3 | Ed→X conversion, X25519 | inside `accept` and `finish`; no adversary DH oracle; Gap-DH inside CE-A1 |
| O4 | ML-KEM | inside `accept` and `finish`; `kemLoss_g`, `β_g`, `ε_ctcoll`; no KEM injectivity is used |
| O5 | `pqxdh_root` | the R1 slice (`hmac`); the statistical term of `slotLoss_g` (item 2) |
| O6 | initial chains | the key-schedule part of `slotLoss_g` (item 2) |
| O7 | `ratchet_next`, `ratchet_material` | the chain hops of `authLoss_g` and `recLoss_g` (item 5) |
| O8 | seal, AEAD/CTX, BLAKE2b | sends; the `hash` random oracle; the integrity and privacy losses of the record lifts (item 4) |
| O9 | open | `serverRaw`, `beaconRaw` (mode O plaintext, mode P bit); the same losses |
| O10 | fresh application name | `fresh`; CE-APP with `2^-min` |
| O11 | `choice[l, r]` | `test`; CE-LOR |
| O12 | replicated accept | `accept` with the consumed-set check |
| O13 | one-use pending token, delayed build | `build` on the same object (moved token); cross-object builds need CE-M (not built) |
| O14 | `fail_build`, `fail_seal` | the actual failure branches (occupancy, writer `none`, empty plaintext, exhaustion) |
| O15 | fixed chain disclosures | none: symbolic-only capability; inside proofs only as kernel reads |
| O16 | root release for non-selected identities | none: symbolic-only capability; simulated inside reductions |
| O17 | AnyPin creation | `create` with any pin |
| O18 | `fs_far_chain` | not imported; the general receive with at most 51 derivations |
| O19 | OD5 `fs_strong_partner` | the public counterpart of the designation |
| O20 | material services (seal, open, reveal) | the selected key against known calls inside the record lift (`PqxdhRecordLiftCtx.ctxReduction`, `PqxdhRecordLiftCtxPriv.privReduction`); no reveal operation |
| O21 | SSX full-response lookup | none as stated: CE uses designation by session handle, not raw response equality |
| O22 | Dolev-Yao deduction | local real computation; only the R1 slice and BLAKE2b are oracles |
| O23 | `ProvDhService` | none for the adversary: symbolic-only capability |
| O24 | events (L6) | the observation and the event projection above |
| O25 | quantum capabilities | no classical endpoint; the LQ-F post-run reveal is a classical analogue for passive confidentiality only, with no QPT or QROM claim |
| O26 | identity key output at allocation | only through the bundle (D2): symbolic-only capability |
| O27 | two published triples per owner | one published bundle per Beacon, as in Rust: symbolic-only capability |

### The rows

The 185 security-class lines of `verdict-classes.tsv` divide into the 18 lines of the source-scope ledger, 26 legacy fs lines and close relatives, and 141 further lines (plan section 12). The computational column, one entry per row with its theorems, conditions, bound, production form and symbolic-only remainder, is the section "Computational column: the common deployment experiment" of [the ProVerif source-scope ledger](../proverif-source-scope.md). Its statuses, by group:

| Group | Rows (VC) | Status |
| --- | --- | --- |
| Key transfer and root secrecy | A1-root 3168, S3-server 601, S3-beacon 602 | partial: CE-KT transfers any decision to the ideal game; `attacker(root)` stays symbolic-only (CE-RG not built) |
| b2s origin | L2-origin 3179, b2s-C2 633, b2s-C2-chosen-fs 634, b2s-C4 636, far-b2s-C4 3174 | computational; the root is not an observable; the Server pin and the mode-O plaintext under CE designation only; injectivity by named failure modes |
| s2b origin | S2b-origin 3183, s2b-C4 617, far-s2b-C4 3175; s2b-C1 615 | computational from position 2, except the Beacon's assigned key ID and the root; s2b-C1 partial (its position 1 is CE-A1's) |
| initial response and registration | A1-delayed 3167, S2b-initial 3184, A1 597, s2b-A1 613, b2s-A1 631, encoding-A1 649 | partial: CE-A1's matching states no root, assigned key ID, associated data or application payload |
| provenance and replay | A2-provenance 3161, A2 598, s2b-A2 614, b2s-A2 632, encoding-A2 650, R1 599, encoding-R1 651, R1' 600, encoding-R1' 652, s2b-C3 616, b2s-C3 635 | computational (publication readings on runs with no rejected bundle call in Fresh; replay with zero loss) |
| application secrecy | App-b2s 3188, b2s-S2 637, App-s2b 3189; s2b-S1 618 | computational in mode P; s2b-S1 partial (sequence-one payload and chosen-prefix taskings) |
| left-or-right secrecy | SSX-b2s 3192, SS-b2s 3155, SSX-s2b 3193, SS-s2b 3156 | computational for one test session, eligibility-weighted |
| unknown key share | b2s-UKSr 638 | partial: frame-linked, not plaintext-linked |
| passive and live | passive-classical 162-167, passive-quantum 168-173, live 127, 130, 132, 134, 135 | 162 and 168 symbolic-only; 163-166 computational; 167, 169-173 and the live rows partial |
| auxiliary | L2-identity 3180, S2b-identity 3185, A2-beacon-key 3162, A2-server-key 3163, SSX-b2s-origin 3194, SSX-s2b-origin 3195 | no endpoint |
| the remaining 124 lines | active-classical, baseline, failed-receive, compromise, general-registration, alias, kem-controller, registration-set | regression or symbolic-only evidence, as plan section 12.3 says |

SSX simulation remark (design-v2 section 12): an ineligible SSX call, which sends `left` in both worlds, corresponds to an ordinary CE send of `left`; CE-LOR's eligibility covers runs whose admitted tests all lie in the one designated session, which `SameSession` admission enforces.

## Production forms

At central `529e2c8b` every published CE-12 headline form has a production form under its frozen name (`PqxdhDeploymentProductionHeadlinesClassical`, `PqxdhDeploymentProductionHeadlinesLater`, `PqxdhDeploymentProductionHeadlines`; 129 forms). Each keeps the frozen bound word for word at codec′ and route′, moves every probability of the CE or LQ-F experiment to the classical or LQ-F source game read back through `unwrap`, keeps `Phase1ReadBack codec` and `Phase2ReadBack codec` (transported to codec′ by `Iff.rfl`) and carries `FrameReadBack` and `ReadWritable` at codec′ where the frozen form takes them; no form takes `DecoderAgreement` (at the production instance it is proved, `PqxdhBoundaryDeploymentStep.route_agreement`). `ctGapTerm_source` and `ctCollTerm_source` show that the two explicit terms are probabilities of the classical source game. The production forms of the 42 `_dct` closed forms (and of `ctgap_term_le` and `ctgap_term_billed`) are not on central: they exist as the module `PqxdhDeploymentProductionHeadlinesDct` on branch `codex/deployment-boundary-production` at `fa57acd9`, pending review and integration, and are not cited as results here. So on central the Beacon-side and mixed-side production forms keep `ctGapTerm` explicit, while every Server-side production form is fully closed. There is no production form of CE-A1's `ce_a1`, `ce_a1_billed`, `ce_a1_injective`, of CE-A2 and CE-A2pub, of the replay facts or of the AG statements about the ideal record world; they are outside the production selection (`production-headlines.md`, section "The production forms by family").

The production forms say nothing about the persistence-wrapped Server surface of the C, Go and Python bindings, about other identity indices than 0, about a varying `checks`, or about Rust beyond the reviewed transcription; every item of the ledger that is RT or E stays so.

## What is not claimed

- No root secrecy as `attacker(root)`: CE-KT is a transfer between the experiment and the ideal game, events cannot read roots, and the optional root-guess endpoint CE-RG is not built.
- No computational-soundness transfer of any ProVerif result, in either direction.
- No reveal during the run; the freshness and compromise-timing requirements are vacuous under the classical profile, not discharged for a richer one. In LQ-F only confidentiality is claimed; no authentication, origin, binding or unknown-key-share statement in that mode, and no QPT or QROM claim.
- No published-tuple provenance, registration-replay or CE-A1 claim on runs with a rejected bundle call in Fresh (bundle-writer option (b) of plan section 19).
- No Beacon-side claim for Beacons pinned to another Server key ID than `serverKid`.
- No forward secrecy against a later ML-KEM key disclosure, no post-compromise recovery and no KCI.
- No multi-object Server (CE-M), no multi-test-session left-or-right claim, no plaintext-linked unknown key share, no `INITIAL_SECRET` endpoint, no raw-byte event (events compare decoded frames), no designation-free form of the Server-pin or plaintext fields.
- The injective forms bound named failure modes; that they exhaust injectivity is argued in prose, and the key-ID uniqueness the s2b argument uses is read from `server.rs:434-451`, not proved.
- That every published record is a production `Sent` (used to read the plaintext forms as the full ProVerif plaintext claim) is checked by inspection of `PqxdhDeploymentSecrecy.ledgerImpl`, not by a Lean lemma.
- No running-time bounds; no persistence, snapshot, restoration, codec-internal, running-code or primitive-implementation claim.

## Sources, verification and corrections

The column was mapped row group by row group from the Lean source and the ProVerif queries at central, and each group's cells were checked by an independent adversarial verification against the same sources. Where the mapping and the verification differed, the Lean or ProVerif source was read again and the source decided. The corrections applied (recorded in the receipt):

1. The production composition is on central `529e2c8b` (fast-forward from `16956129`, coordination message 529); every production cell cites central. The production `_dct` forms are only on the branch tip `fa57acd9` and are marked pending integration.
2. S3-beacon and A1-root: every ProVerif Beacon of these processes pins `(ed_public(SERVER_IDENTITY_SECRET), SERVER_KEY_ID)` (`fs-registration.pvl:238`, :285, :313; `delayed-response.pvl:88`, :113); "any assigned key ID" is the Beacon's own assigned ID. CE's `(S, serverKid)` eligibility therefore loses nothing for these two rows; the pin remainder applies only to the AnyPin processes.
3. S3-server: `SymServer` quantifies over the created owners' identities only, so a Server peer that accepted the Server's own identity or any non-owner identity is ineligible and nothing is claimed for it.
4. S3-beacon: `ce_kt_beacon_sym_dct` takes `qInit` and `initBound` besides the CE-KT and CE-A1 premises; on central the production Beacon-side form keeps `ctGapTerm` explicit.
5. The event map carries its qualifier: designation implies symbolic eligibility only on runs with no rejected bundle call in Fresh (`designated_sym`); symbolic eligibility implies designation up to the gap terms on every run.
6. b2s origin: the strongest symbolic-eligibility form is `PqxdhDeploymentHeadlineInjective.ce_or_injective_b2s`, which has the binders and the bound of `ce_or_b2s_sym` on a larger event; it is listed with its production form.
7. s2b origin: the `kid` of the ProVerif s2b events is the Beacon's stored assigned key ID (`doc/proverif-fs-event-meaning.md`, `kid` row), which no CE event compares, so it is symbolic-only for S2b-origin, s2b-C1 and s2b-C4; position 1 of s2b-C1 is CE-A1's, whose matching states no root, associated data, assigned key ID or payload.
8. CE-A1 rows: the symbolic-only remainder names the assigned key ID and the application payload besides the root and the associated data; CE-A2's signing-history bound lives on the report-instrumented execution, related to the experiment at index 0 by `PqxdhDeploymentProvenance.report_game` under the two Phase read-back laws.
9. Application secrecy: the production later forms are on `laterSourceGame` through `PqxdhBoundaryDeploymentLater.unwrap`; the mixed-side forms need `shortRejects` and the forgery parameters besides CE-A1's premises; the LQ-F reveal omits only kind (a), and kind (b) is in the log.
10. Left-or-right: SS-b2s has no OD5 partner channel (only the SS-s2b process uses `fs_strong_partner`, through `fs-strong-s2b-interface.pvl` and `fs-strong-s2b-taskings.pvl`); the SSX processes release the roots of non-selected identities and fixed chains at accept time (`exact-interface-strong-b2s.pvl:35-36`, `exact-interface-strong-s2b.pvl:35-36`), symbolic-only capabilities (O15, O16).
11. The LQ-F key-transfer forms (CE-KT-L) are later-mode analogues, not counterparts of the classical rows A1-root, S3-server and S3-beacon.
12. The unknown-key-share row had no mapped cell; it was mapped from source in this stage (frame-linked CE-UKS, plaintext-linked symbolic reading).

## Checks

This stage changes documents only: no Lean file, inventory row, check script or Rust file. The documents it touches (`doc/` files) are not covered by `reviewed-inventory.txt` or `check-inventory.sh`, so no inventory recount, rehash or inventory check was needed. Every `Module.name` cited in the four documents was checked mechanically against the declarations of the Lean sources at central (receipt `name_check`); `git diff --check` is clean. No Lean check was run: every statement was read from source. Not run, by instruction: `make verify`, a full `lake build`, mutation testing and `nix-collect-garbage`.
