# Stage B9a notes: `Computational/PqxdhPhase2LocalMatching`

Module: `/tmp/bc-arc-scratch/c-work/b9a/PqxdhPhase2LocalMatching.lean`, namespace `BeaconcryptCore.Computational.PqxdhPhase2LocalMatching`. No tracked file of the worktree is edited and no state-changing git command is run.

## Checkpoint 0: reading and statement choice

Design sources read: `b-design.md` sections 2 (events, `sealed`, W2), 5 (step H_j uses "the local-owner `matching_open`, `afterOpening_success`, `plaintextBinding_bytes`, `registration_key_id_binding_abs` and `LE64_inj`"), 7 (row B9a) and 10 (spike: B9b needs `event_won`, the analogue of C's gap game, over `RawCtxSelectedAuthenticationObserver`).

Existing components used:

- Phase 2 local owner: `PqxdhBeaconPhase2Publication.localOwner candidate kernel` (pinned sender `candidate.server_binding.identity_key_id`, AD `absBytes candidate.associated_data`), `afterOpening`, `afterOpening_success`, `finish_success`, `publish_fields`.
- Raw receive provenance: `RawCtxOwnerProvenance.raw_success`, `RawCtxSourceOpen.raw_success_primitives`, `sourceRecord_spec`, `baseOpen_combined`, `RawCtxCanonicalOpening.selectedTarget`, `RawCtxKeyFreeDecoder.target`/`target_source`.
- CTX matching: `CtxAliasTarget.sameFullTupleAsSuccessfulSeal`, `AdaptiveCtxReplayDictionary.fullTuple_fields`, `RawCtxSelectedPlaintextOrigins.HistoryCorrect`/`record_payload`, observer `accepted_iff`/`won_iff`.
- Server seal: `PqxdhServerRegistrationPublication.firstContext` (plaintext `LE64 key_id ++ payload`, target `key_id`, sender `server_identity_key_id`, AD `absBytes associated_data`), `candidate_binding`; `RawCtxCanonicalSeal.sourceInput` (CTX seal input of a source seal: nonce from material, AD `⟨ad, seq, senderId⟩`, plaintext).
- Binding: extracted `pqxdh.authenticate_registration_key_id_binding` (sender must be the pinned key ID; binding must equal `candidate.key_id_binding`, which is `LE64 assigned_key_id`), `plaintextBinding_bytes`, `registration_key_id_binding_abs`, `array_eq_abs`, `LE64_inj`.

Rust grounding: `beacon.rs:461-484` (decrypt with the pinned server key ID and candidate AD; `seq != 1` rejected; binding is the first 8 plaintext bytes, authenticated against the outer assigned key ID and the pinned sender), core `pqxdh.rs:616-628` (`authenticate_registration_key_id_binding`), `server.rs:463-477` (Server seals `key_id_binding ++ payload` with target `key_id` and sender `server_identity_key_id`).

Statement choice (the design gives names only). B9b's `event_won` must show: if the Beacon accepted a tuple that differs from `sealed context` for every prior partner seal, then its selected CTX attempt has no full-tuple match among the observer's prior seals. So B9a provides, without any B4a definition:

1. `acceptedFields staged` and `sealedFields context` (the design's `Accepted` and `sealed`, as triples), and `KeyIdBound context` (plaintext starts with `LE64 targetId`), with `firstContext_bound` for every Server registration seal.
2. `matching_open` for the Phase 2 local owner: a key-free local target (`LocalTarget`: decoded frame validated against the pinned sender and candidate AD, API value carries the frame's sender and sequence), whose ordinary AEAD opening under some key gives the plaintext (`Opens`), and a correct CTX seal entry with the same full tuple, give equal plaintext, AD, sequence, sender (the pinned key ID), nonce and protected payload.
3. `accepted_of_match`: `afterOpening` success plus a full-tuple match with a correct entry that records a key-ID-bound seal context give `acceptedFields staged = sealedFields context` (and the seal has sequence one and the pinned sender).
4. The contrapositive in observer form (`fresh_of_differs`, `attempt_accepted`) for `event_won`.
5. Native provenance: every local-owner success under an interpreter whose AEAD branch is the ordinary `baseOpen` yields `LocalTarget` and `Opens` for its actual opening input (`local_opening`), also at the level of the post-root tail (`afterRoot_opening`) and the related-root consumer's tail (`consumer_opening`); `native_ordinary` shows the shared-cache interpreter `RawCtxSharedPrimitive.nativeImpl` qualifies.

## Checkpoint 1 (compiled, exit 0, 3.6 s, 4.2 GB RSS)

Part 1 (fields, Server seal bound, binding authentication, `accepted_of_plaintext`, `finish_fields`) and part 2 (`Opens`, `SealCorrect`, `target_matching`, `LocalTarget`, `matching_open`, `Records`, `accepted_of_match`, `fresh_of_differs`, `attempt_accepted`, `won_of_attempt`) compile with only `propext`, `Classical.choice`, `Quot.sound`. Note: `local` is a Lean keyword, so the local-target binder is named `delivery`. Deprecated `if_pos`/`if_neg` replaced by `split at`.

## Checkpoint 2 (compiled, exit 0)

Part 3 (native provenance: `OrdinaryOpen`, `native_ordinary`, `raw_nonempty`, `local_opening`, `afterRoot_run`, `afterRoot_opening`, `consumer_opening`) compiles. Fixes on the way: `rw` with `baseOpen_combined` backwards failed on a non-type-correct `change`, replaced by a forward `have combined … rw [← hbase] at combined`; `support_pure ▸` got a stuck `ExactMonadAttach` instance, replaced by `rw [support_pure, Set.mem_singleton_iff]`.

## Checkpoint 3 (final)

Added `afterOpening_of_binding` (converse of the binding gate), `relay_fields` (honest-relay consistency of `acceptedFields` and `sealedFields`) and `consumer_matching` (end-to-end form for the executable tail). `afterRoot_run` made public so every theorem carries a guard.

Compile command (serialized through the shared lock):

```
cd /tmp/beaconcrypt-authenticated-root-completion/beaconcrypt-core/proofs/lean && flock /tmp/bc-arc-scratch/lean.lock timeout 3600 lake env lean /tmp/bc-arc-scratch/c-work/b9a/PqxdhPhase2LocalMatching.lean
```

Result: exit 0, no errors, no warnings, no messages (all 24 `#guard_msgs` blocks match; only lake's two "local changes" notices for Hax and aeneas on stderr). Wall clock about 4 s, peak RSS about 4.2 GB. Logs: `compile-final.out` (empty), `compile-final.time`.

Counts: 678 lines; 8 definitions (`acceptedFields`, `sealedFields`, `KeyIdBound`, `Opens`, `SealCorrect`, `LocalTarget`, `Records`, `OrdinaryOpen`); 24 theorems, each with a repository-form guard. Axioms: `historyCorrect_iff`, `opens_of_targetOpen`: `[propext]`; `ctxSeal_correct`, `target_matching`, `won_of_attempt`: `[propext, Quot.sound]`; all others `[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom` or `native_decide` (grep for the standalone words is empty), no `@[simp]`, a docstring on every declaration, module docstring one paragraph per line.

Meaning check (scratch, not for the repository): `B9aMeaningCheck.lean` = module body plus four `example`s, compiled clean (`meaning.out` has only the lake notices):

1. joint satisfiability of the acceptance premises for every Server candidate and non-empty payload (a Beacon candidate with the Server's pin, key ID and AD stages the Server's sealed plaintext, `KeyIdBound` holds, and `acceptedFields = sealedFields = (key_id, payload, absBytes AD)`);
2. `KeyIdBound` is a real restriction (fails for an empty plaintext);
3. the full-tuple match premise is satisfiable whenever the target opens (the self-recording entry is correct and matches);
4. `acceptedFields` is not constant (two payloads give different accepted fields).

## Declarations and statements

- `acceptedFields staged := (staged.authenticated.candidate.assigned_key_id, staged.opened.plaintext.drop 8, absBytes staged.associatedData)`.
- `sealedFields context := (context.targetId, context.plaintext.drop 8, context.associatedData)` (the design's `sealed`).
- `KeyIdBound context := context.plaintext.take 8 = Pqxdh.LE64 context.targetId.val`.
- `firstContext_bound`: for `candidate.key_id_binding = ok binding`, the Server context `firstContext candidate (absBytes binding.bytes ++ payload)` is `KeyIdBound`, its `sealedFields` are `(candidate.key_id, payload, absBytes candidate.associated_data)`, and its sender is `candidate.server_identity_key_id`.
- `authenticated_binding`: `afterOpening candidate kernel reply = some staged →` `reply = .Some staged.opened`, `staged.authenticated.candidate = candidate`, `staged.opened.keyId = candidate.server_binding.identity_key_id`, sequence `1#u64`, `8 < length`, `plaintext.take 8 = LE64 candidate.assigned_key_id.val`, `staged.associatedData = candidate.associated_data`.
- `accepted_of_plaintext`: `afterOpening … = some staged`, `KeyIdBound context`, `staged.opened.plaintext = context.plaintext`, `absBytes candidate.associated_data = context.associatedData` `→ acceptedFields staged = sealedFields context`.
- `finish_fields`: `finish control state (some staged) = (some payload, next) → acceptedFields staged = (next.beacon.identityKeyId, payload, absBytes staged.associatedData) ∧ next.beacon.phase = .established … staged.associatedData staged.kernel`.
- `afterOpening_of_binding`: pinned sender, sequence one, `plaintext = LE64 assigned ++ payload`, `payload ≠ []` `→ afterOpening candidate kernel (.Some opened) = some ⟨⟨candidate⟩, candidate.associated_data, kernel, opened⟩`.
- `relay_fields`: Server candidate `server` with binding, `payload ≠ []`, Beacon candidate with `assigned_key_id = server.key_id` and `associated_data = server.associated_data`, opened from the pinned sender at sequence one with the Server context's plaintext `→ ∃ staged, afterOpening … = some staged ∧ acceptedFields staged = sealedFields (firstContext server …)`.
- `Opens c key target p := c.aeadOpen key.toList target.nonce.toList target.context.ad.bytes target.record.body target.record.tag = some p`.
- `SealCorrect c key entry` (one entry of `RawCtxSelectedPlaintextOrigins.HistoryCorrect`; `historyCorrect_iff`).
- `opens_of_targetOpen`: `AdaptiveCtxCanonical.targetOpen c key target expected = some p → Opens c key target p`.
- `ctxSeal_correct`: `record ∈ support (ctxSeal c key input) → SealCorrect c key ⟨input, record⟩`.
- `target_matching`: `Opens c key target p → SealCorrect c key entry → target.toLegacy.sameFullTupleAsSuccessfulSeal entry → p = entry.input.plaintext`.
- `LocalTarget decode raw candidate opened target := ∃ frame nonce slices parsed width, raw.isEmpty = false ∧ decode raw = some frame ∧ ValidFrame candidate.server_binding.identity_key_id (absBytes candidate.associated_data) frame ∧ opened.keyId = frame.sender ∧ opened.sequence = frame.sequence ∧ target = RawCtxKeyFreeDecoder.target nonce frame.sequence frame (absBytes candidate.associated_data) slices parsed width`.
- `localTarget_context`: `target.context.ad = ⟨absBytes AD, opened.sequence.val, opened.keyId.val⟩`, `opened.keyId = pinned`, and the target record encodes the frame payload.
- `matching_open` (the B9a headline): `LocalTarget … opened target → Opens c key target opened.plaintext → SealCorrect c key entry → same full tuple →` `opened.plaintext = entry.input.plaintext ∧ entry.input.context.ad = ⟨absBytes candidate.associated_data, opened.sequence.val, opened.keyId.val⟩ ∧ opened.keyId = candidate.server_binding.identity_key_id ∧ entry.input.nonce = target.nonce ∧ ∃ frame, decode raw = some frame ∧ frame.payload = entry.record.encode`.
- `Records entry context := entry.input.plaintext = context.plaintext ∧ entry.input.context.ad.bytes = context.associatedData ∧ entry.input.context.ad.sid = context.senderId.val`; `sourceInput_records`: `Records ⟨RawCtxCanonicalSeal.sourceInput input had, record⟩ input.context` and its `seq = input.sequence.val`.
- `accepted_of_match` (the B9a headline): `afterOpening candidate kernel reply = some staged`, `LocalTarget decode raw candidate staged.opened target`, `Opens c key target staged.opened.plaintext`, `SealCorrect c key entry`, same full tuple, `Records entry context`, `KeyIdBound context` `→ acceptedFields staged = sealedFields context ∧ context.senderId = candidate.server_binding.identity_key_id ∧ entry.input.context.ad.seq = 1`.
- `fresh_of_differs`: same Beacon premises, `HistoryCorrect c key history`, and `∀ entry ∈ history, ∃ context, Records entry context ∧ KeyIdBound context ∧ acceptedFields staged ≠ sealedFields context` `→ ∀ entry ∈ history, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry`.
- `attempt_accepted`: `rawDecode bytes = some target` and freshness against `history` `→ RawCtxSelectedAuthenticationObserver.accepted rawDecode ⟨bytes, some p, history⟩ = true`; `won_of_attempt`: an accepted attempt in `state.attempts` gives `won rawDecode state = true`.
- `OrdinaryOpen c impl`: the AEAD branch `.inr (.inr input)` of `impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT σ (OracleComp base))` returns `RawCtxSourceOpen.baseOpen c input` on its support. `native_ordinary`: `OrdinaryOpen c (RawCtxSharedPrimitive.nativeImpl c kdf)` for every `kdf`.
- `raw_nonempty`: a present raw-owner reply needs `raw.isEmpty = false` (any interpreter).
- `local_opening`: a present reply of `RawCtxWholeOwner.rawGame (impl ∘ₛ RawCtxSourceOpen.nativeAdapter) decode raw (localOwner candidate kernel) primitive` under `OrdinaryOpen c impl` gives an opening input with `context.raw = raw`, `context.associatedData = absBytes candidate.associated_data`, `sequence = frame.sequence`, `LocalTarget decode raw candidate opened (selectedTarget input …)` and `Opens c (sourceKey input) (selectedTarget input …) opened.plaintext`.
- `afterRoot_run`: generic-base sequencing of `PqxdhBeaconPhase2Publication.afterRoot` (initial KDF, application getter, local-owner raw receive, `afterOpening`).
- `afterRoot_opening`: for `PqxdhBeaconPhase2Publication.afterRoot` under a `TailSpec` handler whose raw branch is `impl ∘ₛ nativeAdapter` with `OrdinaryOpen c impl`: every `(some staged, final)` in the support has the application-getter provenance of `raw`, `afterOpening (clearedCandidate prepared.candidate) kernel reply = some staged`, and the `local_opening` facts for `staged.opened`.
- `consumer_opening`: the same for `PqxdhPhase2DhRootConsumer.afterRoot decode pending root` under a native tail interpreter `native` with `OrdinaryOpen c (fun q => native (.inl q))` (candidate `clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate`).
- `consumer_matching`: from the same support, `∃ raw key target, LocalTarget … ∧ Opens … ∧ ∀ entry, SealCorrect c key entry → same → ∀ context, Records entry context → KeyIdBound context → acceptedFields staged = sealedFields context`.

## How B9b is expected to use this

`event_won` (W2 case, owner = session j): the Beacon's selected CTX attempt has decoded target `selectedTarget input …` (the universal decoder of `pack (envelope …)`), which is a `LocalTarget` of the Beacon's delivery; in the real-CTX compiled world `opens_of_targetOpen` turns the challenger's present reply into `Opens c K1_j target p`, and the compile relation identifies `p` with `staged.opened.plaintext`. The observer's `Good` invariant gives `HistoryCorrect c K1_j sealsBefore`. Each observer seal entry under K1_j comes from session j's seal, whose context is logged in `snap.seals`; for entries of the form `⟨RawCtxCanonicalSeal.sourceInput sealIn had, record⟩` `sourceInput_records` gives `Records`, and `firstContext_bound` gives `KeyIdBound` for Server registration contexts. W2's `sealed context ≠ accepted` then gives `differs`, `fresh_of_differs` gives freshness, and `attempt_accepted`/`won_of_attempt` give `won`. In the W1 case (owner = Beacon) the history is empty and only `attempt_accepted` is needed. In the native game world `consumer_matching`/`consumer_opening` give the same premises directly from the executable Phase 2 tail.

## Deviations and choices (flag to the caller)

1. The design names `matching_open` and `accepted_of_match` without statements. I stated `matching_open` for a key-free `LocalTarget` plus `Opens` (ordinary AEAD opening under some key), not only for the native owner run, so that it applies both in the native game (`local_opening`, `consumer_opening`) and in B9b's compiled CTX world (`opens_of_targetOpen` on the selected challenger's reply). The key is a parameter; identifying it with K1_j (material provenance) is B9b's compile work.
2. `Accepted` and `sealed` belong to B4a. B9a uses triples `acceptedFields`/`sealedFields` with the same fields in the same order as the design's `Accepted ⟨keyId, payload, associatedData⟩` and `sealed context = ⟨targetId, plaintext.drop 8, associatedData⟩`. B4a or B9b needs a one-line bridge. `finish_fields` shows the accepted key ID is the installed `identityKeyId` and the payload is the finish output, so B4a can read `Accepted` from the finish result.
3. `accepted_of_match` takes `Records entry context` and `KeyIdBound context` as premises. They are what makes the design's "sealed context" well defined from an observer entry; B9b must discharge them from its compile invariant (helpers `sourceInput_records`, `firstContext_bound`).
4. Added beyond the design row: `afterOpening_of_binding` and `relay_fields` (completeness and honest-relay consistency; useful to B5a's `relay_not_win`/`honest_session_accepted`), `consumer_matching`, and the observer-form contrapositive `fresh_of_differs`/`attempt_accepted`/`won_of_attempt`.
5. Native results are stated for `StateT σ (OracleComp base)`, not only `ProbComp`, because B4a's handlers run over `OracleComp RootSpec`; the existing `PqxdhBeaconPhase2Publication.afterRoot_supported` is ProbComp-only, so `afterRoot_run` re-proves the sequencing generically.
6. `OrdinaryOpen` is not an assumption about libsodium: it is a checkable property of the interpreter, proved for the design's interpreter `RawCtxSharedPrimitive.nativeImpl` (`native_ordinary`). The only primitive law used is `Pqxdh.Crypto.aead_open_seal`.
7. Size 678 lines, within the 500-800 estimate.

## Integration left for the main agent (tracked files, not edited here)

Copy the module to `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/PqxdhPhase2LocalMatching.lean`, add it to `BeaconcryptCore.lean`, `check-inventory.sh` and `reviewed-inventory.txt` in the wave merge. Imports are all already built modules.

## Revision 1 (after review: `review-b9a-meaning-notes.md`, `review-b9a-hygiene-notes.md`)

Result: exit 0, no errors, no warnings, no messages (31 `#guard_msgs` blocks match), about 4.2 s, 4.2 GB peak. Counts: 966 lines; 31 theorems (each guarded), 9 definitions, 1 inductive. Axioms: `historyCorrect_iff`, `opens_of_targetOpen` `[propext]`; `ctxSeal_correct`, `target_matching`, `won_of_attempt` `[propext, Quot.sound]`; all others `[propext, Classical.choice, Quot.sound]`. The forbidden-word grep is empty; no `@[simp]`, no `private`. `B9aMeaningCheck.lean` was regenerated from the new body and compiles cleanly.

### 1. Opening-key provenance (reviewer F1 meaning / F1 hygiene / F2 meaning)

New declarations:

- `Reaches kdf state effect pending final` (inductive): `opened : Reaches kdf s (.ReceiveOpenRequested p) p s`; `resume : (response, next) ∈ support ((kdf request.request).run s) → Reaches kdf next (RawCtxOwnerOracle.resume request response) p f → Reaches kdf s (.ReceiveKdfRequested request) p f`. The receive admission reaches an opening capability through KDF replies in the support of `kdf`.
- `reaches_mono` (transfer along support inclusion of the KDF interpreter), `reaches_scope` (a reached capability keeps the admission's target sequence and context, from `RawCtxOwnerProvenance.oracle_resume_scope`), `reaches_of_supported` (a `RawCtxOwnerOracle.SupportedExecution` with a present reply opened a reached capability, with the opening reply in its support at the final state).
- `raw_reaches` (any `impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec …`): a present reply of `rawGame impl decode raw state primitive` gives `frame`, `pending`, `input`, `plaintext`, `final` with `decode raw = some frame`, `ValidFrame`, `Reaches (fun r => impl (.inl r)) primitive (RawCtxOwnerOracle.begin state.owner.kernel frame.sequence ⟨raw, frame, AD⟩) pending final`, `arguments pending = some input`, `pending.material = ok (.Some input.material)`, `input.sequence = frame.sequence`, `input.context = ⟨raw, frame, AD⟩`, `message = decrypted input plaintext`, and the opening reply in the support of `impl (.inr input)` at `final`. This is `RawCtxOwnerProvenance.raw_success` with the capability tied to the owner kernel.
- `KernelOpening c impl decode raw candidate kernel primitive opened input slices parsed width` (definition): `(∃ pending final, Reaches (fun r => impl (.inl r)) primitive (RawCtxOwnerOracle.begin kernel input.context.frame.sequence input.context) pending final ∧ arguments pending = some input ∧ pending.material = ok (.Some input.material)) ∧ input.context.raw = raw ∧ input.context.associatedData = absBytes candidate.associated_data ∧ input.sequence = input.context.frame.sequence ∧ LocalTarget decode raw candidate opened (selectedTarget input slices parsed width) ∧ Opens c (sourceKey input) (selectedTarget …) opened.plaintext`.
- `sourceKey_material`: `(RawCtxSourceOpen.sourceKey input).toList = (absMaterial input.material).1`.

Changed statements:

- `local_opening`: conclusion is now `∃ input slices parsed width, KernelOpening c impl decode raw candidate kernel primitive opened input slices parsed width` (kernel = the local owner's installed kernel, primitive = the receive's entry state).
- `afterRoot_opening`: now exports `initial : InitialRatchetKdfResponse`, `initialState`, `raw`, `application`, `received` with `(initial, initialState) ∈ support ((handler (.inr (.initial (beaconPending root).request))).run auxiliary)`, `(some raw, application) ∈ support ((handler (.inr (.application prepared.response))).run initialState)`, `received ∈ support (rawGame (impl ∘ₛ nativeAdapter) decode raw (localOwner (clearedCandidate prepared.candidate) (normalInitial (beaconPending root) initial)) application)`, `received.2 = final`, `received.1.1 = .Some staged.opened`, `afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1 = some staged`, and `KernelOpening … (normalInitial (beaconPending root) initial) application staged.opened input …`.
- `consumer_opening`: same exports for `PqxdhPhase2DhRootConsumer.afterRoot`, with the getter facts stated on `native (.inr …)` (no longer discarded) and the raw game on `(fun q => native (.inl q)) ∘ₛ nativeAdapter`.
- `consumer_matching`: exports `initial`, `initialState`, `raw`, `application`, the two getter facts, the `KernelOpening` at the installed initial kernel, and `∀ entry, SealCorrect c (sourceKey input) entry → (selectedTarget input …).toLegacy.sameFullTupleAsSuccessfulSeal entry → ∀ context, Records entry context → KeyIdBound context → acceptedFields staged = sealedFields context`. The docstring now says it does not identify the material with a Server session's key.

What B9b can now say: the key that opened the accepted record is `sourceKey input`, the key half of `pending.material`, where `pending` is the capability that the extracted receive admission `RawCtxOwnerOracle.begin (normalInitial (beaconPending root) initial) frame.sequence ctx` reaches through KDF replies of the native KDF branch, and `initial` is the reply to the Beacon's initial KDF request. Evaluating `begin` on the fresh Beacon kernel at sequence one (one KDF step on the receive chain, material from its reply) is not done here; B9b gets it from its factored receive (`RawCtxSelectedChain.receive_source`, spike `beacon_receive_factor`) applied to the exported raw-game run, or by computing `begin`/`resume` on that kernel.

### 2. Universal freshness (reviewer F3)

Added `fresh_forall` (premise `∀ entry ∈ history, ∀ context, Records entry context → KeyIdBound context → acceptedFields staged ≠ sealedFields context`, same conclusion as `fresh_of_differs`); proof follows the reviewer's scratch. `fresh_of_differs`'s docstring now states its `∀ entry, ∃ context` premise.

### 3. Docstring fixes

"actual" removed where not exported (`local_opening`, `afterRoot_opening`, module paragraph 4); `consumer_opening`/`consumer_matching` docstrings describe exactly the exported facts (no "end to end" claim); `relay_fields` names the non-empty payload (hygiene F2); module docstring paragraphs 3 and 4 rewritten to match.

### 4. Joint satisfiability (reviewer F4)

Reviewer's check `ReviewB9aMeaning.joint` in `/tmp/bc-arc-scratch/c-work/review-b9a-meaning-joint.lean` (output `review-b9a-meaning-joint.out`, axioms `[propext, Classical.choice, Quot.sound]`) shows every premise of `accepted_of_match` holding at once under the toy AEAD `PqxdhHypothesisWitness.toyCrypto`, with conclusion `(assigned_key_id, payload, AD)`; the same file has `fresh_forall` and `sealed_determined` (`Records` plus `KeyIdBound` fix `sealedFields` from the entry). Importing the toy witness into this component module would pull in `PqxdhAuthenticatedEvolvingSecrecy`, so instead the module has a generic `joint` for every `Pqxdh.Crypto`: given `payload ≠ []` and a non-empty seal body `(c.aeadSeal key nonce AD (LE64 assigned ++ payload)).1 ≠ []` (true for ChaCha20-Poly1305 on non-empty plaintexts), it exhibits `staged`, `decode`, `raw`, `target`, `entry`, `context` satisfying every premise of `accepted_of_match` and `acceptedFields staged = sealedFields context = (candidate.assigned_key_id, payload, absBytes candidate.associated_data)`. It uses only `aead_open_seal` and `aeadSeal_tag_length`.

Hygiene F4 (short names `matching_open`, `finish_fields` clash with `RawCtxSelectedPlaintextOrigins.matching_open` and `RawCtxReceiveSendFields.finish_fields` when both namespaces are open) is unchanged: the design fixes the name; B9b should use qualified names.

Size is now 966 lines, above the 500-800 estimate, because of the provenance layer (about 200 lines) and `joint`/`fresh_forall` (about 90 lines).

## Revision 2 (after `review-b9a2-notes.md`: N1-N3)

Result: exit 0, no errors, no warnings, no messages (31 `#guard_msgs` blocks match; axioms unchanged), about 4.2 s, 4.2 GB peak. Counts: 979 lines; 31 theorems (each guarded), 9 definitions, 1 inductive. Forbidden-word grep empty; no `@[simp]`, no `private`. `B9aMeaningCheck.lean` regenerated and compiles.

N1 (run's own opening). `KernelOpening` gains an argument `after : σ` (after `primitive`) and, inside its existential, the conjunct `(.Some opened.plaintext, after) ∈ support (((impl ∘ₛ RawCtxSourceOpen.nativeAdapter) (.inr input)).run final)`, where `final` is the end state of the `Reaches` path. Changed statements:

- `local_opening`: concludes `KernelOpening c impl decode raw candidate kernel primitive result.2 opened input slices parsed width` (the link is `raw_reaches`'s reply fact, kept before it is rewritten for `openInput_success`).
- `afterRoot_opening`, `consumer_opening`: the `KernelOpening` now takes `after := received.2` (with `received.2 = final` exported as before).
- `consumer_matching`: now also exports `received`, `received ∈ support (rawGame ((fun q => native (.inl q)) ∘ₛ nativeAdapter) decode raw (localOwner … (normalInitial (beaconPending root) initial)) application)`, `received.2 = final`, `received.1.1 = .Some staged.opened`, `afterOpening … received.1.2.owner.kernel received.1.1 = some staged`, and `KernelOpening … application received.2 staged.opened …`, so its `initial` is the run's initial reply; the matching implication is unchanged.
- Docstrings of `KernelOpening`, `local_opening`, `afterRoot_opening`, `consumer_opening`, `consumer_matching` and module paragraph 4 now say that the run's reply and final state come from the opening callback at `input`, whose material is that of a capability reached from the installed kernel, so the key is the material the run opened with (still not identified with a Server session's key).

N2. Module paragraph 5 now lists `Pqxdh.Crypto.aeadSeal_tag_length` (used by `joint` to build its record, and by the existing `ctxSeal`) next to `aead_open_seal` and AEAD-opening determinism.

N3. The `joint` docstring and the module sentence on `joint` now name the non-empty payload premise and say it is necessary (the binding gate needs more than eight plaintext bytes; the reviewer's `joint_empty_false` in `review-b9a2-payload.lean`).
