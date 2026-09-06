import BeaconcryptCore.Computational.PqxdhPhase1AcceptanceOracle
import BeaconcryptCore.Refinement.PqxdhProtocol

/-!
# Source Phase-1 signing through the joint identity service

The extracted unsigned builder feeds the source-ordered prekey, one-time and PQ signing calls. The client holds no identity seed. Exact full-state equalities retain all earlier source, signing, converted-DH and reveal history; optional missing-handle rejection remains an actual recorded request. Native serialization, role-state publication, material generation and the common protocol composition remain separate boundaries.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting

/-- Exact source field buffers after three attached signatures. No private context is included in the returned bundle. -/
def candidate (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (preSignature oneSignature pqSignature : Ed25519Signature) : Phase1Candidate :=
  ⟨encodedIdentity identity, attachSignature preSignature (prekeyMessage keys.prekey),
    attachSignature oneSignature (oneTimeMessage keys.oneTime), attachSignature pqSignature (pqMessage keys.pqKey)⟩

/-- The native source order is prekey, one-time, PQ. An unavailable service rejects immediately without skipping the failed request. -/
def signingProgram (index : ℕ) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    OracleComp DynamicSpec (Option Phase1Candidate) := do
  let preSignature ← DynamicSpec.query (.inr (.service index (.sign (prekeyMessage keys.prekey))))
  match preSignature with
  | none => pure none
  | some preSignature =>
    let oneSignature ← DynamicSpec.query (.inr (.service index (.sign (oneTimeMessage keys.oneTime))))
    match oneSignature with
    | none => pure none
    | some oneSignature =>
      let pqSignature ← DynamicSpec.query (.inr (.service index (.sign (pqMessage keys.pqKey))))
      pure (pqSignature.map fun pqSignature => candidate identity keys preSignature oneSignature pqSignature)

/-- A signing service reads only the actual created seed inside its private interpreter and retains its complete reply in source order. -/
theorem signing_step (primitives : Primitives) (index : ℕ) (message : Pqxdh.Bytes)
    (state : SourceState) :
    (lazyImpl primitives (.inr (.service index (.sign message)))).run state =
      pure ((state.seeds[index]?).map (fun seed => primitives.sign seed message),
        record (.inr (.service index (.sign message)))
          ((state.seeds[index]?).map (fun seed => primitives.sign seed message)) state) := rfl

/-- Retain one actual signing reply, without changing any generated private seed. -/
def recordSign (primitives : Primitives) (seed : IdentitySeed) (index : ℕ)
    (message : Pqxdh.Bytes) (state : SourceState) : SourceState :=
  record (.inr (.service index (.sign message))) (some (primitives.sign seed message)) state

/-- All three source observations append in source order after the entire existing transcript. -/
def signedState (primitives : Primitives) (seed : IdentitySeed) (index : ℕ)
    (keys : Phase1KeyTuple) (state : SourceState) : SourceState :=
  recordSign primitives seed index (pqMessage keys.pqKey)
    (recordSign primitives seed index (oneTimeMessage keys.oneTime)
      (recordSign primitives seed index (prekeyMessage keys.prekey) state))

def signedCandidate (primitives : Primitives) (seed : IdentitySeed)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) : Phase1Candidate :=
  candidate identity keys (primitives.sign seed (prekeyMessage keys.prekey))
    (primitives.sign seed (oneTimeMessage keys.oneTime)) (primitives.sign seed (pqMessage keys.pqKey))

set_option backward.isDefEq.respectTransparency false in
/-- A created handle realizes the exact source three-signature result and full source poststate. The client receives no seed. -/
theorem signingProgram_created (primitives : Primitives) (index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (state : SourceState) (seed : IdentitySeed)
    (created : state.seeds[index]? = some seed) :
    (simulateQ (lazyImpl primitives) (signingProgram index identity keys)).run state =
      pure (some (signedCandidate primitives seed identity keys), signedState primitives seed index keys state) := by
  simp only [signingProgram, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    signing_step, created, Option.map_some, pure_bind]
  simp [record, recordSign, signedState, signedCandidate, created, simulateQ_map,
    StateT.run_map]
  rw [signing_step]
  simp [created, record, List.append_assoc]


set_option backward.isDefEq.respectTransparency false in
/-- An uncreated index retains the rejected prekey request and performs neither later signature call. -/
theorem signingProgram_uncreated (primitives : Primitives) (index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (state : SourceState)
    (uncreated : state.seeds[index]? = none) :
    (simulateQ (lazyImpl primitives) (signingProgram index identity keys)).run state =
      pure (none, record (.inr (.service index (.sign (prekeyMessage keys.prekey)))) none state) := by
  simp only [signingProgram, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    signing_step, uncreated, Option.map_none, pure_bind, simulateQ_pure, StateT.run_pure]

/-- The complete private created prefix survives the source signing block. -/
theorem signedState_seeds (primitives : Primitives) (seed : IdentitySeed) (index : ℕ)
    (keys : Phase1KeyTuple) (state : SourceState) :
    (signedState primitives seed index keys state).seeds = state.seeds := rfl

/-- Complete source trace equality keeps every prior request/reply before the three new observations. -/
theorem signedState_transcript (primitives : Primitives) (seed : IdentitySeed) (index : ℕ)
    (keys : Phase1KeyTuple) (state : SourceState) :
    (signedState primitives seed index keys state).transcript = state.transcript ++
      [⟨.inr (.service index (.sign (prekeyMessage keys.prekey))), some (primitives.sign seed (prekeyMessage keys.prekey))⟩,
       ⟨.inr (.service index (.sign (oneTimeMessage keys.oneTime))), some (primitives.sign seed (oneTimeMessage keys.oneTime))⟩,
       ⟨.inr (.service index (.sign (pqMessage keys.pqKey))), some (primitives.sign seed (pqMessage keys.pqKey))⟩] := by
  simp [signedState, recordSign, record, List.append_assoc]

/-- The exact signed result is substituted before an arbitrary full-state protocol continuation. This is not a marginal signature-distribution equality. -/
theorem signingProgram_continuation (primitives : Primitives) (index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (state : SourceState) (seed : IdentitySeed)
    (created : state.seeds[index]? = some seed) {Result : Type}
    (next : Option Phase1Candidate × SourceState → ProbComp Result) :
    (simulateQ (lazyImpl primitives) (signingProgram index identity keys)).run state >>= next =
      next (some (signedCandidate primitives seed identity keys), signedState primitives seed index keys state) := by
  rw [signingProgram_created primitives index identity keys state seed created, pure_bind]

/-- Source history instrumentation uses the same actual signature reply as the private source transcript. -/
def globalRecordSign (primitives : Primitives) (seed : IdentitySeed) (count index : ℕ)
    (message : Pqxdh.Bytes) (history : GlobalState count) : GlobalState count :=
  historyUpdate count (.inr (.service index (.sign message)))
    (some (primitives.sign seed message)) history

def signedGlobalState (primitives : Primitives) (seed : IdentitySeed) (count index : ℕ)
    (keys : Phase1KeyTuple) (history : GlobalState count) : GlobalState count :=
  globalRecordSign primitives seed count index (pqMessage keys.pqKey)
    (globalRecordSign primitives seed count index (oneTimeMessage keys.oneTime)
      (globalRecordSign primitives seed count index (prekeyMessage keys.prekey) history))

set_option backward.isDefEq.respectTransparency false in
/-- A created source handle has the same complete optional service reply with both source and joint histories retained. -/
theorem signing_history_step (primitives : Primitives) (count index : ℕ) (message : Pqxdh.Bytes)
    (history : GlobalState count) (state : SourceState) (seed : IdentitySeed)
    (created : state.seeds[index]? = some seed) :
    (sourceWithHistory count (lazyImpl primitives) (.inr (.service index (.sign message)))).run
      (history, state) = pure (some (primitives.sign seed message),
        (globalRecordSign primitives seed count index message history, recordSign primitives seed index message state)) := by
  rw [sourceWithHistory_run, signing_step]
  simp [created, globalRecordSign, recordSign]

set_option backward.isDefEq.respectTransparency false in
/-- Exact source signing preserves all earlier correlated-DH/signing/reveal histories, not only the selected signing log. -/
theorem signingProgram_complete (primitives : Primitives) (count index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (history : GlobalState count)
    (state : SourceState) (seed : IdentitySeed) (created : state.seeds[index]? = some seed) :
    (simulateQ (sourceWithHistory count (lazyImpl primitives))
      (signingProgram index identity keys)).run (history, state) =
      pure (some (signedCandidate primitives seed identity keys),
        (signedGlobalState primitives seed count index keys history, signedState primitives seed index keys state)) := by
  simp only [signingProgram, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    signing_history_step primitives count index _ _ state seed created, pure_bind]
  have nextCreated : (recordSign primitives seed index (prekeyMessage keys.prekey) state).seeds[index]? = some seed := created
  rw [signing_history_step primitives count index _ _ _ seed nextCreated]
  simp only [pure_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  have lastCreated : (recordSign primitives seed index (oneTimeMessage keys.oneTime)
      (recordSign primitives seed index (prekeyMessage keys.prekey) state)).seeds[index]? = some seed := created
  rw [signing_history_step primitives count index _ _ _ seed lastCreated]
  simp only [pure_bind, simulateQ_pure, StateT.run_pure]
  rfl


/-- An actual in-range generated identity appends the three signed events to its entire prior joint history; all other identity histories and every reveal are unchanged. -/
theorem signedGlobalState_exact (primitives : Primitives) (seed : IdentitySeed) {count : ℕ}
    (index : Fin count) (keys : Phase1KeyTuple) (history : GlobalState count) :
    signedGlobalState primitives seed count index.val keys history =
      { history with histories := (Function.update history.histories index
        (history.histories index ++
          [.signed (prekeyMessage keys.prekey) (primitives.sign seed (prekeyMessage keys.prekey)),
           .signed (oneTimeMessage keys.oneTime) (primitives.sign seed (oneTimeMessage keys.oneTime)),
           .signed (pqMessage keys.pqKey) (primitives.sign seed (pqMessage keys.pqKey))])) } := by
  simp [signedGlobalState, globalRecordSign, historyUpdate, index.isLt,
    PqxdhJointIdentityEvents.publicUpdate, requestEvent, List.append_assoc]

/-- The weak-EUF message history appends exactly the three source messages, retaining every earlier signing request even if other DH events preceded it. -/
theorem signedGlobalState_messages (primitives : Primitives) (seed : IdentitySeed) {count : ℕ}
    (index : Fin count) (keys : Phase1KeyTuple) (history : GlobalState count) :
    signedMessages ((signedGlobalState primitives seed count index.val keys history).histories index) =
      signedMessages (history.histories index) ++
        [prekeyMessage keys.prekey, oneTimeMessage keys.oneTime, pqMessage keys.pqKey] := by
  rw [signedGlobalState_exact]
  simp [signedMessages]

/-- Only with an actually empty prior signing-message log does the source block establish the exact three-entry log used by the strict single-bundle origin corollary. Prior DH events are still allowed. -/
theorem signedGlobalState_three_messages (primitives : Primitives) (seed : IdentitySeed) {count : ℕ}
    (index : Fin count) (keys : Phase1KeyTuple) (history : GlobalState count)
    (noPriorSign : signedMessages (history.histories index) = []) :
    signedMessages ((signedGlobalState primitives seed count index.val keys history).histories index) =
      [prekeyMessage keys.prekey, oneTimeMessage keys.oneTime, pqMessage keys.pqKey] := by
  rw [signedGlobalState_messages, noPriorSign, List.nil_append]

/-- The complete joint-history result feeds any protocol continuation without revealing the seed to the source signing program. -/
theorem signingProgram_complete_continuation (primitives : Primitives) (count index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (history : GlobalState count)
    (state : SourceState) (seed : IdentitySeed) (created : state.seeds[index]? = some seed)
    {Result : Type} (next : Option Phase1Candidate × (GlobalState count × SourceState) → ProbComp Result) :
    (simulateQ (sourceWithHistory count (lazyImpl primitives))
      (signingProgram index identity keys)).run (history, state) >>= next =
      next (some (signedCandidate primitives seed identity keys),
        (signedGlobalState primitives seed count index keys history, signedState primitives seed index keys state)) := by
  rw [signingProgram_complete primitives count index identity keys history state seed created, pure_bind]

/-- The ordinary attached-signature functional contract maps all four complete output buffers to the byte model. It supplies no authentication conclusion. -/
theorem signedCandidate_source (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (seed : IdentitySeed) (keys : Phase1KeyTuple) :
    signedCandidate primitives seed (primitives.publicKeys seed).ed25519 keys =
      ⟨Pqxdh.tagSig (c.edPub (secretOfSeed seed).toList),
        c.sign (secretOfSeed seed).toList (prekeyMessage keys.prekey),
        c.sign (secretOfSeed seed).toList (oneTimeMessage keys.oneTime),
        c.sign (secretOfSeed seed).toList (pqMessage keys.pqKey)⟩ := by
  simp [signedCandidate, candidate, encodedIdentity, wiring.edPublic, wiring.attachedSign]

/-- The block's exact submitted message widths are fixed by the production encodings; they are not hidden as free base work. -/
theorem signing_message_bytes (keys : Phase1KeyTuple) :
    (prekeyMessage keys.prekey).length + (oneTimeMessage keys.oneTime).length +
      (pqMessage keys.pqKey).length = 1253 := by simp


set_option backward.isDefEq.respectTransparency false in
/-- The source has at most three signing requests under every optional reply path, including rejection. -/
theorem signingProgram_total_bound (index : ℕ) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    (signingProgram index identity keys).IsTotalQueryBound 3 := by
  rw [signingProgram, isTotalQueryBound_query_bind_iff]
  refine ⟨by omega, fun pre => ?_⟩
  cases pre with
  | none => trivial
  | some pre =>
    rw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega, fun one => ?_⟩
    cases one with
    | none => trivial
    | some one =>
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by omega, fun _ => by trivial⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every source class except signing has zero calls; signing has cap three. The cap includes failed service attempts. -/
theorem signingProgram_class_bound (index : ℕ) (identity : Ed25519PublicKey)
    (keys : Phase1KeyTuple) (kind : Kind) :
    (signingProgram index identity keys).IsQueryBoundP (dynamicClass (IsClass kind))
      (if kind = .sign then 3 else 0) := by
  cases kind <;>
    simp only [signingProgram, isQueryBoundP_query_bind_iff, dynamicClass, IsClass] <;>
    simp only [not_true_eq_false, false_or, not_false_eq_true, true_or,
      reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, true_and] <;>
    intro pre <;> cases pre <;> simp only [isQueryBoundP_pure, isQueryBoundP_query_bind_iff,
      dynamicClass, IsClass, not_true_eq_false, false_or, not_false_eq_true, true_or,
      reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, true_and] <;>
    intro one <;> cases one <;> simp only [isQueryBoundP_pure, isQueryBoundP_query_bind_iff,
      dynamicClass, IsClass, not_true_eq_false, false_or, not_false_eq_true, true_or,
      reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceSub, true_and] <;>
    intro pq <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- Any predicate excluding this exact identity's signing calls has zero budget, including creation, seed reveal and services of other identities. -/
theorem signingProgram_excluded_bound (index : ℕ) (identity : Ed25519PublicKey)
    (keys : Phase1KeyTuple) (predicate : DynamicSpec.Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ message, ¬ predicate (.inr (.service index (.sign message)))) :
    (signingProgram index identity keys).IsQueryBoundP predicate 0 := by
  simp only [signingProgram, isQueryBoundP_query_bind_iff, excluded, not_false_eq_true,
    true_or, ↓reduceIte, true_and]
  intro pre
  cases pre with
  | none => trivial
  | some pre =>
    simp only [isQueryBoundP_query_bind_iff, excluded, not_false_eq_true, true_or, ↓reduceIte, true_and]
    intro one
    cases one with
    | none => trivial
    | some one =>
      simp only [isQueryBoundP_query_bind_iff, excluded, not_false_eq_true, true_or, ↓reduceIte, true_and]
      intro pq
      trivial


set_option backward.isDefEq.respectTransparency false in
/-- An unavailable source identity still records the failed request, with no phantom signing or reveal event in the joint family. -/
theorem signingProgram_complete_uncreated (primitives : Primitives) (count index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (history : GlobalState count)
    (state : SourceState) (uncreated : state.seeds[index]? = none) :
    (simulateQ (sourceWithHistory count (lazyImpl primitives))
      (signingProgram index identity keys)).run (history, state) =
      pure (none, (history, record (.inr (.service index (.sign (prekeyMessage keys.prekey)))) none state)) := by
  simp only [signingProgram, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    sourceWithHistory_run, signing_step, uncreated, Option.map_none, pure_bind,
    simulateQ_pure, StateT.run_pure]
  simp [historyUpdate]

/-- The interpreted signing block adds no seed generation or random draws. Its up-to-three deterministic signatures and byte processing remain separately counted local primitive work. -/
theorem signingProgram_interpreted_uniform_bound (primitives : Primitives) (count index : ℕ)
    (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) (history : GlobalState count)
    (state : SourceState) :
    ((simulateQ (sourceWithHistory count (lazyImpl primitives))
      (signingProgram index identity keys)).run (history, state)).IsTotalQueryBound 0 := by
  cases created : state.seeds[index]? with
  | none =>
    rw [signingProgram_complete_uncreated primitives count index identity keys history state created]
    trivial
  | some seed =>
    rw [signingProgram_complete primitives count index identity keys history state seed created]
    trivial

/-- Under the same functional attached-signature interface, the source consumes the native four complete buffers and retains both full histories before any protocol continuation executes. -/
theorem sourceSigning_complete (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (count index : ℕ) (keys : Phase1KeyTuple) (history : GlobalState count)
    (state : SourceState) (seed : IdentitySeed) (created : state.seeds[index]? = some seed)
    {Result : Type} (next : Option Phase1Candidate × (GlobalState count × SourceState) → ProbComp Result) :
    (simulateQ (sourceWithHistory count (lazyImpl primitives))
      (signingProgram index (primitives.publicKeys seed).ed25519 keys)).run (history, state) >>= next =
      next (some ⟨Pqxdh.tagSig (c.edPub (secretOfSeed seed).toList),
        c.sign (secretOfSeed seed).toList (prekeyMessage keys.prekey),
        c.sign (secretOfSeed seed).toList (oneTimeMessage keys.oneTime),
        c.sign (secretOfSeed seed).toList (pqMessage keys.pqKey)⟩,
        (signedGlobalState primitives seed count index keys history, signedState primitives seed index keys state)) := by
  rw [signingProgram_complete_continuation primitives count index _ keys history state seed created,
    signedCandidate_source c primitives secretOfSeed wiring seed keys]


open CoreModels Aeneas Aeneas.Std RustM beaconcrypt_core PqxdhRefinement in
/-- The actual extracted builder produces these four unsigned fields for arbitrary input arrays, without a cryptographic key-generation or validation premise. -/
theorem beacon_start_unsigned (state : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins) :
    ∃ out : pqxdh.BeaconStart, pqxdh.beacon_start state inputs coins = ok out ∧
      out.state.expected_server_binding = state.expected_server_binding ∧
      absBytes out.message.identity_key = Pqxdh.tagSig (absBytes inputs.identity_public_key) ∧
      absBytes out.message.prekey = Pqxdh.tagX Pqxdh.rolePre (absBytes inputs.prekey_public_key) ∧
      absBytes out.message.one_time_key = Pqxdh.tagX Pqxdh.roleOtk (absBytes coins.one_time_public_key) ∧
      absBytes out.message.pq_key = Pqxdh.tagPQ (absBytes inputs.pq_public_key) := by
  obtain ⟨a, ha, haabs⟩ := tag_sign_key_abs inputs.identity_public_key
  obtain ⟨pre, hpre, habsPre⟩ := tag_x25519_key_abs pqxdh.KEY_ROLE_PREKEY inputs.prekey_public_key
  obtain ⟨one, hone, habsOne⟩ := tag_x25519_key_abs pqxdh.KEY_ROLE_ONE_TIME coins.one_time_public_key
  obtain ⟨pq, hpq, habsPq⟩ := tag_mlkem768_key_abs inputs.pq_public_key
  refine ⟨_, by rw [pqxdh.beacon_start, ha, hpre, hone, hpq]; rfl, rfl, haabs, ?_, ?_, habsPq⟩
  · simpa only [absByte_role_pre] using habsPre
  · simpa only [absByte_role_otk] using habsOne

open CoreModels Aeneas Aeneas.Std RustM beaconcrypt_core PqxdhRefinement in
/-- Byte-equal input arrays connect the extracted unsigned builder to the exact joint signing block, before native serialization or role-state publication. -/
theorem sourceBuilderSigning_complete (c : Pqxdh.Crypto) (primitives : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c primitives secretOfSeed)
    (count index : ℕ) (keys : Phase1KeyTuple) (history : GlobalState count)
    (state : SourceState) (seed : IdentitySeed) (created : state.seeds[index]? = some seed)
    (fresh : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (identityBytes : absBytes inputs.identity_public_key = (primitives.publicKeys seed).ed25519.toList)
    (preBytes : absBytes inputs.prekey_public_key = keys.prekey.toList)
    (oneBytes : absBytes coins.one_time_public_key = keys.oneTime.toList)
    (pqBytes : absBytes inputs.pq_public_key = keys.pqKey.toList)
    {Result : Type} (next : Option Phase1Candidate × (GlobalState count × SourceState) → ProbComp Result) :
    ∃ out : pqxdh.BeaconStart, pqxdh.beacon_start fresh inputs coins = ok out ∧
      out.state.expected_server_binding = fresh.expected_server_binding ∧
      ((simulateQ (sourceWithHistory count (lazyImpl primitives))
        (signingProgram index (primitives.publicKeys seed).ed25519 keys)).run (history, state) >>= next) =
      next (some ⟨absBytes out.message.identity_key,
        c.sign (secretOfSeed seed).toList (absBytes out.message.prekey),
        c.sign (secretOfSeed seed).toList (absBytes out.message.one_time_key),
        c.sign (secretOfSeed seed).toList (absBytes out.message.pq_key)⟩,
        (signedGlobalState primitives seed count index keys history, signedState primitives seed index keys state)) := by
  obtain ⟨out, hbuild, hpin, hid, hpre, hone, hpq⟩ := beacon_start_unsigned fresh inputs coins
  refine ⟨out, hbuild, hpin, ?_⟩
  rw [hid, hpre, hone, hpq, identityBytes, preBytes, oneBytes, pqBytes, wiring.edPublic]
  exact sourceSigning_complete c primitives secretOfSeed wiring count index keys history state seed created next

end BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signing_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signing_step

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_created

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_uncreated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_uncreated

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedState_seeds' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedState_seeds

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedState_transcript' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedState_transcript

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signing_history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signing_history_step

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedGlobalState_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedGlobalState_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedGlobalState_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedGlobalState_messages

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedGlobalState_three_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedGlobalState_three_messages

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_complete_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_complete_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedCandidate_source' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signedCandidate_source

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signing_message_bytes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signing_message_bytes

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_total_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_total_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_class_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_excluded_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_excluded_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_complete_uncreated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_complete_uncreated

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_interpreted_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.signingProgram_interpreted_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.sourceSigning_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.sourceSigning_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.beacon_start_unsigned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.beacon_start_unsigned

/--
info: 'BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.sourceBuilderSigning_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter.sourceBuilderSigning_complete
