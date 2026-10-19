import BeaconcryptCore.Computational.AdaptiveCtxSharedTarget
import BeaconcryptCore.Computational.RawCtxRoleFamily
import BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard

/-!
Seventeen statements connect one adaptive shared-cache CTX family to the existing selected-key ordinary reductions. The source retains every per-key nonce, successful seal, public/private query history and raw-attempt counter plus one common cache. Other keys are fixed independent parameters outside the selected uniform draw; coincident values are permitted. The reduction never receives the selected key and forwards its actual optional opening replies. The selected integrity and privacy bounds reuse the existing modified nonce-AEAD INT-CTXT and IND$ endpoints with their explicit secret-prefix and commitment terms. These are selected-key hops, not an all-key CTX hybrid or a proof that evolving production keys have this distribution.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedFamily
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxSharedHash AdaptiveCtxSharedTarget

abbrev OtherSpec (count : Nat) := RawCtxRoleFamily.FamilySpec ReceiveSpec count
abbrev FamilySpec (count : Nat) := ReceiveSpec + OtherSpec count
abbrev Others (count : Nat) := Fin count → Local

structure SourceState (count : Nat) where
  selected : Local
  others : Others count
  cache : CtxRO.QueryCache

structure ReductionState (count : Nat) where
  others : Others count
  selectedPublic : List Pqxdh.Bytes

noncomputable def sourceImpl {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (SourceState count) ProbComp) := fun query state =>
  match query with
  | .inl selected => do
      let result ← (simulateQ hashImpl
        ((localImpl selectedDecode c selectedKey selected).run state.selected)).run state.cache
      pure (result.1.1, { state with selected := result.1.2, cache := result.2 })
  | .inr other => do
      let result ← (simulateQ hashImpl
        ((localImpl (decode other.1) c (keys other.1) other.2).run (state.others other.1))).run state.cache
      pure (result.1.1, { state with others := Function.update state.others other.1 result.1.2, cache := result.2 })

noncomputable def reductionImpl {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (ReductionState count) (OracleComp ReceiveSpec)) := fun query state =>
  match query with
  | .inl selected => do
      let answer ← ReceiveSpec.query selected
      pure (answer, { state with selectedPublic := nextPublic selected state.selectedPublic })
  | .inr other => do
      let result ← simulateQ forward
        ((localImpl (decode other.1) c (keys other.1) other.2).run (state.others other.1))
      pure (result.1, { state with others := Function.update state.others other.1 result.2 })

def project {count : Nat} (state : ReductionState count × CanonicalState) : SourceState count :=
  ⟨(separate (replacePublic state.2 state.1.selectedPublic)).1, state.1.others, state.2.ctx.cache⟩

noncomputable def linkedImpl {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (ReductionState count × CanonicalState) ProbComp) :=
  ((canonicalImpl selectedDecode c selectedKey).mapStateTBase (reductionImpl decode c keys)).flattenStateT

set_option backward.isDefEq.respectTransparency false in
/-- The selected branch forwards its request and updates only its original public-query history. -/
theorem linked_selected_run {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (query : ReceiveSpec.Domain) (state : ReductionState count) (selected : CanonicalState) :
    (linkedImpl selectedDecode decode c selectedKey keys (.inl query)).run (state, selected) =
      (fun result => (result.1, ({ state with selectedPublic := nextPublic query state.selectedPublic }, result.2))) <$>
        (canonicalImpl selectedDecode c selectedKey query).run selected := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (canonicalImpl selectedDecode c selectedKey)
      (do let answer ← ReceiveSpec.query query
          pure (answer, { state with selectedPublic := nextPublic query state.selectedPublic }))).run selected = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- The selected source step equals the target challenger under the complete state projection. -/
theorem selected_step {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (query : ReceiveSpec.Domain) (state : ReductionState count) (selected : CanonicalState) :
    Prod.map id project <$> (linkedImpl selectedDecode decode c selectedKey keys (.inl query)).run (state, selected) =
      (sourceImpl selectedDecode decode c selectedKey keys (.inl query)).run (project (state, selected)) := by
  rw [linked_selected_run]
  change _ = (do
    let result ← (simulateQ hashImpl ((localImpl selectedDecode c selectedKey query).run
      (project (state, selected)).selected)).run (project (state, selected)).cache
    pure (result.1.1, { project (state, selected) with selected := result.1.2, cache := result.2 }))
  rw [local_from_canonical]
  have entry : install (project (state, selected)).selected (project (state, selected)).cache =
      replacePublic selected state.selectedPublic := rfl
  rw [entry, ← public_history_step selectedDecode c selectedKey query selected state.selectedPublic]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The other-key branch runs its actual local cryptography through the selected shared hash service. -/
theorem linked_other_run {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (other : (OtherSpec count).Domain) (state : ReductionState count) (selected : CanonicalState) :
    (linkedImpl selectedDecode decode c selectedKey keys (.inr other)).run (state, selected) =
      (fun result => (result.1.1, ({ state with others := Function.update state.others other.1 result.1.2 }, result.2))) <$>
        (simulateQ (canonicalImpl selectedDecode c selectedKey) (simulateQ forward
          ((localImpl (decode other.1) c (keys other.1) other.2).run (state.others other.1)))).run selected := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (canonicalImpl selectedDecode c selectedKey)
      (do let result ← simulateQ forward ((localImpl (decode other.1) c (keys other.1) other.2).run (state.others other.1))
          pure (result.1, { state with others := Function.update state.others other.1 result.2 }))).run selected = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Each other-key source step preserves all local histories and the one common cache. -/
theorem other_step {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (other : (OtherSpec count).Domain) (state : ReductionState count) (selected : CanonicalState) :
    Prod.map id project <$> (linkedImpl selectedDecode decode c selectedKey keys (.inr other)).run (state, selected) =
      (sourceImpl selectedDecode decode c selectedKey keys (.inr other)).run (project (state, selected)) := by
  rw [linked_other_run, forward_complete]
  change _ = (do
    let result ← (simulateQ hashImpl
      ((localImpl (decode other.1) c (keys other.1) other.2).run (state.others other.1))).run selected.ctx.cache
    pure (result.1.1, { project (state, selected) with
      others := Function.update state.others other.1 result.1.2, cache := result.2 }))
  rw [← cache_schedule _ (selected.ctx.cache, selected.ctx.publicInputs)]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

/-- Each linked request preserves its reply and the complete source-state projection. -/
theorem linked_step {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    (query : (FamilySpec count).Domain) (state : ReductionState count × CanonicalState) :
    Prod.map id project <$> (linkedImpl selectedDecode decode c selectedKey keys query).run state =
      (sourceImpl selectedDecode decode c selectedKey keys query).run (project state) := by
  cases query with
  | inl selected => exact selected_step selectedDecode decode c selectedKey keys selected state.1 state.2
  | inr other => exact other_step selectedDecode decode c selectedKey keys other state.1 state.2

/-- The per-request equality extends to the entire adaptive execution and final state. -/
theorem linked_schedule {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (state : ReductionState count × CanonicalState) :
    Prod.map id project <$> (simulateQ (linkedImpl selectedDecode decode c selectedKey keys) client).run state =
      (simulateQ (sourceImpl selectedDecode decode c selectedKey keys) client).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq (linkedImpl selectedDecode decode c selectedKey keys)
    (sourceImpl selectedDecode decode c selectedKey keys) project
      (linked_step selectedDecode decode c selectedKey keys) client state

noncomputable def wrapped {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type} (client : OracleComp (FamilySpec count) Result)
    (state : ReductionState count) : OracleComp ReceiveSpec (Result × ReductionState count) :=
  (simulateQ (reductionImpl decode c keys) client).run state

def erase {count : Nat} {Result : Type} (result : (Result × ReductionState count) × CanonicalState) :
    Result × SourceState count := (result.1.1, project (result.1.2, result.2))

/-- The wrapped selected challenger interprets the complete original adaptive source schedule. -/
theorem schedule_interpretation {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (selectedKey : CtxKey) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (state : ReductionState count) (selected : CanonicalState) :
    erase <$> (simulateQ (canonicalImpl selectedDecode c selectedKey) (wrapped decode c keys client state)).run selected =
      (simulateQ (sourceImpl selectedDecode decode c selectedKey keys) client).run (project (state, selected)) := by
  rw [wrapped, simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map]
  exact linked_schedule selectedDecode decode c selectedKey keys client (state, selected)

def TargetClass {count : Nat} (p : ReceiveSpec.Domain → Prop) : (FamilySpec count).Domain → Prop
  | .inl query => p query
  | .inr _ => False

instance {count : Nat} (p : ReceiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (TargetClass (count := count) p) := fun query => by
  cases query <;> unfold TargetClass <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Only original selected requests can consume a target-only resource. -/
theorem target_step_bound {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False)
    (query : (FamilySpec count).Domain) (state : ReductionState count) :
    ((reductionImpl decode c keys query).run state).IsQueryBoundP p
      (if TargetClass p query then 1 else 0) := by
  cases query with
  | inl selected =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass]
      exact (isQueryBoundP_query_iff p selected _).mpr (by intro hit; simp [hit])
  | inr other =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass, ite_false]
      apply forward_bound
      simp only [unavailable]
      exact isQueryBoundP_false _ 0

/-- The full adaptive wrapper preserves each selected-only resource cap. -/
theorem wrapped_target_bound {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (unavailable : ForwardClass p = fun _ => False) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (TargetClass p) bound) (state : ReductionState count) :
    (wrapped decode c keys client state).IsQueryBoundP p bound :=
  bounded.simulateQ_run_StateT_of_step (target_step_bound decode c keys p unavailable) state

def TargetResource (hash : Bool) : ReceiveSpec.Domain → Prop :=
  if hash then AdaptiveCtxQueryBounds.SourceHash else AdaptiveCtxQueryBounds.SourceUniform

instance (hash : Bool) : DecidablePred (TargetResource hash) := by
  unfold TargetResource
  split <;> infer_instance

def RouteClass {count : Nat} (hash : Bool) : (FamilySpec count).Domain → Prop
  | .inl query => TargetResource hash query
  | .inr other => SourceClass hash other.2

instance {count : Nat} (hash : Bool) : DecidablePred (RouteClass (count := count) hash) :=
  fun query => by cases query <;> unfold RouteClass <;> infer_instance

/-- The hash-interface resource class matches its selected-challenger class. -/
theorem forward_resource (hash : Bool) : ForwardClass (TargetResource hash) = HashClass hash := by
  cases hash
  · exact forward_uniform_class
  · exact forward_hash_class

set_option backward.isDefEq.respectTransparency false in
/-- Each source request pays for its actual forwarded selected or other-key resource. -/
theorem route_step_bound {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (hash : Bool) (query : (FamilySpec count).Domain) (state : ReductionState count) :
    ((reductionImpl decode c keys query).run state).IsQueryBoundP (TargetResource hash)
      (if RouteClass hash query then 1 else 0) := by
  cases query with
  | inl selected =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, RouteClass]
      exact (isQueryBoundP_query_iff (TargetResource hash) selected _).mpr (by intro hit; simp [hit])
  | inr other =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, RouteClass]
      apply forward_bound
      simp only [forward_resource]
      simpa only [StateT.run] using
        local_step_bound hash (decode other.1) c (keys other.1) other.2 (state.others other.1)

/-- The routed resource cap is preserved through every possible adaptive continuation. -/
theorem wrapped_route_bound {count : Nat} (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (hash : Bool) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (RouteClass hash) bound) (state : ReductionState count) :
    (wrapped decode c keys client state).IsQueryBoundP (TargetResource hash) bound :=
  bounded.simulateQ_run_StateT_of_step (route_step_bound decode c keys hash) state

def initialLocal : Local := (separate canonicalInitial).1

def initialReduction (count : Nat) : ReductionState count := ⟨fun _ => initialLocal, []⟩

def initialSource (count : Nat) : SourceState count := ⟨initialLocal, fun _ => initialLocal, ∅⟩

/-- Empty local histories and one empty cache reconstruct the exact initial source state. -/
theorem initial_projection (count : Nat) : project (initialReduction count, canonicalInitial) = initialSource count := rfl

noncomputable def sourceGame {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) : ProbComp (Result × SourceState count) := do
  let selectedKey ← $ᵗ CtxKey
  (simulateQ (sourceImpl selectedDecode decode c selectedKey keys) client).run (initialSource count)

/-- The source key draw followed by the full execution equals the canonical challenger interpretation. -/
theorem uniform_interpretation {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) :
    sourceGame selectedDecode decode c keys client = (do
      let selectedKey ← $ᵗ CtxKey
      erase <$> canonicalGame selectedDecode c selectedKey
        (wrapped decode c keys client (initialReduction count))) := by
  simp only [sourceGame, canonicalGame, schedule_interpretation, initial_projection]

noncomputable def decisionClient {count : Nat} (decode : Fin count → RawDecoder)
    (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) (client : OracleComp (FamilySpec count) Bool) :
    OracleComp ReceiveSpec Bool := Prod.fst <$> wrapped decode c keys client (initialReduction count)

/-- The original Boolean source decision is the existing canonical selected-key experiment. -/
theorem source_view_eq {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (client : OracleComp (FamilySpec count) Bool) :
    Prod.fst <$> sourceGame selectedDecode decode c keys client =
      AdaptiveCtxPrivacyGuard.canonicalView selectedDecode c (decisionClient decode c keys client) := by
  rw [uniform_interpretation]
  simp only [AdaptiveCtxPrivacyGuard.canonicalView, AdaptiveCtxPrefixValidation.retainedCanonicalGame,
    decisionClient, canonicalGame, simulateQ_map, StateT.run_map,
    map_bind, Functor.map_map, bind_pure_comp, erase]

open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The actual selected shared-cache integrity hop uses the explicit ordinary reduction family and losses. -/
theorem selected_integrity_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (FamilySpec count) Bool)
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass AdaptiveCtxQueryBounds.SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass AdaptiveCtxReceive.IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((Prod.fst <$> sourceGame selectedDecode decode c keys client).boolDistAdvantage
      (AdaptiveCtxPrivacyGuard.replayView selectedDecode c (decisionClient decode c keys client))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient decode c keys client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
          (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient decode c keys client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) := by
  rw [source_view_eq]
  apply AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound selectedDecode c fallback
    (decisionClient decode c keys client) qHash qSeal qRaw
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_route_bound decode c keys true client qHash hashBound (initialReduction count))
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_target_bound decode c keys _ forward_seal_class client qSeal sealBound (initialReduction count))
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_target_bound decode c keys _ forward_raw_class client qRaw rawBound (initialReduction count))
  · exact small

/-- The selected privacy hop adds the ordinary ciphertext-view IND$ reduction to the integrity losses. -/
theorem selected_privacy_bound {count : Nat} (selectedDecode : RawDecoder)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (FamilySpec count) Bool)
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (RouteClass true) qHash)
    (sealBound : client.IsQueryBoundP (TargetClass AdaptiveCtxQueryBounds.SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass AdaptiveCtxReceive.IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((Prod.fst <$> sourceGame selectedDecode decode c keys client).boolDistAdvantage
      (AdaptiveCtxPrivacyGuard.randomView selectedDecode (decisionClient decode c keys client))) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction selectedDecode c (decisionClient decode c keys client) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder selectedDecode) fallback
          (AdaptiveCtxReceive.wrapped selectedDecode (decisionClient decode c keys client)) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrivacyGuard.viewReduction selectedDecode (decisionClient decode c keys client))) := by
  rw [source_view_eq]
  apply AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound selectedDecode c fallback
    (decisionClient decode c keys client) qHash qSeal qRaw
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_route_bound decode c keys true client qHash hashBound (initialReduction count))
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_target_bound decode c keys _ forward_seal_class client qSeal sealBound (initialReduction count))
  · exact (isQueryBoundP_map_iff _ _ _).mpr
      (wrapped_target_bound decode c keys _ forward_raw_class client qRaw rawBound (initialReduction count))
  · exact small

end BeaconcryptCore.Computational.AdaptiveCtxSharedFamily

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_selected_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_selected_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.selected_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_other_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_other_run

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.other_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.other_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.linked_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.target_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.target_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.wrapped_target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.wrapped_target_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.forward_resource' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.forward_resource

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.route_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.route_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.wrapped_route_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.wrapped_route_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.initial_projection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.initial_projection

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.uniform_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.uniform_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.source_view_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.source_view_eq

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.selected_integrity_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.selected_integrity_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.selected_privacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedFamily.selected_privacy_bound
