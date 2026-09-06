import BeaconcryptCore.Computational.AdaptiveCtxIndependent
import BeaconcryptCore.Computational.RawCtxRoleFamily

/-!
Seventeen statements embed one hidden uniform key in an adaptive family of raw nonce-AEAD interfaces. The reduction holds every other fixed key and complete local history; it forwards the selected target requests to the ordinary challenger and returns its actual optional plaintext. The full source handler and arbitrary adaptive continuation agree, retaining each per-key nonce history, successful seal log, raw-attempt count and discrepancy flag. Other keys and supplied states may coincide but are parameters independent of the target's later uniform sample.

The selected integrity hop is the explicit sum of ordinary INT-CTXT advantages over all selected raw slots. Target seals and raw attempts retain their source caps, caller uniform requests across every key are charged, and actual source/challenger key generation adds 32 byte-valued draws. Non-target AEAD calls remain local cryptographic computation bounded by their own original traffic; zero target-challenger calls do not make those computations free. This interface permits arbitrary raw bytes and actual optional replies but does not instantiate the native parser, CTX cache, changing source keys, compromise or target selection across all keys. The theorem's retained private states are not additional network observations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveRawKeyFamily
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead

abbrev LocalState := ReceiveState × Bool
abbrev OtherSpec (count : Nat) := RawCtxRoleFamily.FamilySpec AdaptiveSpec count
abbrev FamilySpec (count : Nat) := AdaptiveSpec + OtherSpec count
abbrev OtherState (count : Nat) := Fin count → LocalState
abbrev State (count : Nat) := OtherState count × LocalState

/-- Interpreting all preparation randomness preserves the entire hidden-target challenger state. -/
theorem targetUniform (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (work : ProbComp Result) (state : LocalState) :
    (simulateQ (adaptiveImpl real decode c key)
      (OracleComp.liftComp work AdaptiveSpec)).run state =
        (fun answer => (answer, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (simulateQ (adaptiveImpl real decode c key)
    (AdaptiveSpec.query (.inl (.inl coin)))).run before = _
  change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- Only the challenger receives target-key operations; all other keys and histories belong to the reduction. -/
noncomputable def reductionImpl {count : Nat} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (OtherState count) (OracleComp AdaptiveSpec)) :=
  fun query state => match query with
  | .inl target => do
      let answer ← AdaptiveSpec.query target
      pure (answer, state)
  | .inr other => do
      let result ← OracleComp.liftComp
        ((adaptiveImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state other.1)) AdaptiveSpec
      pure (result.1, Function.update state other.1 result.2)

/-- The comparison source invokes actual per-key handlers with the original dependent replies and complete state. -/
noncomputable def sourceImpl {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey) :
    QueryImpl (FamilySpec count) (StateT (State count) ProbComp) :=
  fun query state => match query with
  | .inl target => do
      let result ← (adaptiveImpl targetReal targetDecode c targetKey target).run state.2
      pure (result.1, (state.1, result.2))
  | .inr other => do
      let result ← (adaptiveImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.1 other.1)
      pure (result.1, (Function.update state.1 other.1 result.2, state.2))

/-- Full handler interpretation preserves every selected and unselected key history. -/
theorem interpretation {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey) :
    ((adaptiveImpl targetReal targetDecode c targetKey).mapStateTBase
      (reductionImpl real decode c keys)).flattenStateT =
        sourceImpl targetReal targetDecode real decode c targetKey keys := by
  funext query state
  cases query with
  | inl target =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, reductionImpl, sourceImpl,
        StateT.run, StateT.mk, bind_pure_comp, simulateQ_map, simulateQ_query, OracleQuery.input_query]
      change (fun x => (x.1.1, x.1.2, x.2)) <$>
        (((fun a => (a, state.1)) <$> ((OracleSpec.query target).cont <$> adaptiveImpl targetReal targetDecode c targetKey target)).run state.2) = _
      rw [StateT.run_map, StateT.run_map]
      simp only [Functor.map_map, StateT.run]
      rfl
  | inr other =>
      simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, reductionImpl, sourceImpl,
        StateT.run, StateT.mk, bind_pure_comp, simulateQ_map]
      change (fun x => (x.1.1, x.1.2, x.2)) <$>
        (((fun a => (a.1, Function.update state.1 other.1 a.2)) <$>
          simulateQ (adaptiveImpl targetReal targetDecode c targetKey)
            (OracleComp.liftComp ((adaptiveImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state.1 other.1)) AdaptiveSpec)).run state.2) = _
      rw [StateT.run_map, targetUniform]
      simp only [Functor.map_map, StateT.run]
      rfl

noncomputable def wrapped {count : Nat} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result)
    (others : OtherState count) : OracleComp AdaptiveSpec (Result × OtherState count) :=
  (simulateQ (reductionImpl real decode c keys) client).run others

def reassociate {count : Nat} {Result : Type}
    (result : (Result × OtherState count) × LocalState) : Result × State count :=
  (result.1.1, result.1.2, result.2)

/-- Adaptive choices and stopping preserve the complete family and target states. -/
theorem schedule_interpretation {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (state : State count) :
    (simulateQ (sourceImpl targetReal targetDecode real decode c targetKey keys) client).run state =
      reassociate <$> (simulateQ (adaptiveImpl targetReal targetDecode c targetKey)
        (wrapped real decode c keys client state.1)).run state.2 := by
  rw [wrapped, simulateQ_mapStateTBase_run_eq_map_flattenStateT, interpretation]
  simp [reassociate, Functor.map_map]

def TargetClass {count : Nat} (p : AdaptiveSpec.Domain → Prop) : (FamilySpec count).Domain → Prop
  | .inl query => p query
  | .inr _ => False

instance {count : Nat} (p : AdaptiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (TargetClass (count := count) p)
  | .inl query => inferInstanceAs (Decidable (p query))
  | .inr _ => isFalse id

/-- Internal non-target randomness makes no request from a target-only nonuniform resource class. -/
theorem lift_no_class (p : AdaptiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) {Result : Type} (work : ProbComp Result) :
    (OracleComp.liftComp work AdaptiveSpec).IsQueryBoundP p 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := AdaptiveSpec) (p := fun _ => False)
    (hpq := fun query => by simpa [SubSpec.onQuery] using noUniform query)
    (OracleComp.isQueryBoundP_false work 0)

/-- Each original target resource request is forwarded at most once; all other work stays local. -/
theorem target_step_bound {count : Nat} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (p : AdaptiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) (query : (FamilySpec count).Domain)
    (state : OtherState count) :
    ((reductionImpl real decode c keys query).run state).IsQueryBoundP p
      (if TargetClass p query then 1 else 0) := by
  cases query with
  | inl target =>
      simp only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, TargetClass]
      exact (isQueryBoundP_query_iff p target _).mpr (by intro hit; simp [hit])
  | inr other =>
      simpa only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
        TargetClass, if_false] using lift_no_class p noUniform
          ((adaptiveImpl (real other.1) (decode other.1) c (keys other.1) other.2).run (state other.1))

/-- Target resource caps survive every possible adaptive continuation. -/
theorem wrapped_target_bound {count : Nat} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (p : AdaptiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (TargetClass p) bound) (others : OtherState count) :
    (wrapped real decode c keys client others).IsQueryBoundP p bound :=
  bounded.simulateQ_run_StateT_of_step (target_step_bound real decode c keys p noUniform) others

noncomputable def uniformSource {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (others : OtherState count) :
    ProbComp (Result × State count) := do
  let targetKey ← $ᵗ CtxKey
  (simulateQ (sourceImpl targetReal targetDecode real decode c targetKey keys) client).run
    (others, initialState, false)

/-- The independent hidden target key remains entirely inside the ordinary adaptive challenger. -/
theorem uniform_interpretation {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (others : OtherState count) :
    uniformSource targetReal targetDecode real decode c keys client others =
      reassociate <$> uniformAdaptiveGame targetReal targetDecode c
        (wrapped real decode c keys client others) := by
  simp only [uniformSource, uniformAdaptiveGame, adaptiveGame, schedule_interpretation, map_bind]

/-- The selected key's complete raw opening experiment, with all other keys and their adaptive traffic retained, reduces to the ordinary attempt-indexed integrity family. -/
theorem selected_integrity_bound {count : Nat} (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (others : OtherState count)
    (rawCount : Nat) (bounded : client.IsQueryBoundP (TargetClass IsRawQuery) rawCount) :
    ENNReal.ofReal (tvDist (uniformSource true targetDecode real decode c keys client others)
      (uniformSource false targetDecode real decode c keys client others)) ≤
      ∑ index ∈ Finset.range rawCount, modifiedNonceAeadINTCTXTAdvantage c
        (indexedReduction targetDecode fallback (wrapped real decode c keys client others) index) := by
  rw [uniform_interpretation, uniform_interpretation]
  exact (ENNReal.ofReal_le_ofReal (tvDist_map_le reassociate _ _)).trans
    (uniformAdaptiveGame_distance_le_intctxt_sum targetDecode c fallback
      (wrapped real decode c keys client others) rawCount
        (wrapped_target_bound real decode c keys IsRawQuery (by intro coin; simp [IsRawQuery]) client rawCount bounded others))

def IsUniform : AdaptiveSpec.Domain → Prop
  | .inl (.inl _) => True
  | _ => False

instance : DecidablePred IsUniform
  | .inl (.inl _) => isTrue trivial
  | .inl (.inr _) | .inr _ => isFalse id

def UniformClass {count : Nat} : (FamilySpec count).Domain → Prop
  | .inl query => IsUniform query
  | .inr other => IsUniform other.2

instance {count : Nat} : DecidablePred (UniformClass (count := count))
  | .inl query => inferInstanceAs (Decidable (IsUniform query))
  | .inr other => inferInstanceAs (Decidable (IsUniform other.2))

/-- Actual deterministic AEAD operations add no uniform requests; every explicit coin query is charged. -/
theorem local_uniform_bound (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : AdaptiveSpec.Domain) (state : LocalState) :
    ((adaptiveImpl real decode c key query).run state).IsTotalQueryBound
      (if IsUniform query then 1 else 0) := by
  cases query with
  | inl primitive =>
    cases primitive with
    | inl coin =>
      change (do let answer ← unifSpec.query coin; pure (answer, state) : ProbComp _).IsTotalQueryBound 1
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => by trivial⟩
    | inr input =>
      change (do let pair ← (modifiedNonceAeadSealOracle c key input).run state.1.seals
                 pure (pair.1, ((⟨pair.2, state.1.attempts⟩ : ReceiveState), state.2)) : ProbComp _).IsTotalQueryBound 0
      rw [modifiedNonceAeadSealOracle_run]
      split <;> trivial
  | inr raw =>
      change (pure _ : ProbComp _).IsTotalQueryBound 0
      trivial

/-- Every uniform query in an interpreted probabilistic subroutine is counted. -/
theorem lift_uniform_bound {Result : Type} (work : ProbComp Result) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) :
    (OracleComp.liftComp work AdaptiveSpec).IsQueryBoundP IsUniform bound := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := AdaptiveSpec) (p := fun _ => True)
    (hpq := fun query => by simp [IsUniform, SubSpec.onQuery])
  exact (OracleComp.isQueryBoundP_true_iff work bound).mpr bounded

set_option backward.isDefEq.respectTransparency false in
/-- Caller randomness at every key contributes to the same reduction uniform budget. -/
theorem uniform_step_bound {count : Nat} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    (query : (FamilySpec count).Domain) (state : OtherState count) :
    ((reductionImpl real decode c keys query).run state).IsQueryBoundP IsUniform
      (if UniformClass query then 1 else 0) := by
  cases query with
  | inl target =>
      simpa only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, UniformClass] using
        (isQueryBoundP_query_iff IsUniform target _).mpr (by intro hit; simp [hit])
  | inr other =>
      simpa only [reductionImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, UniformClass] using
        lift_uniform_bound _ _ (local_uniform_bound (real other.1) (decode other.1) c (keys other.1) other.2 (state other.1))

/-- The full adaptive family inherits all original caller uniform requests. -/
theorem wrapped_uniform_bound {count : Nat} (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin count → CtxKey)
    {Result : Type} (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP UniformClass bound) (others : OtherState count) :
    (wrapped real decode c keys client others).IsQueryBoundP IsUniform bound :=
  bounded.simulateQ_run_StateT_of_step (uniform_step_bound real decode c keys) others

/-- The displayed uniform predicate is exactly the ordinary primitive reduction predicate. -/
theorem uniform_class_exact : IsUniform = primitiveClass IsPrimitiveUniformQuery := by
  funext query
  cases query with
  | inl primitive => cases primitive <;> rfl
  | inr raw => rfl

/-- Every constructed indexed ordinary forger retains its uniform and target-sealing caps. -/
theorem reduction_query_bounds {count : Nat} (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (others : OtherState count)
    (uniformCount sealCount index : Nat)
    (uniformBound : client.IsQueryBoundP UniformClass uniformCount)
    (sealBound : client.IsQueryBoundP (TargetClass (primitiveClass IsModifiedNonceAeadSealQuery)) sealCount) :
    (indexedReduction targetDecode fallback (wrapped real decode c keys client others) index).main.IsQueryBoundP
        IsPrimitiveUniformQuery uniformCount ∧
      (indexedReduction targetDecode fallback (wrapped real decode c keys client others) index).MakesAtMostSealQueries sealCount := by
  apply indexedReduction_query_bounds
  · simpa only [uniform_class_exact] using
      wrapped_uniform_bound real decode c keys client uniformCount uniformBound others
  · exact wrapped_target_bound real decode c keys (primitiveClass IsModifiedNonceAeadSealQuery)
      (by intro coin; simp [primitiveClass, IsModifiedNonceAeadSealQuery]) client sealCount sealBound others

set_option backward.isDefEq.respectTransparency false in
/-- The original complete source step obeys its actual uniform-request cost. -/
theorem source_uniform_step {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey)
    (query : (FamilySpec count).Domain) (state : State count) :
    ((sourceImpl targetReal targetDecode real decode c targetKey keys query).run state).IsTotalQueryBound
      (if UniformClass query then 1 else 0) := by
  cases query with
  | inl target =>
      simpa only [sourceImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, UniformClass] using
        local_uniform_bound targetReal targetDecode c targetKey target state.2
  | inr other =>
      simpa only [sourceImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, UniformClass] using
        local_uniform_bound (real other.1) (decode other.1) c (keys other.1) other.2 (state.1 other.1)

/-- The source cost is established on the source program through its full adaptive continuation. -/
theorem source_run_uniform {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (targetKey : CtxKey) (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP UniformClass bound) (state : State count) :
    ((simulateQ (sourceImpl targetReal targetDecode real decode c targetKey keys) client).run state).IsTotalQueryBound bound := by
  apply (isQueryBoundP_true_iff _ bound).mp
  apply bounded.simulateQ_run_StateT_of_step
  intro query state
  exact (isQueryBoundP_true_iff _ _).mpr
    (source_uniform_step targetReal targetDecode real decode c targetKey keys query state)

/-- The actual source additionally charges the single hidden target-key sample. -/
theorem source_uniform_bound {count : Nat} (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (keys : Fin count → CtxKey) {Result : Type}
    (client : OracleComp (FamilySpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP UniformClass bound) (others : OtherState count) :
    (uniformSource targetReal targetDecode real decode c keys client others).IsTotalQueryBound (32 + bound) := by
  unfold uniformSource
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro targetKey
  exact source_run_uniform targetReal targetDecode real decode c targetKey keys client bound bounded _

end BeaconcryptCore.Computational.AdaptiveRawKeyFamily

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.targetUniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.targetUniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.lift_no_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.lift_no_class

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.target_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.target_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.wrapped_target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.wrapped_target_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.uniform_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.uniform_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.selected_integrity_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.selected_integrity_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.local_uniform_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.local_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.lift_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.lift_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.uniform_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.uniform_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.wrapped_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.wrapped_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.uniform_class_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.uniform_class_exact

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.reduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.reduction_query_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.source_uniform_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.source_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.source_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.source_run_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyFamily.source_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyFamily.source_uniform_bound
