-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativeKeyPreparation

/-! The phase service's private PRK cache is the protected slice of the actual related-Extract family cache. Ordinary side evaluations remain the fixed source root and are filtered out of that private slice. The root callback below is the existing RootSpec reduction interpreted by Family.idealImpl, not an assumed replacement initializer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacBlock HmacSha512 HmacOracle RootOutput expandRoot)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)

def inside (target : Option DhOutput) (bytes : Pqxdh.Bytes) : Bool :=
  decide (RegistrationNativeRelatedFamily.Protected target bytes)

def cacheOf (target : Option DhOutput) (cache : HmacOracle.QueryCache) : HmacOracle.QueryCache :=
  QueryCache.ofFn fun bytes => if RegistrationNativeRelatedFamily.Protected target bytes then cache bytes else none

theorem cacheOf_protected (target : Option DhOutput) (cache : HmacOracle.QueryCache)
    (bytes : Pqxdh.Bytes) (protectedInput : RegistrationNativeRelatedFamily.Protected target bytes) :
    cacheOf target cache bytes = cache bytes := by
  simp only [cacheOf, QueryCache.ofFn_apply, ite_eq_left protectedInput]

theorem cacheOf_insert (target : Option DhOutput) (cache : HmacOracle.QueryCache)
    (bytes : Pqxdh.Bytes) (prk : HmacBlock) (protectedInput : RegistrationNativeRelatedFamily.Protected target bytes) :
    cacheOf target (cache.cacheQuery bytes prk) = (cacheOf target cache).cacheQuery bytes prk := by
  apply QueryCache.ext
  intro other
  by_cases same : other = bytes
  · subst other
    simp only [cacheOf_protected target _ bytes protectedInput, QueryCache.cacheQuery_self]
  · simp only [cacheOf, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ same]

theorem cacheOf_side_insert (target : Option DhOutput) (cache : HmacOracle.QueryCache)
    (bytes : Pqxdh.Bytes) (prk : HmacBlock) (side : ¬ RegistrationNativeRelatedFamily.Protected target bytes) :
    cacheOf target (cache.cacheQuery bytes prk) = cacheOf target cache := by
  apply QueryCache.ext
  intro other
  by_cases same : other = bytes
  · subst other
    simp only [cacheOf, QueryCache.ofFn_apply, ite_eq_right side]
  · simp only [cacheOf, QueryCache.ofFn_apply, QueryCache.cacheQuery_of_ne _ _ same]

/-- Actual protected root queries use the very same cached PRK after filtering unrelated source calls. -/
theorem query_project (target : Option DhOutput) (cache : HmacOracle.QueryCache)
    (bytes : Pqxdh.Bytes) (protectedInput : RegistrationNativeRelatedFamily.Protected target bytes) :
    Prod.map id (cacheOf target) <$> (HmacOracle.randomOracle bytes).run cache =
      (HmacOracle.randomOracle bytes).run (cacheOf target cache) := by
  cases cached : cache bytes with
  | none =>
    have filtered := (cacheOf_protected target cache bytes protectedInput).trans cached
    rw [LazyOracleDiscard.query_of_none cached, LazyOracleDiscard.query_of_none filtered]
    simp only [map_bind, map_pure, Prod.map, id_eq, cacheOf_insert target cache bytes _ protectedInput]
  | some prk =>
    have filtered := (cacheOf_protected target cache bytes protectedInput).trans cached
    rw [LazyOracleDiscard.query_of_some cached, LazyOracleDiscard.query_of_some filtered]
    simp only [map_pure, Prod.map, id_eq]

noncomputable def familyRoot (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) :
    StateT RegistrationNativeRelatedFamily.State ProbComp (Option RootOutput) :=
  simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar) (RegistrationNativeRelatedRoot.root message)

private theorem pure_apply {S Result : Type} (value : Result) (state : S) :
    (pure value : StateT S ProbComp Result) state = pure (value, state) := rfl

private theorem map_apply {S Input Result : Type} (f : Input → Result) (work : StateT S ProbComp Input)
    (before : S) : (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem root_cache (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (before : RegistrationNativeRelatedFamily.State) :
    Prod.map id RegistrationNativeRelatedFamily.State.cache <$> (familyRoot hmac joint dh seed scalar message).run before =
      match RegistrationNativeRelatedFamily.input joint dh seed scalar message with
      | none => pure (none, before.cache)
      | some bytes =>
          (fun result => (some (expandRoot hmac result.1), result.2)) <$>
            (RegistrationNativeRelatedFamily.protectedExtract hmac
              (joint.staticDh seed (dh.publicKey scalar)) bytes).run before.cache := by
  simp only [familyRoot, RegistrationNativeRelatedRoot.root, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  cases actual : RegistrationNativeRelatedFamily.input joint dh seed scalar message
  all_goals simp only [RegistrationNativeRelatedFamily.idealImpl, RegistrationNativeRelatedFamily.impl,
    StateT.run, actual, pure_bind, bind_map_left, simulateQ_map, simulateQ_spec_query,
    simulateQ_pure, pure_apply, map_apply, map_pure,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, expandRoot]

/-- The same private root callback used by the native phase service, before its root32 reply is erased. -/
noncomputable def root (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) : StateT HmacOracle.QueryCache ProbComp (Option RootOutput) :=
  match RegistrationNativeRelatedFamily.input joint dh seed scalar message with
  | none => pure none
  | some bytes =>
      if inside (joint.staticDh seed (dh.publicKey scalar)) bytes then
        (fun prk => some (expandRoot hmac prk)) <$> HmacOracle.randomOracle bytes
      else pure (some (RegistrationNativeRelatedRoot.nativeRoot source bytes))

/-- The actual post-G1 related-family root callback projects to the phase service's private root callback. Unrelated fixed-Extract cache entries and signing/HMAC history are discarded only by this stated analysis projection. -/
theorem root_project (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (before : RegistrationNativeRelatedFamily.State) :
    Prod.map id (fun state => cacheOf (joint.staticDh seed (dh.publicKey scalar)) state.cache) <$>
      (familyRoot hmac joint dh seed scalar message).run before =
      (root source hmac joint dh seed scalar message).run
        (cacheOf (joint.staticDh seed (dh.publicKey scalar)) before.cache) := by
  have mapped := congrArg (fun experiment =>
    Prod.map id (cacheOf (joint.staticDh seed (dh.publicKey scalar))) <$> experiment)
    (root_cache hmac joint dh seed scalar message before)
  simp only [Functor.map_map, Prod.map, id_eq] at mapped
  change (fun result : Option RootOutput × RegistrationNativeRelatedFamily.State =>
    (result.1, cacheOf (joint.staticDh seed (dh.publicKey scalar)) result.2.cache)) <$>
    (familyRoot hmac joint dh seed scalar message).run before = _
  rw [mapped]
  cases realized : RegistrationNativeRelatedFamily.input joint dh seed scalar message with
  | none => simp only [realized, root, StateT.run_pure, map_pure, Prod.map, id_eq]
  | some bytes =>
    by_cases protectedInput : RegistrationNativeRelatedFamily.Protected (joint.staticDh seed (dh.publicKey scalar)) bytes
    · have filtered := query_project (joint.staticDh seed (dh.publicKey scalar)) before.cache bytes protectedInput
      have result := congrArg (fun experiment => (fun result : HmacBlock × HmacOracle.QueryCache =>
        (some (expandRoot hmac result.1), result.2)) <$> experiment) filtered
      simpa only [realized, root, inside, protectedInput, decide_true, ite_true,
        RegistrationNativeRelatedFamily.protectedExtract, StateT.run_map, Functor.map_map, Prod.map, id_eq] using result
    · simp only [realized, root, inside, protectedInput, decide_false, Bool.false_eq_true, ite_false,
        RegistrationNativeRelatedFamily.protectedExtract, RegistrationNativeRelatedFamily.actualExtract,
        StateT.run, map_pure, Prod.map, id_eq, pure_apply, cacheOf_side_insert _ _ bytes _ protectedInput]
      rw [RegistrationNativeRelatedRoot.nativeRoot, PqxdhSecretInputKdf.sourceRootOutput_eq source hmac correct bytes]

end BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.cacheOf_protected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.cacheOf_protected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.cacheOf_insert' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.cacheOf_insert
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.cacheOf_side_insert' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.cacheOf_side_insert
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.root_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyFamilyPreparation.root_project
