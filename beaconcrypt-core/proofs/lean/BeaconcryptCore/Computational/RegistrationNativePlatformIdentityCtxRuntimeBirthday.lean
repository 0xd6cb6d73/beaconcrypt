-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity
/-! The original final native shared-cache event is the same collision event in the physical indexed CTX interpreter. One adaptive run pays one warm-cache birthday term; source callback resource caps are separately instantiated. -/
open OracleComp OracleSpec CoreModels ENNReal MeasureTheory ProbabilityTheory Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday
open RegistrationNativePlatformIdentityCtxMain (M Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (native Owned)
variable {n : Nat} {KemSK Platform A : Type} {source : RegistrationNativeMldsa.Source}

/-- The fixed-output cache collision is exactly VCVio's heterogeneous cache collision predicate. -/
theorem cache_collision (cache : CtxRomAuth.CtxRO.QueryCache) :
    CacheHasCollision cache ↔ PqxdhRecordFactsCollisionCache.Collision (fun _ => true) cache := by
  constructor
  · rintro ⟨left, right, first, second, different, atLeft, atRight, equal⟩
    have same : first = second := eq_of_heq equal
    subst second
    exact ⟨left, right, first, different, Or.inl rfl, atLeft, atRight⟩
  · rintro ⟨left, right, digest, different, _targeted, atLeft, atRight⟩
    exact ⟨left, right, digest, digest, different, atLeft, atRight, HEq.rfl⟩

private theorem collision_decide (cache : CtxRomAuth.CtxRO.QueryCache) :
    @decide (CacheHasCollision cache) (Classical.propDecidable _) =
      @decide (PqxdhRecordFactsCollisionCache.Collision (fun _ => true) cache) (Classical.propDecidable _) :=
  decide_eq_decide.mpr (cache_collision cache)

/-- Full source restoration uses the literal physical backend cache, without owner copies or cache resets. -/
theorem native_cache (before : Full n KemSK Platform source) :
    RegistrationNativeWorldCache.cache (native before).1 = before.2.2.1 := rfl

/-- One complete adaptive Main program has a single birthday charge on its original native final cache. -/
theorem program_bound (joint : PqxdhJointIdentity.Primitives) (work : M n KemSK Platform source A)
    (before : Full n KemSK Platform source) (future : Nat)
    (bounded : (work.run before.1).IsQueryBoundP RegistrationNativePlatformIdentityCtxBackend.IsHash future)
    (warm : RegistrationNativePlatformCtxBirthdayCache.Warm before.2.2.1) :
    𝒟[(fun result : A × Full n KemSK Platform source =>
      @decide (CacheHasCollision (RegistrationNativeWorldCache.cache (native result.2).1)) (Classical.propDecidable _)) <$>
        (interpret joint work).run before] {true} ≤
      ((future + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  have tight := RegistrationNativePlatformIdentityCtxBackend.collision_bound joint (work.run before.1) future bounded before.2 warm
  simp only [interpret, StateT.run, Functor.map_map, native_cache]
  simpa only [collision_decide, StateT.run] using tight

open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {I E : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "handler" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "callback" => RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "target" => RegistrationNativePlatformIdentityCtxTyped.target setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- The literal original typed native run has the same one-cache birthday charge, with generated ownership derived by its actual callbacks. -/
theorem typed_bound (work : OracleComp TypedSpec A) (before : Full n KemSK Platform source)
    (owned : Owned setup.joint before) (future : Nat)
    (bounded : ((simulateQ handler work).run before.1).IsQueryBoundP RegistrationNativePlatformIdentityCtxBackend.IsHash future)
    (warm : RegistrationNativePlatformCtxBirthdayCache.Warm before.2.2.1) :
    𝒟[(fun result : (A × RegistrationNativeExperiment.State n KemSK source) × Platform =>
      @decide (CacheHasCollision (RegistrationNativeWorldCache.cache result.1.2)) (Classical.propDecidable _)) <$>
        ((simulateQ callback work).run (native before).1).run (native before).2] {true} ≤
      ((future + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  have tight := program_bound setup.joint (simulateQ handler work) before future bounded warm
  have source_run := RegistrationNativePlatformIdentityCtxProgram.program_source setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer work before owned
  have packed : (simulateQ target work).run (native before) =
      (fun result : (A × RegistrationNativeExperiment.State n KemSK source) × Platform => (result.1.1, (result.1.2, result.2))) <$>
        ((simulateQ callback work).run (native before).1).run (native before).2 := by
    change (simulateQ target work).run (native before) =
      (RegistrationNativePlatformPackedState.pack (simulateQ callback work)).run (native before)
    rw [RegistrationNativePlatformPackedState.simulate_pack]
    rfl
  have observed := congrArg (fun distribution => (fun result : A × (RegistrationNativeExperiment.State n KemSK source × Platform) =>
    @decide (CacheHasCollision (RegistrationNativeWorldCache.cache result.2.1)) (Classical.propDecidable _)) <$> distribution) (source_run.trans packed)
  have same :
      (fun result : A × Full n KemSK Platform source =>
        @decide (CacheHasCollision (RegistrationNativeWorldCache.cache (native result.2).1)) (Classical.propDecidable _)) <$>
          (interpret setup.joint (simulateQ handler work)).run before =
      (fun result : (A × RegistrationNativeExperiment.State n KemSK source) × Platform =>
        @decide (CacheHasCollision (RegistrationNativeWorldCache.cache result.1.2)) (Classical.propDecidable _)) <$>
          ((simulateQ callback work).run (native before).1).run (native before).2 := by
    simpa only [Functor.map_map, Prod.map_def, id_eq] using observed
  rw [← same]
  exact tight

/-- The literal original initialized collision game pays one final shared-cache term. Startup supplies the warm cache internally; the syntactic future-hash allowance is a resource premise discharged by concrete callbacks. -/
theorem runtime_bound (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (adversary : RegistrationNativeExperiment.Public → OracleComp TypedSpec A) (previous : Platform) (future : Nat)
    (bounded : ∀ initial : RegistrationNativeExperiment.Initial n KemSK source,
      some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId) →
      ((simulateQ (RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation initial.created initial.credential keys failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer) (adversary initial.public)).run
          (RegistrationNativePlatformIdentityCtxInitial.fromInitial initial previous PqxdhDynamicIdentityPool.initialState).1).IsQueryBoundP
            RegistrationNativePlatformIdentityCtxBackend.IsHash future) :
    Pr{let collision ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame (n := n) source setup checks wire route representation keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer adversary previous ensureInit identityIndex serverKeyId)}[collision = true] ≤
      ((future + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 := by
  unfold RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.collisionGame
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun initialized reached => ?_
  cases initialized with
  | none => simp
  | some initial =>
    have tight := typed_bound setup checks wire route representation initial.created initial.credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (adversary initial.public)
      (RegistrationNativePlatformIdentityCtxInitial.fromInitial initial previous PqxdhDynamicIdentityPool.initialState)
      (RegistrationNativePlatformIdentityCtxInitial.initial_owned setup.joint initial previous PqxdhDynamicIdentityPool.initialState)
      future (bounded initial reached)
      (RegistrationNativePlatformIdentityCtxInitial.initial_warm setup ensureInit identityIndex serverKeyId initial previous PqxdhDynamicIdentityPool.initialState reached)
    have empty := RegistrationNativeScalarRun.start_empty setup source ensureInit identityIndex serverKeyId initial reached
    rw [RegistrationNativePlatformIdentityCtxInitial.initial_native initial empty previous PqxdhDynamicIdentityPool.initialState] at tight
    simpa only [RegistrationNativeWorldCache.cache, prEvent_eq_evalDist_singleton] using tight
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.cache_collision' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.cache_collision

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.native_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.native_cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.typed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.typed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.runtime_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxRuntimeBirthday.runtime_bound
