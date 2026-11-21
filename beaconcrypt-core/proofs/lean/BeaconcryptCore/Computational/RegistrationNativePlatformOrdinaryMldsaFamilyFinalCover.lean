-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyCover

/-! The finite actual native protected-origin cover charges every earlier cache collision to the literal final shared cache. No cache-extension or event-coverage premise is assumed: both follow from actual native callbacks and the derived reached source invariant. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyFinalCover
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformOrdinaryMldsaGhostFamily (State callback nativeState coordinateState)
open RegistrationNativePlatformOrdinaryMldsaFamilyCover (Safe observe bad collision counter cost marked)
open RegistrationNativeMldsaEuf (Forgery)
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (fallback : Credential source)

omit primitive in
private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

private theorem table_cache (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativePlatformOrdinaryMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : RegistrationNativePlatformOrdinaryMldsaTableStop.Safe source credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativePlatformOrdinaryMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  exact RegistrationNativePlatformOrdinaryMldsaTableStop.cache source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer fallback query before result safe supported

private theorem family_cache (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform) (safe : Safe source credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  apply table_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback query (nativeState source before)
    ⟨safe.1.safe, safe.2.1, safe.1.provenance⟩ (result.1, nativeState source result.2)
  rw [← RegistrationNativePlatformOrdinaryMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

private theorem collision_flag (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
    (initial : Safe source credential fallback before.native)
    (already : before.collision = true → collision source before.native)
    (result : V × RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
    (supported : result ∈ support ((simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before)) :
    Safe source credential fallback result.2.native ∧ (result.2.collision = true → collision source result.2.native) := by
  classical
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨initial, already⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, marked, RegistrationNativeMldsaFiniteMonitor.handler,
        StateT.run, mem_support_bind_iff, support_map] at supported
      obtain ⟨middle, ⟨raw, reached, same⟩, continued⟩ := supported
      cases same
      have safeAfter := RegistrationNativePlatformOrdinaryMldsaFamilyCover.step_safe source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback
        query before.native raw initial reached
      have extended := family_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback
        query before.native initial raw reached
      apply ih raw.1 _ safeAfter _ continued
      intro active
      change before.collision || decide (collision source raw.2) = true at active
      rcases Bool.or_eq_true_iff.mp active with old | fresh
      · obtain ⟨first, second, left, right, distinct, firstAt, secondAt, equal⟩ := already old
        exact ⟨first, second, left, right, distinct, extended firstAt, extended secondAt, equal⟩
      · exact of_decide_eq_true fresh

/-- Erasing all family monitors and generation metadata retains the original actual complete typed source run and its full private table. -/
theorem native_erase (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery) :
    (fun result => (result.1, nativeState source result.2.native)) <$>
      (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run before =
      (simulateQ (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run
        (nativeState source before.native) := by
  have familyErase := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (callback (cap := cap) (n := n) source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (nativeState source)
    (fun query current => RegistrationNativePlatformOrdinaryMldsaGhostFamily.callback_erase source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current)
    work before.native
  have flagsErase := congrArg (fun distribution => Prod.map id (nativeState source) <$> distribution)
    (RegistrationNativeMldsaFiniteMonitor.erase
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) (bad source credential) (collision source) (observe source) work before)
  simp only [Functor.map_map, Prod.map, id_eq] at flagsErase familyErase
  exact flagsErase.trans familyErase

/-- Actual protected native bad cuts are bounded by the literal final shared-cache collision event of the original source execution and the finite family of actual dynamic candidate monitors. -/
theorem bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK Platform)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.bad = true] ≤
      Pr{let result ← (simulateQ (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run (nativeState source before)}[
        CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformOrdinaryMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
        (RegistrationNativePlatformOrdinaryMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have covered := RegistrationNativePlatformOrdinaryMldsaFamilyCover.bound source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback
    work remaining bounded before initial room
  have collisionBound :
      Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.collision = true] ≤
        Pr{let result ← (simulateQ (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run (nativeState source before)}[
          CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] := by
    have erasure := native_erase source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work
      ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
    change (fun result => (result.1, nativeState source result.2.native)) <$>
      (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery) =
      (simulateQ (RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work).run
        (nativeState source before) at erasure
    rw [← erasure, prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun result supported active =>
      (collision_flag source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback work
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
        initial (by intro impossible; cases impossible) result supported).2 active
  exact covered.trans (add_le_add collisionBound le_rfl)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyFinalCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyFinalCover.native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyFinalCover.native_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyFinalCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaFamilyFinalCover.bound
