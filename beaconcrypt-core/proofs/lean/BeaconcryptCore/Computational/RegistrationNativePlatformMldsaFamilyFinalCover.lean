-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyCover

/-! The finite actual native protected-origin cover charges every earlier cache collision to the literal final shared cache. No cache-extension or event-coverage premise is assumed: both follow from actual native callbacks and the derived reached source invariant. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaGhostFamily (State callback nativeState coordinateState)
open RegistrationNativePlatformMldsaFamilyCover (Safe observe bad collision counter cost marked)
open RegistrationNativeMldsaEuf (Forgery)
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK Platform E V : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (fallback : Credential source)

omit primitive in
private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

private theorem table_cache (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : RegistrationNativePlatformMldsaTableStop.Safe source credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (supported : result ∈ support ((RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  simp only [RegistrationNativePlatformMldsaTableCallback.callback, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact RegistrationNativePlatformHandlerCache.table setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer
    source credential fallback before.2 safe.server query before.1.1 before.1.2 safe.owners inner reached

private theorem family_cache (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform) (safe : Safe source credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  apply table_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback query (nativeState source before)
    ⟨safe.1.safe, safe.2.1, safe.1.provenance⟩ (result.1, nativeState source result.2)
  rw [← RegistrationNativePlatformMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

private theorem collision_flag (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
    (initial : Safe source credential fallback before.native)
    (already : before.collision = true → collision source before.native)
    (result : V × RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
    (supported : result ∈ support ((simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run before)) :
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
      have safeAfter := RegistrationNativePlatformMldsaFamilyCover.step_safe source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback
        query before.native raw initial reached
      have extended := family_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback
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
      (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run before =
      (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run
        (nativeState source before.native) := by
  have familyErase := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (callback (cap := cap) (n := n) source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
    (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
    (nativeState source)
    (fun query current => RegistrationNativePlatformMldsaGhostFamily.callback_erase source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query current)
    work before.native
  have flagsErase := congrArg (fun distribution => Prod.map id (nativeState source) <$> distribution)
    (RegistrationNativeMldsaFiniteMonitor.erase
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) (bad source credential) (collision source) (observe source) work before)
  simp only [Functor.map_map, Prod.map, id_eq] at flagsErase familyErase
  exact flagsErase.trans familyErase

/-- Actual protected native bad cuts are bounded by the literal final shared-cache collision event of the original source execution and the finite family of actual dynamic candidate monitors. -/
theorem bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK Platform)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.bad = true] ≤
      Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before)}[
        CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have covered := RegistrationNativePlatformMldsaFamilyCover.bound source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback
    work remaining bounded before initial room
  have collisionBound :
      Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.collision = true] ≤
        Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before)}[
          CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] := by
    have erasure := native_erase source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer work
      ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
    change (fun result => (result.1, nativeState source result.2.native)) <$>
      (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery) =
      (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run
        (nativeState source before) at erasure
    rw [← erasure, prEvent_map]
    exact prEvent_mono_of_support _ _ _ fun result supported active =>
      (collision_flag source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback work
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
        initial (by intro impossible; cases impossible) result supported).2 active
  exact covered.trans (add_le_add collisionBound le_rfl)

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover.native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover.native_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover.bound
