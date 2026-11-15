-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaFamilyFinalCover
import BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteFinal

/-! The finite actual native protected-origin cover charges every earlier cache collision to the literal final shared cache. The union of final collision and protected-origin failure pays the collision charge once. Cache extension and event coverage follow from actual callbacks and the reached source invariant. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionCover
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaGhostFamily (State callback nativeState coordinateState)
open RegistrationNativePlatformMldsaFamilyCover (Safe observe bad collision counter cost marked step_safe step_count monitor_coordinate coordinateMonitor)
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
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
variable (fallback : Credential source)

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
    source credential fallback before.2 safe.server query before.1.1 before.1.2 inner reached

private theorem family_cache (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform) (safe : Safe source credential fallback before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  apply table_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback query (nativeState source before)
    ⟨safe.1.safe, safe.2.1, safe.1.provenance⟩ (result.1, nativeState source result.2)
  rw [← RegistrationNativePlatformMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

/-- One original native bad-cut marker is covered by its same-run collision marker plus the finite family of actual dynamic single-ordinal candidate monitors. The union includes the literal final collision without a second charge. The creation cap is independent of generation success and private draw counts. -/
theorem bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK Platform)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)}[result.2.bad = true ∨ collision source result.2.native] ≤
    Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before)}[CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have cover := RegistrationNativeMldsaFiniteFinal.bound
    (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) (bad source credential) (collision source) (observe source)
    (Safe source credential fallback) (counter source) cost cap
    (step_safe source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback)
    (step_count source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback)
    (fun query first result safe supported collided => by
      have extended := family_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback query first safe result supported
      obtain ⟨one, two, left, right, distinct, firstAt, secondAt, equal⟩ := collided
      exact ⟨one, two, left, right, distinct, extended firstAt, extended secondAt, equal⟩)
    (fun query first result safe room supported badEvent => RegistrationNativePlatformMldsaBadCut.cover source setup checks wire route representation
      created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback query first result
        ⟨safe.1.safe, safe.2.1, safe.1.provenance⟩ safe.2.2 room supported badEvent)
    work remaining bounded before initial room
  have coordinates : (∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) (observe source index)) work).run (before, none)}[
        result.2.2.isSome = true]) =
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
    apply Finset.sum_congr rfl
    intro index _member
    have same := monitor_coordinate source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer index work (before, none)
    simp only [coordinateMonitor] at same
    rw [← same, prEvent_map]
    rfl
  have collisionEqual :
      Pr{let result ← ((simulateQ (marked source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run
        ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery))}[collision source result.2.native] =
      Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before)}[CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] := by
    rw [← RegistrationNativePlatformMldsaFamilyFinalCover.native_erase source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer work
      ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery), prEvent_map]
    rfl
  dsimp only [marked] at collisionEqual
  rw [coordinates, collisionEqual] at cover
  exact cover

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionCover.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionCover.bound
