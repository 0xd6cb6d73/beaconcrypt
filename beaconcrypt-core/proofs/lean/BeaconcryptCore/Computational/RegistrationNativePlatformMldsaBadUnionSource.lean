-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadSource
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaUnionCover

/-! The original actual source union of a protected unsigned-origin failure and final shared-cache collision has one collision charge. The marker and final cache are transported jointly through the finite analysis instrument. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadUnionSource
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaGhostFamily (State nativeState coordinateState)
open RegistrationNativePlatformMldsaFamilyCover (Safe cost counter marked)
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

/-- The original marker and its own final shared cache are covered jointly, with one collision charge. -/
theorem bound (fallback : Credential source) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (remaining : Nat)
    (bounded : work.IsQueryBoundP cost remaining) (before : State source cap n KemSK Platform)
    (initial : Safe source credential fallback before) (room : counter source before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaBadSource.handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before, false)}[
      result.2.2 = true ∨ CacheHasCollision result.2.1.1.1.server.world.world.1.primitive.2] ≤
      Pr{let result ← (simulateQ (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work).run (nativeState source before)}[
        CacheHasCollision result.2.1.1.server.world.world.1.primitive.2] +
      ∑ index : Fin cap, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor
        (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
        (RegistrationNativePlatformMldsaGhostNative.observe source)) work).run (coordinateState source index before, none)}[
          result.2.2.isSome = true] := by
  have same := RegistrationNativePlatformMldsaBadSource.program source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer work
    ({ native := before } : RegistrationNativeMldsaFiniteMonitor.State (State source cap n KemSK Platform) (Fin cap) Forgery)
  simp only [RegistrationNativePlatformMldsaBadSource.project] at same
  rw [← same, prEvent_map]
  exact RegistrationNativePlatformMldsaUnionCover.bound source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback
    work remaining bounded before initial room

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadUnionSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadUnionSource.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBadUnionSource.bound
