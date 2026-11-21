-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostNative
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily

/-! A finite family tracks every permitted generation ordinal on one actual corrected execution, retaining the full external platform state. Its coordinate and erasure laws use the same source primitive replies and private table. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily
open BeaconcryptCore.Refinement
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource Pool)
open RegistrationNativeMldsaGhostFamily (Family run coordinate erase)
variable {cap : Nat} (source : Source)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι}
abbrev State (cap n : Nat) (KemSK Platform : Type) :=
  RegistrationNativePlatformMldsaCountStop.State n KemSK Platform (handleSource source) × (Family cap × Pool source)

def coordinateState (index : Fin cap) (before : State source cap n KemSK Platform) : RegistrationNativePlatformMldsaGhostNative.State source n KemSK Platform :=
  (before.1, (before.2.1 index, before.2.2))

def nativeState (before : State source cap n KemSK Platform) : RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source :=
  (before.1, before.2.2)

noncomputable def callback (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State source cap n KemSK Platform) ProbComp) := fun query before =>
  (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$>
    RegistrationNativeMldsaTableProgram.evaluate source
      (run source ((RegistrationNativePlatformMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before.1)
        before.2.1) before.2.2

private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = (fun pair => (f pair.1, pair.2)) <$> work before := StateT.run_map f work before

/-- Each native family coordinate executes the literal original single-ordinal tracked callback on the same true-count private table. -/
theorem callback_coordinate (index : Fin cap) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform) :
    (fun result => (result.1, coordinateState source index result.2)) <$>
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before =
      (RegistrationNativePlatformMldsaGhostNative.callback source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run
        (coordinateState source index before) := by
  have same := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program before.2.2)
    (coordinate source index ((RegistrationNativePlatformMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before.1) before.2.1)
  simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] at same
  have arranged := congrArg (fun distribution => (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$> distribution) same
  simpa only [callback, StateT.run, Functor.map_map, coordinateState,
    RegistrationNativePlatformMldsaGhostNative.callback, RegistrationNativeMldsaTableProgram.runState,
    RegistrationNativeMldsaGhostState.track, RegistrationNativeMldsaGhostState.arrange,
    RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, map_apply] using arranged

/-- The joint finite family erases to the actual complete original native callback, without resetting any private source state. -/
theorem callback_erase (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform) :
    (fun result => (result.1, nativeState source result.2)) <$>
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before =
      (RegistrationNativePlatformMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run
        (nativeState source before) := by
  rw [RegistrationNativePlatformMldsaTableCallback.generic]
  have same := congrArg (fun program => RegistrationNativeMldsaTableProgram.evaluate source program before.2.2)
    (erase source ((RegistrationNativePlatformMldsaCountStop.handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before.1) before.2.1)
  simp only [RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, StateT.run_map] at same
  have arranged := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) same
  simpa only [callback, StateT.run, Functor.map_map, nativeState,
    RegistrationNativeMldsaTableProgram.runState, RegistrationNativeMldsaTableProgram.evaluate] using arranged

/-- All actual finite selected-row invariants are retained simultaneously by one complete native callback. -/
theorem callback_rows (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
    [primitive : AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform)
    (rows : ∀ index : Fin cap, RegistrationNativeMldsaGhostRows.Safe source index.val (before.2.1 index, before.2.2))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query).run before)) :
    ∀ index : Fin cap, RegistrationNativeMldsaGhostRows.Safe source index.val (result.2.2.1 index, result.2.2.2) := by
  intro index
  apply RegistrationNativePlatformMldsaGhostNative.rows source index.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query
    (coordinateState source index before) (rows index) (result.1, coordinateState source index result.2)
  rw [← callback_coordinate source index setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before, support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily.callback_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily.callback_coordinate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily.callback_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily.callback_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily.callback_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaGhostFamily.callback_rows
