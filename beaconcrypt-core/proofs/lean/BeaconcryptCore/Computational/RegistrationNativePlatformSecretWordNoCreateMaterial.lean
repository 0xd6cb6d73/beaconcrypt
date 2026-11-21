-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateOpen
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCaps
/-! The corrected material callback macros have zero private KEM births. Each bound comes from its actual common-state source language, including stateful reservations, assigned-ID finish and all failed results. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativePlatformSecretWordFrontend
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  cases query with
  | inl message =>
    simp only [RegistrationNativeSecretWordOwners.ordinary, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, ite_false]
    split <;> simp [RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  | inr query =>
    simp only [RegistrationNativeSecretWordOwners.ordinary, isQueryBoundP_query_iff]
    intro counted
    rw [ite_eq_left counted]
    exact Nat.zero_lt_one


private theorem server_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformSecretWordOpen.PublicM (Base n KemSK Platform) A) (cap : Nat)
    (bounded : ∀ before env previous, (((work.run before).run env).run previous).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) cap) (before : State source Platform) :
    ((serverOpen work).run before).IsQueryBoundP (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) cap := by
  simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact bounded before.1.server before.1.environment before.2

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedAccept : Nat) (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before : State source Platform) :
    ((accept (n := n) (KemSK := KemSK) setup checks source selectedAccept reserve packet).run before).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0 := by
  simp only [accept, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
  exact server_bound _ 0 (RegistrationNativePlatformSecretWordNoCreateOpen.accept_free
    (decide (before.1.parsedAccepts = selectedAccept)) reserve setup checks source.verify packet) _

theorem finish_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform) :
    ((finish (n := n) (KemSK := KemSK) setup wire source index packet).run before).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0 := by
  simp only [finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    apply RegistrationNativePlatformSecretWordNoCreateLocal.local_bound false _ 0
    cases own : owner.scalar with
    | none => exact RegistrationNativePlatformSecretWordNoCreateFinish.finish_bound setup wire source packet owner.view before.1.environment
    | some localScalar =>
      exact ordinary_bound setup localScalar _ 0
        (RegistrationNativePlatformSecretWordNoCreateFinish.finish_bound setup wire source packet owner.view before.1.environment)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem build_bound (handle : Nat) (application : Option (Slice U8)) (before : State source Platform) :
    ((build (n := n) (KemSK := KemSK) setup sign view failure allocation erased helper writer reservePeer handle application source).run before).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0 := by
  simp only [build, StateT.run, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformSecretWordNoCreateLocal.build_free _

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial.accept_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial.finish_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateMaterial.build_bound
