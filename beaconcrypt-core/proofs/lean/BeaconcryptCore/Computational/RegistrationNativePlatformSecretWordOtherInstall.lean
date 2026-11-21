-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinaryInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishInstall
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! Every actual new typed callback except build and finish contains no role installation. The corrected incoming finish contains no Server installation, including both scalar routes and every source failure. These are literal syntactic source facts, independent of chronological monitor state and backend success. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall GlobalInstall)
open PqxdhRecordLiftInterface (Role)

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun reached => next reached.1 reached.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before, before) := rfl
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl

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


attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- No nonmaterial corrected callback can add an installation attempt of either role. -/
theorem other_free (role : Role) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 4 ∧ RegistrationNativeRawAdapter.kind query ≠ 5)
    (before : State source Platform) :
    ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) role) 0 := by
  by_cases allowed : RegistrationNativePlatformSecretWordOrdinary.Ordinary query
  · rw [RegistrationNativePlatformSecretWordFrontend.ordinary setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query allowed]
    exact RegistrationNativePlatformSecretWordOrdinaryInstall.handler_free (n := n) role setup source selectedOwner publicPrekey reserveFrame writer query before
  · cases query with
    | inl coin => exact (allowed trivial).elim
    | inr query => cases query with
      | accept packet =>
        simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.accept,
          StateT.run, bind_apply, get_apply, modify_apply, pure_bind,
          RegistrationNativePlatformSecretWordFrontend.serverOpen, isQueryBoundP_map_iff]
        exact RegistrationNativePlatformSecretWordAcceptInstall.accept_free role (decide (before.1.parsedAccepts = selectedAccept))
          reserveRegistration setup checks source.verify packet before.1.server before.1.environment before.2
      | build handle application => exact (quiet.1 rfl).elim
      | finish index packet => exact (quiet.2 rfl).elim
      | _ => exact (allowed trivial).elim

omit primitive in
private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) A)
    (free : work.IsQueryBoundP (LocalInstall (KemSK := KemSK) .server) 0) :
    (simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work).IsQueryBoundP
      (LocalInstall (KemSK := KemSK) .server) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 free
  intro query
  cases query with
  | inl message =>
    simp only [RegistrationNativeSecretWordOwners.ordinary, LocalInstall, ite_false]
    split <;> simp [LocalInstall, isQueryBoundP_query_iff]
  | inr query =>
    simp only [RegistrationNativeSecretWordOwners.ordinary, isQueryBoundP_query_iff]
    intro installed
    rw [ite_eq_left installed]
    decide

/-- Corrected mixed-roster completion installs only Beacon peers, on both actual optional scalar routes. -/
theorem finish_server_free (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform) :
    ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.finish index packet))).run before).IsQueryBoundP
      (GlobalInstall (KemSK := KemSK) .server) 0 := by
  simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    apply RegistrationNativeSecretWordAtomInstallPredicate.local_bound .server false _ 0
    cases owner.scalar with
    | none => exact RegistrationNativePlatformSecretWordFinishInstall.finish_bound setup wire source packet owner.view before.1.environment
    | some scalar =>
      exact ordinary_bound setup scalar _
        (RegistrationNativePlatformSecretWordFinishInstall.finish_bound setup wire source packet owner.view before.1.environment)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall.other_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall.other_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall.finish_server_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOtherInstall.finish_server_free
