-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend

/-! Every actual Word owner finish contributes one Beacon installation exactly when that same public reply succeeds. Ordinary local DH translation preserves the paired completion and all terminal failures remain in the original callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {ι KemSK Auxiliary Platform E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual typed Word finish has the exact role count of its same public reply for every owner. -/
theorem finish [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (frontend : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformSecretWordOrdinary.State source Platform) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧
      added.length = (if role = .beacon ∧ present result.1.1 = true then 1 else 0) := by
  cases found : frontend.1.beacons[index]? with
  | none =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.finish, found, StateT.run, simulateQ_pure, pure_apply,
        mem_support_pure_iff] at supported
      subst result
      exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
  | some owner =>
      simp only [RegistrationNativePlatformSecretWordFrontend.handler, RegistrationNativePlatformSecretWordFrontend.finish, found, StateT.run, simulateQ_map] at supported
      rw [map_apply, support_map] at supported
      obtain ⟨localResult, actual, returned⟩ := supported
      have counted : ∃ added, messages role localResult.2.events = messages role before.events ++ added ∧
          added.length = (if role = .beacon ∧ present localResult.1.1.1 = true then 1 else 0) := by
        cases scalar : owner.scalar with
        | none =>
            exact RegistrationNativePlatformSecretWordInstallBeaconFinish.finish role setup wire none owner.view frontend.1.environment packet before localResult
              (by simpa only [scalar, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile,
                RegistrationNativeSecretWordAtomOwnerSource.routing, StateT.run] using actual)
        | some scalarValue =>
            exact RegistrationNativePlatformSecretWordInstallBeaconFinish.finish role setup wire (some scalarValue) owner.view frontend.1.environment packet before localResult
              (by simpa only [scalar, RegistrationNativePlatformSecretWordInstallBeaconComplete.compile,
                RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.simulateQ_compose, StateT.run] using actual)
      cases returned
      exact counted

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconTyped.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallBeaconTyped.finish
