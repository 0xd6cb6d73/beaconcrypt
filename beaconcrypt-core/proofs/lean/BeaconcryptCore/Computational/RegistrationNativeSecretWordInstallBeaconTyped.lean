-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconFinish

/-! Every actual Word owner finish contributes one Beacon installation exactly when that same public reply succeeds. Ordinary local DH translation preserves the paired completion and all terminal failures remain in the original callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual typed Word finish has the exact role count of its same public reply for every owner. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (frontend : RegistrationNativeSecretWordMessage.State source) (before : RegistrationNativeSecretWordFrontendTrace.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeSecretWordMessage.State source) × RegistrationNativeSecretWordFrontendTrace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧
      added.length = (if role = .beacon ∧ present result.1.1 = true then 1 else 0) := by
  cases found : frontend.beacons[index]? with
  | none =>
      simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon,
        RegistrationNativeSecretWordOwners.finish, found, StateT.run, simulateQ_pure, pure_apply, map_pure,
        mem_support_pure_iff] at supported
      subst result
      exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
  | some owner =>
      simp only [RegistrationNativeSecretWordFrontend.handler, RegistrationNativeSecretWordFrontend.beacon,
        RegistrationNativeSecretWordOwners.finish, found, StateT.run, simulateQ_map] at supported
      rw [map_apply, map_apply, Functor.map_map, support_map] at supported
      obtain ⟨localResult, actual, returned⟩ := supported
      have counted : ∃ added, messages role localResult.2.events = messages role before.events ++ added ∧
          added.length = (if role = .beacon ∧ present localResult.1.1.1 = true then 1 else 0) := by
        cases scalar : owner.scalar with
        | none =>
            exact RegistrationNativeSecretWordInstallBeaconFinish.finish role setup none owner.view frontend.environment packet before localResult
              (by simpa only [scalar, RegistrationNativeSecretWordInstallBeaconFinish.compile,
                RegistrationNativeSecretWordAtomOwnerSource.routing, StateT.run] using actual)
        | some scalarValue =>
            exact RegistrationNativeSecretWordInstallBeaconFinish.finish role setup (some scalarValue) owner.view frontend.environment packet before localResult
              (by simpa only [scalar, RegistrationNativeSecretWordInstallBeaconFinish.compile,
                RegistrationNativeSecretWordAtomOwnerSource.routing, QueryImpl.simulateQ_compose, StateT.run] using actual)
      cases returned
      exact counted

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconTyped.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBeaconTyped.finish
