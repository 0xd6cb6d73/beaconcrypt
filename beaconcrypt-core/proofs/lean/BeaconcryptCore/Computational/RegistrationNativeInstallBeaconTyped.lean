-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconFinish

/-! Every original typed owner finish has the exact role-local installation count of its literal public reply, including missing owners, malformed responses, ordinary preparation translation and all terminal failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

/-- The actual typed finish has one own-role descriptor on public success and none on every failure. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (frontend : RegistrationNativePublicFrontend.State source) (before : RegistrationNativeG2Trace.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State)
    (supported : result ∈ support ((simulateQ RegistrationNativeG2Trace.handler
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.finish index packet))).run frontend)).run before)) :
    ∃ added, messages role result.2.events = messages role before.events ++ added ∧
      added.length = (if role = .beacon ∧ present result.1.1 = true then 1 else 0) := by
  cases found : frontend.beacons[index]? with
  | none =>
      simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
        RegistrationNativePublicOwners.finish, found, StateT.run, simulateQ_pure, pure_apply, map_pure,
        mem_support_pure_iff] at supported
      subst result
      exact ⟨[], by simp only [List.append_nil], by simp [present]⟩
  | some owner =>
      rw [RegistrationNativeTypedBeaconAllController.finish_source setup checks wire sign selectedOwner selectedAccept publicPrekey
        index packet frontend owner found] at supported
      simp only [simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨localResult, actual, returned⟩ := supported
      have counted := RegistrationNativeInstallBeaconFinish.finish role setup owner.scalar owner.view frontend.environment packet before localResult
        (by simpa only [RegistrationNativeInstallBeaconFinish.compile, RegistrationNativeInstallBeaconComplete.compile] using actual)
      cases returned
      exact counted


/-- Missing original owner indices return pure public failure before any callback. -/
theorem missing_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend : RegistrationNativePublicFrontend.State source)
    (missing : frontend.beacons[index]? = none) :
    (RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr (.finish index packet))).run frontend = pure (.ok none, frontend) := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    RegistrationNativePublicOwners.finish, missing, StateT.run, simulateQ_pure, map_pure]

end BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped.missing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallBeaconTyped.missing_source
