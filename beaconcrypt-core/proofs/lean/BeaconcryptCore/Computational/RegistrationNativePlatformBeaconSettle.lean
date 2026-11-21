-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService
/-! Corrected assigned-ID installation and terminal phase are the literal native continuation, including abort on every failed opening or insertion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle
open RegistrationNativeBeaconFrontend
variable {n : Nat} {KemSK Auxiliary : Type} {source : RegistrationNativeMldsa.Source}

def settle (index : Nat) (owner : Owner source) :
    RustM RegistrationNativePairedBeaconService.Result → M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.Err _) => abort owner *> pure (.ok none)
  | .ok (.Ok completed) => do
      updatePhase index (.established completed)
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))

noncomputable def native (index : Nat) (owner : Owner source) :
    RustM RegistrationBeaconRecordExecutor.Result → M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.Err _) => abort owner *> pure (.ok none)
  | .ok (.Ok completed) => RegistrationNativePlatformBeaconFinish.install index owner completed

theorem installed (index : Nat) (owner : Owner source) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    native (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner result = (do
      let completed ← RegistrationNativePlatformPairedBeaconService.after effect owner.worldOwner
        (fun value => .known value.kernel) result
      settle index owner completed) := by
  cases result with
  | fail error | div => simp only [native, RegistrationNativePlatformPairedBeaconService.after, pure_bind, settle]
  | ok result => cases result with
    | Err aborted => simp only [native, RegistrationNativePlatformPairedBeaconService.after, pure_bind, settle]
    | Ok completed =>
        rw [native, RegistrationNativePlatformBeaconFinish.install_exact]
        simp only [RegistrationNativePlatformPairedBeaconService.after, bind_assoc, pure_bind]
        apply bind_congr
        intro installed
        cases installed <;> rfl

variable {ι : Type} {base : OracleSpec ι}
theorem after_authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) :
    RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary)
      setup wire index owner oneTime accepted = (do
        let agreed ← simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
        match agreed with
        | .fail error => abort owner *> pure (.fail error)
        | .div => abort owner *> pure .div
        | .ok (.BeaconComplete completed) => do
            let opened ← simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
            let installed ← RegistrationNativePlatformPairedBeaconService.after effect owner.worldOwner
              (fun value => .known value.kernel) opened
            settle index owner installed
        | .ok _ => abort owner *> pure (.ok none)) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div => rfl
  | ok result =>
      cases result <;> try rfl
      apply bind_congr
      intro opened
      change native index owner opened = _
      exact installed index owner opened

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle.installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle.installed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle.after_authentication

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconSettle
