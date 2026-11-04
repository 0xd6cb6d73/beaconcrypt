-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource

/-! Corrected assigned-ID Beacon installation under opaque generated Ed credentials. The actual source copy precedes the same native install capability; every abort, kernel, binding, application and current-owner history is retained. This additive controller does not equate the older Server-ID shell with the corrected runtime. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

open RegistrationNativeIdentityFinishRecord (abort_value_source abort_value_keeps)

noncomputable def install (index : Nat) (owner : Owner source)
    (completed : registration.CompletedBeacon) :
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  match CoreModels.alloc.slice.Slice.to_vec core.U8.Insts.CoreCloneClone completed.application with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok copied => do
    let installed : Bool ← RegistrationNativeIdentityFrontend.effect (.inr (.installBeacon owner.worldOwner
      ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ (.known completed.kernel)))
    if installed then
      RegistrationNativeIdentityFrontend.updatePhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
      pure (.ok (some (TranscriptAuthParts.absSlice copied)))
    else RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)

theorem install_exact (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed = (do
      let installed : Bool ← RegistrationNativeIdentityFrontend.effect (.inr (.installBeacon owner.worldOwner
        ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ (.known completed.kernel)))
      if installed then
        RegistrationNativeIdentityFrontend.updatePhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))
      else RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)) := by
  unfold install CoreModels.alloc.slice.Slice.to_vec
  rw [BeaconcryptCore.Refinement.AdapterPublicWrapperCopy.bytes]

/-- Both source controllers copy before installing the actual assigned sender identifier and the actual consumed first-record kernel. -/
theorem install_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (owner : Owner source) (seed : IdentitySeed) (completed : registration.CompletedBeacon) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (install index owner completed)
      (RegistrationNativePlatformBeaconFinish.install index (RegistrationNativeIdentityFrontend.restore seed owner) completed) := by
  rw [install_exact, RegistrationNativePlatformBeaconFinish.install_exact]
  apply related_bind setup checks representation created seeds _ _ _ _
    (RegistrationNativeIdentityCommonSource.effect_source setup checks representation created seeds _)
    (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
  intro installed
  cases installed with
  | false => exact abort_value_source setup checks representation created seeds owner seed _
  | true =>
    exact related_bind setup checks representation created seeds _ _ _ _
      (RegistrationNativeIdentityBundleSource.phase_source setup checks representation created seeds index _)
      (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index _)
      (fun _ => related_pure setup checks representation created seeds _)

theorem install_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (install index owner completed) := by
  rw [install_exact]
  apply keeps_bind setup checks representation created _ _
    (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
  intro installed
  cases installed with
  | false => exact abort_value_keeps setup checks representation created owner _
  | true =>
    exact keeps_bind setup checks representation created _ _
      (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index _)
      (fun _ => keeps_pure setup checks representation created _)

noncomputable def after (index : Nat) (owner : Owner source) : RustM RegistrationBeaconRecordExecutor.Result →
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeIdentityFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeIdentityFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok established) => install index owner established

noncomputable def original (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) :
    RustM RegistrationBeaconRecordExecutor.Result →
      RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok established) => RegistrationNativePlatformBeaconFinish.install index owner established

theorem after_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (index : Nat) (owner : Owner source) (seed : IdentitySeed) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (after index owner reply) (original index (RegistrationNativeIdentityFrontend.restore seed owner) reply) := by
  cases reply with
  | fail error | div => exact abort_value_source setup checks representation created seeds owner seed _
  | ok result => cases result with
    | Err error => exact abort_value_source setup checks representation created seeds owner seed _
    | Ok established => exact install_source setup checks representation created seeds index owner seed established

theorem after_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (after index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value_keeps setup checks representation created owner _
  | ok result => cases result with
    | Err error => exact abort_value_keeps setup checks representation created owner _
    | Ok established => exact install_keeps setup checks representation created index owner established

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.install_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.install_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.install_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.install_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.install_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.install_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.after_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.after_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRecord.after_keeps
