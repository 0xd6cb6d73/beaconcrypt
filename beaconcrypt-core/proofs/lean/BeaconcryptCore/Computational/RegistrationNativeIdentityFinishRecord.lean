-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecordSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundleSource

/-! Terminal abort and successful sequence-one opening settle the same original native owner and World. Installation uses the actual completed kernel and populated binding; current owner phase updates preserve every reached signing-history field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

theorem abort_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.abort owner)
      (RegistrationNativeBeaconFrontend.abort (RegistrationNativeIdentityFrontend.restore seed owner)) :=
  related_bind setup checks representation created seeds _ _ _ _
    (RegistrationNativeIdentityCommonSource.effect_source setup checks representation created seeds _)
    (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
    (fun _ => related_pure setup checks representation created seeds ())

theorem abort_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : Owner source) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (RegistrationNativeIdentityFrontend.abort owner) :=
  keeps_bind setup checks representation created _ _
    (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
    (fun _ => keeps_pure setup checks representation created ())

theorem abort_value_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (value : Value) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.abort owner *> pure value)
      (RegistrationNativeBeaconFrontend.abort (RegistrationNativeIdentityFrontend.restore seed owner) *> pure value) := by
  simpa only [seqRight_eq_bind] using
    related_bind setup checks representation created seeds _ _ _ _ (abort_source setup checks representation created seeds owner seed)
      (abort_keeps setup checks representation created owner) (fun _ => related_pure setup checks representation created seeds value)

theorem abort_value_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : Owner source) (value : Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (RegistrationNativeIdentityFrontend.abort owner *> pure value) := by
  simpa only [seqRight_eq_bind] using keeps_bind setup checks representation created _ _
    (abort_keeps setup checks representation created owner) (fun _ => keeps_pure setup checks representation created value)

noncomputable def after (index : Nat) (owner : Owner source) : RustM RegistrationBeaconRecordExecutor.Result →
    RegistrationNativeIdentityFrontend.M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeIdentityFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeIdentityFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok established) => do
      let installed : Bool ← RegistrationNativeIdentityFrontend.effect (.inr (.installBeacon owner.worldOwner
        ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩ (.known established.kernel)))
      if installed then
        RegistrationNativeIdentityFrontend.updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
      else RegistrationNativeIdentityFrontend.abort owner *> pure (.ok none)

noncomputable def original (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) :
    RustM RegistrationBeaconRecordExecutor.Result →
      RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativeBeaconFrontend.abort owner *> pure (.fail error)
  | .div => RegistrationNativeBeaconFrontend.abort owner *> pure .div
  | .ok (.Err _) => RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)
  | .ok (.Ok established) => do
      let installed : Bool ← RegistrationNativeBeaconFrontend.effect (.inr (.installBeacon owner.worldOwner
        ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩ (.known established.kernel)))
      if installed then
        RegistrationNativeBeaconFrontend.updatePhase index (.established ⟨established.control, established.binding, established.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
      else RegistrationNativeBeaconFrontend.abort owner *> pure (.ok none)

/-- The actual consumed sequence-one kernel, populated AD and native phase are installed with precisely the original source effects. -/
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
    | Ok established =>
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

theorem after_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created (after index owner reply) := by
  cases reply with
  | fail error | div => exact abort_value_keeps setup checks representation created owner _
  | ok result => cases result with
    | Err error => exact abort_value_keeps setup checks representation created owner _
    | Ok established =>
        apply keeps_bind setup checks representation created _ _
          (RegistrationNativeIdentityCommonSource.effect_keeps setup checks representation created _)
        intro installed
        cases installed with
        | false => exact abort_value_keeps setup checks representation created owner _
        | true =>
            exact keeps_bind setup checks representation created _ _
              (RegistrationNativeIdentityBundleSource.phase_keeps setup checks representation created index _)
              (fun _ => keeps_pure setup checks representation created _)

end BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_value_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_value_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_value_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.abort_value_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.after_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.after_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinishRecord.after_keeps
