-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
import BeaconcryptCore.Refinement.AdapterPublicWrapperCopy

/-! The platform finish preserves the actual source byte-copy-before-install order and the assigned Beacon sender identifier. The earlier native profile used the original Server identifier for this shell; that separate profile and its existing proofs remain unchanged. The private first-record/authentication/agreement programs and all failed prefixes are retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
open RegistrationNativeBeaconFrontend
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire)
open PqxdhRecordLiftInterface (BeaconShell)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

noncomputable def install {source : RegistrationNativeMldsa.Source} (index : Nat) (owner : Owner source)
    (completed : registration.CompletedBeacon) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  match CoreModels.alloc.slice.Slice.to_vec core.U8.Insts.CoreCloneClone completed.application with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok copied => do
      let shell : BeaconShell := ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩
      let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known completed.kernel)))
      if installed then
        updatePhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice copied)))
      else abort owner *> pure (.ok none)

theorem install_exact {source : RegistrationNativeMldsa.Source} (index : Nat) (owner : Owner source)
    (completed : registration.CompletedBeacon) : install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed = (do
      let shell : BeaconShell := ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩
      let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known completed.kernel)))
      if installed then
        updatePhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
        pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))
      else abort owner *> pure (.ok none)) := by
  unfold install CoreModels.alloc.slice.Slice.to_vec
  rw [BeaconcryptCore.Refinement.AdapterPublicWrapperCopy.bytes]

noncomputable def afterAuthenticationWith {source : RegistrationNativeMldsa.Source}
    (setup : Setup base KemSK)
    (installation : (index : Nat) → (owner : Owner source) →
      registration.CompletedBeacon → M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)))
    (wire : Wire) (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let agreed ← simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon accepted)
  match agreed with
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.BeaconComplete completed) => do
    let opened ← simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin completed)
    match opened with
    | .fail error => abort owner *> pure (.fail error)
    | .div => abort owner *> pure .div
    | .ok (.Err _) => abort owner *> pure (.ok none)
    | .ok (.Ok established) => installation index owner established
  | .ok _ => abort owner *> pure (.ok none)

noncomputable def finishWith (setup : Setup base KemSK) (mldsaSource : RegistrationNativeMldsa.Source)
    (installation : (index : Nat) → (owner : Owner mldsaSource) →
    registration.CompletedBeacon → M n KemSK mldsaSource Auxiliary (RustM (Option Pqxdh.Bytes)))
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK mldsaSource Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let owners ← get
  match owners[index]? with
  | none => pure (.ok none)
  | some owner => match owner.phase with
    | .initSent pending oneTime => do
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
        updatePhase index (.aborted aborted)
        let authenticated ← simulateQ (authentication setup mldsaSource)
          (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
        match authenticated with
        | .fail error => abort owner *> pure (.fail error)
        | .div => abort owner *> pure .div
        | .ok (.Err _) => abort owner *> pure (.ok none)
        | .ok (.Ok accepted) => afterAuthenticationWith setup installation wire index owner oneTime accepted
    | _ => pure (.ok none)


noncomputable def afterAuthentication {source : RegistrationNativeMldsa.Source}
    (setup : Setup base KemSK) (wire : Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (accepted : registration.AuthenticatedResponse) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) :=
  afterAuthenticationWith setup install wire index owner oneTime accepted

noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := finishWith setup source install wire index packet

noncomputable def legacyInstall {source : RegistrationNativeMldsa.Source} (index : Nat) (owner : Owner source)
    (completed : registration.CompletedBeacon) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let shell : BeaconShell := ⟨owner.pin.binding.identity_key_id, completed.control, completed.binding.associated_data⟩
  let installed : Bool ← effect (.inr (.installBeacon owner.worldOwner shell (.known completed.kernel)))
  if installed then
    updatePhase index (.established ⟨completed.control, completed.binding, completed.application⟩)
    pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))
  else abort owner *> pure (.ok none)

theorem legacy (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    finishWith (n := n) (Auxiliary := Auxiliary) setup source legacyInstall wire index packet =
      RegistrationNativeBeaconFrontend.finish setup source wire index packet := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish.install_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish.install_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish.legacy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish.legacy
