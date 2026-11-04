-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedBeaconService
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
/-! The corrected Beacon continuation uses the actual completed assigned identifier. The same stateful primitive and World callbacks serve known outputs and private hidden slots; selected seed chains occur only in the private service. No earlier profile equality is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService
open PqxdhRecordLiftInterface
open RegistrationNativePairedChoice (Choice PrivateChoice publicChoice)
open RegistrationNativePairedBeaconService (Result)
variable {n : Nat} {m : Type → Type} [Monad m]

def after (effects : QueryImpl (EnvEffects n) m) (owner : Nat)
    (kernel : registration.CompletedBeacon → KernelRef n) :
    RustM RegistrationBeaconRecordExecutor.Result → m (RustM Result)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err aborted) => pure (.ok (.Err aborted))
  | .ok (.Ok completed) => do
      let installed : Bool ← effects (.inr (.installBeacon owner
        ⟨completed.binding.assigned_key_id, completed.control, completed.binding.associated_data⟩ (kernel completed)))
      pure (if installed then .ok (.Ok ⟨completed.control, completed.binding, completed.application⟩)
        else .ok (.Err ⟨completed.binding.assigned_key_id⟩))

noncomputable def knownStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) : m (RustM Result) := do
  let result ← simulateQ raw (RegistrationNativePairedBeaconService.program source descriptor output)
  after effects owner (fun completed => .known completed.kernel) result

noncomputable def hiddenStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) : m (RustM Result) := do
  let result ← simulateQ raw (RegistrationNativePairedBeaconService.program source descriptor output)
  after effects owner (fun _ => .hidden slot) result

noncomputable def publicHidden (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : RegistrationNativePairedDemand.Reference n) : m (RustM Result) :=
  hiddenStage source raw effects owner reference.slot descriptor
    (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBeaconSeed.fixedSeed)

theorem after_replace (effects : QueryImpl (EnvEffects n) m) (owner : Nat) (slot : Slot n)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    after effects owner (fun _ => .hidden slot) (RegistrationBeaconSeed.replace kernel result) =
      after effects owner (fun _ => .hidden slot) result := by
  cases result with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

variable [LawfulMonad m]

theorem stage_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    hiddenStage source raw effects owner slot descriptor (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      publicHidden source raw effects owner descriptor ⟨slot, material⟩ := by
  unfold hiddenStage publicHidden
  rw [RegistrationNativePairedBeaconService.program_split]
  simp only [simulateQ_map, bind_map_left]
  apply bind_congr
  intro result
  exact after_replace effects owner slot _ result

noncomputable def privateBranch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    PrivateChoice n → m (RustM Result)
  | .known output => knownStage source raw effects owner descriptor output
  | .hidden slot output => hiddenStage source raw effects owner slot descriptor output

noncomputable def publicBranch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    Choice n → m (RustM Result)
  | .known output => knownStage source raw effects owner descriptor output
  | .hidden reference => publicHidden source raw effects owner descriptor reference

theorem branch_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (choice : PrivateChoice n) :
    publicBranch source raw effects owner descriptor (publicChoice choice) =
      privateBranch source raw effects owner descriptor choice := by
  cases choice with
  | known output => rfl
  | hidden slot output =>
      have same := stage_split source raw effects owner slot descriptor
        (PqxdhDeploymentHiddenLayout.splitOutput output).1 (PqxdhDeploymentHiddenLayout.splitOutput output).2
      simpa only [PqxdhDeploymentHiddenLayout.join_split, publicBranch, privateBranch, publicChoice] using same.symm

noncomputable def admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (demand : RegistrationNativeRelatedFamily.Message → m (Option (Choice n)))
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) : m (RustM Result) := do
  match ← demand message with
  | none => pure (.ok (.Err ⟨descriptor.candidate.assigned_key_id⟩))
  | some choice => publicBranch source raw effects owner descriptor choice

noncomputable def privateAdmitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (demand : RegistrationNativeRelatedFamily.Message → m (Option (PrivateChoice n)))
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) : m (RustM Result) := do
  match ← demand message with
  | none => pure (.ok (.Err ⟨descriptor.candidate.assigned_key_id⟩))
  | some choice => privateBranch source raw effects owner descriptor choice

theorem admitted_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RegistrationRawSealBridge.Spec m) (effects : QueryImpl (EnvEffects n) m)
    (demand : RegistrationNativeRelatedFamily.Message → m (Option (PrivateChoice n)))
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) :
    admitted source raw effects (fun query => Option.map publicChoice <$> demand query) owner descriptor message =
      privateAdmitted source raw effects demand owner descriptor message := by
  simp only [admitted, privateAdmitted, bind_map_left]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => rfl
  | some choice => exact branch_split source raw effects owner descriptor choice

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.after_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.after_replace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.stage_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.stage_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.branch_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.branch_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.admitted_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService.admitted_split

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService
