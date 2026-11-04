-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconService
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
/-! Stateful opening callbacks preserve actual request bookkeeping as well as the World and external state. The executable hidden branch retains only material44 and a private slot. The actual source KDF markers are discharged separately before this service; the program cannot request a hidden chain. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner
open PqxdhRecordLiftInterface
open RegistrationNativePairedChoice (Choice PrivateChoice publicChoice)
open RegistrationNativePairedBeaconService (Result)
variable {n : Nat} {m : Type → Type} [Monad m]

open RegistrationNativePlatformPairedBeaconService (after)

noncomputable def knownStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) : m (RustM Result) := do
  let result ← simulateQ raw (RegistrationBeaconSeed.program source descriptor output)
  after effects owner (fun completed => .known completed.kernel) result

noncomputable def hiddenStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) : m (RustM Result) := do
  let result ← simulateQ raw (RegistrationBeaconSeed.program source descriptor output)
  after effects owner (fun _ => .hidden slot) result

noncomputable def publicHidden (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : RegistrationNativePairedDemand.Reference n) : m (RustM Result) :=
  hiddenStage source raw effects owner reference.slot descriptor
    (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBeaconSeed.fixedSeed)

variable [LawfulMonad m]

theorem stage_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    hiddenStage source raw effects owner slot descriptor (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      publicHidden source raw effects owner descriptor ⟨slot, material⟩ := by
  unfold hiddenStage publicHidden
  rw [RegistrationBeaconSeed.program_split]
  simp only [simulateQ_map, bind_map_left, RegistrationBeaconSeed.publicProgram]
  apply bind_congr
  intro result
  exact RegistrationNativePlatformPairedBeaconService.after_replace effects owner slot _ result

noncomputable def privateBranch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    PrivateChoice n → m (RustM Result)
  | .known output => knownStage source raw effects owner descriptor output
  | .hidden slot output => hiddenStage source raw effects owner slot descriptor output

noncomputable def publicBranch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    Choice n → m (RustM Result)
  | .known output => knownStage source raw effects owner descriptor output
  | .hidden reference => publicHidden source raw effects owner descriptor reference

theorem branch_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
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
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (demand : RegistrationNativeRelatedFamily.Message → m (Option (Choice n)))
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) : m (RustM Result) := do
  match ← demand message with
  | none => pure (.ok (.Err ⟨descriptor.candidate.assigned_key_id⟩))
  | some choice => publicBranch source raw effects owner descriptor choice

noncomputable def privateAdmitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
    (demand : RegistrationNativeRelatedFamily.Message → m (Option (PrivateChoice n)))
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) : m (RustM Result) := do
  match ← demand message with
  | none => pure (.ok (.Err ⟨descriptor.candidate.assigned_key_id⟩))
  | some choice => privateBranch source raw effects owner descriptor choice

theorem admitted_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (raw : QueryImpl RawCtxWholeOwner.PrimitiveSpec m) (effects : QueryImpl (EnvEffects n) m)
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

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner.stage_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner.stage_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner.branch_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner.branch_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner.admitted_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner.admitted_split

end BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconOwner
