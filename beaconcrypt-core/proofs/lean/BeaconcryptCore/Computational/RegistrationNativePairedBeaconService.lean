-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconSeed
import BeaconcryptCore.Computational.RegistrationNativePairedServerService
import BeaconcryptCore.Computational.RegistrationBoundSourceCompiler

/-! Both native roles demand the same persistent message-indexed material service. The Beacon's hidden continuation receives material44 and an opaque slot, then executes the actual sequence-one opening and final native admission. Successful installation resolves the already cached consumed Beacon kernel through the private World; ordinary side replies retain their real output and known kernel. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedBeaconService
open PqxdhRecordLiftInterface
open RegistrationNativePairedChoice (Choice PrivateChoice publicChoice)
open RegistrationNativePairedServerService (Common PrivateSpec PublicSpec privateCommon publicCommon)
open RegistrationBeaconSeed (PublicCompleted publicResult)
variable {n : Nat}

/-- Exact source functional KDF/opening operations and the same typed shared hash channel as the Server. -/
noncomputable def read (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RegistrationRawReceiveBridge.Spec (OracleComp RegistrationRawSealBridge.Spec)
  | .inl query => RegistrationRawSealBridge.Spec.query (.inl query)
  | .inr (.inl request) => pure (RawCtxSourceHkdf.response source.crypto request)
  | .inr (.inr (.inl bytes)) => RegistrationRawSealBridge.Spec.query (.inr (.inr (.inl bytes)))
  | .inr (.inr (.inr input)) => pure (RegistrationAuthenticationShared.openedBytes (RawCtxSourceOpen.baseOpen source.crypto input))

noncomputable def opening (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp RegistrationRawSealBridge.Spec) :=
  read source ∘ₛ (RegistrationRawReceiveBridge.modelAdapter ∘ₛ RawCtxSourceOpen.nativeAdapter)

def rawLift : QueryImpl RegistrationRawSealBridge.Spec (OracleComp (Common n)) :=
  fun query => (Common n).query (.inl (.inl query))

theorem read_source {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : RegistrationRawReceiveBridge.Spec.Domain) :
    simulateQ (RegistrationRawSealBridge.implementation (Auxiliary := Auxiliary) source writer) (read source query) =
      RegistrationRawReceiveBridge.implementation source writer query := by
  cases query with
  | inl request => simp only [read, simulateQ_spec_query]; rfl
  | inr request => cases request with
    | inl request => rfl
    | inr request => cases request with
      | inl bytes => simp only [read, simulateQ_spec_query]; rfl
      | inr input => rfl

theorem read_program {Auxiliary Value : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp RegistrationRawReceiveBridge.Spec Value) :
    simulateQ (RegistrationRawSealBridge.implementation (Auxiliary := Auxiliary) source writer) (simulateQ (read source) work) =
      simulateQ (RegistrationRawReceiveBridge.implementation source writer) work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationRawSealBridge.implementation (Auxiliary := Auxiliary) source writer ∘ₛ read source =
      RegistrationRawReceiveBridge.implementation source writer := by
    funext query
    exact read_source source writer query
  rw [same]

noncomputable def program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp RegistrationRawSealBridge.Spec (RustM RegistrationBeaconRecordExecutor.Result) :=
  simulateQ (opening source) (RegistrationBeaconSeed.program source descriptor output)

/-- The complete actual source record service is reconstructed with every shared primitive state and optional failure retained. -/
theorem program_source {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ (RegistrationRawSealBridge.implementation (Auxiliary := Auxiliary) source writer) (program source descriptor output) =
      RegistrationBeaconBoundSource.fromOutput source writer descriptor output := by
  rw [RegistrationBeaconSeed.program_source]
  simp only [program, opening, QueryImpl.simulateQ_compose]
  rw [read_program]
  simp only [← QueryImpl.simulateQ_compose]
  rfl

theorem program_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) :
    program source descriptor (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      RegistrationBeaconSeed.replace (PqxdhRecordLiftWorld.kernel .beacon seed) <$>
        program source descriptor (PqxdhDeploymentHiddenLayout.joinOutput material RegistrationBeaconSeed.fixedSeed) := by
  have same := congrArg (simulateQ (opening source)) (RegistrationBeaconSeed.program_split source descriptor material seed)
  simpa only [program, simulateQ_map, RegistrationBeaconSeed.publicProgram] using same

abbrev Result := core.result.Result PublicCompleted pqxdh.BeaconAborted

def after (owner : Nat) (sender : U64) (selectKernel : registration.CompletedBeacon → KernelRef n) :
    RustM RegistrationBeaconRecordExecutor.Result → OracleComp (EnvEffects n) (RustM Result)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err aborted) => pure (.ok (.Err aborted))
  | .ok (.Ok completed) => do
      let installed : Bool ← (EnvEffects n).query (.inr (.installBeacon owner
        ⟨sender, completed.control, completed.binding.associated_data⟩ (selectKernel completed)))
      pure (if installed then .ok (.Ok ⟨completed.control, completed.binding, completed.application⟩)
        else .ok (.Err ⟨sender⟩))

theorem hidden_after_replace (owner : Nat) (sender : U64) (slot : Slot n)
    (kernel : ConcreteRatchetKernel) (result : RustM RegistrationBeaconRecordExecutor.Result) :
    after owner sender (fun _ => .hidden slot) (RegistrationBeaconSeed.replace kernel result) =
      after owner sender (fun _ => .hidden slot) result := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

noncomputable def knownStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) : OracleComp (Common n) (RustM Result) := do
  let result ← simulateQ rawLift (program source descriptor output)
  simulateQ RegistrationHiddenInstall.effectLift (after owner sender (fun completed => .known completed.kernel) result)

noncomputable def privateHiddenStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) : OracleComp (Common n) (RustM Result) := do
  let result ← simulateQ rawLift (program source descriptor output)
  simulateQ RegistrationHiddenInstall.effectLift (after owner sender (fun _ => .hidden slot) result)

noncomputable def hiddenStage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : RegistrationNativePairedDemand.Reference n) : OracleComp (Common n) (RustM Result) :=
  privateHiddenStage source owner sender reference.slot descriptor
    (PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBeaconSeed.fixedSeed)

theorem hidden_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (slot : Slot n) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (material : PqxdhDeploymentHiddenLayout.Material) (seed : PqxdhRecordLiftSeed.Seed) :
    privateHiddenStage source owner sender slot descriptor (PqxdhDeploymentHiddenLayout.joinOutput material seed) =
      hiddenStage source owner sender descriptor ⟨slot, material⟩ := by
  unfold hiddenStage privateHiddenStage
  rw [program_split]
  simp only [simulateQ_map, bind_map_left]
  congr 1
  funext result
  rw [hidden_after_replace]

noncomputable def privateBranch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    PrivateChoice n → OracleComp (Common n) (RustM Result)
  | .known output => knownStage source owner sender descriptor output
  | .hidden slot output => privateHiddenStage source owner sender slot descriptor output

noncomputable def publicBranch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) :
    Choice n → OracleComp (Common n) (RustM Result)
  | .known output => knownStage source owner sender descriptor output
  | .hidden reference => hiddenStage source owner sender descriptor reference

theorem branch_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (choice : PrivateChoice n) :
    publicBranch source owner sender descriptor (publicChoice choice) = privateBranch source owner sender descriptor choice := by
  cases choice with
  | known output => rfl
  | hidden slot output =>
      have same := hidden_split source owner sender slot descriptor
        (PqxdhDeploymentHiddenLayout.splitOutput output).1 (PqxdhDeploymentHiddenLayout.splitOutput output).2
      simpa only [PqxdhDeploymentHiddenLayout.join_split, publicBranch, privateBranch,
        RegistrationNativePairedChoice.publicChoice] using same.symm

noncomputable def privateAdmitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) : OracleComp (PrivateSpec n) (RustM Result) := do
  let chosen ← (PrivateSpec n).query (.inl message)
  match chosen with
  | none => pure (.ok (.Err ⟨sender⟩))
  | some choice => simulateQ privateCommon (privateBranch source owner sender descriptor choice)

noncomputable def admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) : OracleComp (PublicSpec n) (RustM Result) := do
  let chosen ← (PublicSpec n).query (.inl message)
  match chosen with
  | none => pure (.ok (.Err ⟨sender⟩))
  | some choice => simulateQ publicCommon (publicBranch source owner sender descriptor choice)

/-- Material is demanded only after the actual root-preparation capability exists; its private/public branches retain the same actual opening and insertion behavior. -/
theorem admitted_split (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) :
    simulateQ (RegistrationNativePairedServerService.erase (n := n)) (admitted source owner sender descriptor message) =
      privateAdmitted source owner sender descriptor message := by
  simp only [admitted, privateAdmitted, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativePairedServerService.erase, bind_map_left]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => simp only [Option.map_none, simulateQ_pure]
  | some choice => simp only [Option.map_some, RegistrationNativePairedServerService.common_program, branch_split]

end BeaconcryptCore.Computational.RegistrationNativePairedBeaconService

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.read_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.read_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.read_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.read_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.program_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.program_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.hidden_after_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.hidden_after_replace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.hidden_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.hidden_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.branch_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.branch_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.admitted_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedBeaconService.admitted_split
