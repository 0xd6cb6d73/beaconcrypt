-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting
/-! Actual corrected platform callbacks retain their complete projected Native state and external platform state under original-input and normalized ML count equations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaCountRules (Correct)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (RegistrationNativeExperiment.State n KemSK source) (M source Platform) (Option RawCtxSourceSend.Encrypted))
    (good : Correct RegistrationNativeMldsaMainView.project work) :
    Correct RegistrationNativeMldsaMainView.project (RegistrationNativePlatformOrdinaryMldsaRouting.after reserve work) := by
  apply RegistrationNativePlatformMldsaCountRules.bind RegistrationNativeMldsaMainView.project _ _ good
  intro output
  exact RegistrationNativePlatformMldsaCountRules.external RegistrationNativeMldsaMainView.project
    RegistrationNativeMldsaMainView.idempotent _

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Every actual corrected callback has both count equations, including all stateful first-record and source publication failures. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (RegistrationNativePlatformOrdinaryMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query) := by
  rw [RegistrationNativePlatformOrdinaryMldsaRouting.handler]
  have original := RegistrationNativePlatformMldsaCountRun.handler (n := n) setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer query
  cases query with
  | inl coin => exact original
  | inr query => cases query with
    | serverSend keyId plaintext => exact after reserveFrame _ original
    | beaconSend owner plaintext => exact after reserveFrame _ original
    | _ => exact original

/-- Arbitrary adaptive typed work preserves the full projected Native state and exact public platform state under both source count equations. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (simulateQ (RegistrationNativePlatformOrdinaryMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer) work) :=
  RegistrationNativePlatformMldsaCountRules.simulate _ RegistrationNativeMldsaMainView.idempotent _
    (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work

def observed (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source) × Platform) :=
  ((result.1.1, RegistrationNativeMldsaMainView.project result.1.2), result.2)

/-- Original corrected execution is independent of omitted accounting inputs while retaining its literal compiled ledger and external poststate. -/
theorem run_original (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    observed <$> ((RegistrationNativePlatformOrdinaryMldsaProfile.run setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous) =
      observed <$> ((RegistrationNativePlatformOrdinaryMldsaProfile.run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work (RegistrationNativeMldsaMainView.project before)).run previous) := by
  have same := congrArg (fun action => (fun result => ((result.1, result.2.1), result.2.2)) <$> action)
    ((program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work)).1 (before, previous))
  simp only [RegistrationNativePlatformOrdinaryMldsaProfile.run, RegistrationNativePlatformPackedState.pack,
    StateT.run, Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project] at same ⊢
  exact same

/-- Normalizing each named ML draw receipt retains the exact original compiled ledger/test bit and complete projected Native/platform poststate. -/
theorem run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    observed <$> RegistrationNativeMldsaCountMap.transform
      ((RegistrationNativePlatformOrdinaryMldsaProfile.run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous) =
      observed <$> ((RegistrationNativePlatformOrdinaryMldsaProfile.run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work (RegistrationNativeMldsaMainView.project before)).run previous) := by
  have same := congrArg (fun action => (fun result => ((result.1, result.2.1), result.2.2)) <$> action)
    ((program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work)).2 (before, previous))
  simp only [RegistrationNativePlatformOrdinaryMldsaProfile.run, RegistrationNativePlatformPackedState.pack,
    StateT.run, RegistrationNativeMldsaCountMap.transform, simulateQ_map, Functor.map_map,
    Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project] at same ⊢
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.run_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.run_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaCountRun.run
