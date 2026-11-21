-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryTyped
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProgram

/-! Chronological owner/service synchronization holds at every reached adaptive typed prefix and beneath the literal original native CE ledger. The generated empty owner roster and private empty source establish the invariant directly. No history-preservation or source-simulation premise is supplied by a public client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityMainSource (interpret implementation)
open RegistrationNativeIdentityMainHistory (Inv)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Every reached adaptive native prefix retains actual per-handle signing history and source ownership. -/
theorem program_inv (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK mlSource × SourceState)
    (result : Value × (State n KemSK mlSource × SourceState)) (prior : Inv setup.joint before)
    (supported : result ∈ support ((interpret setup.joint
      (simulateQ (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential) work)).run before)) :
    Inv setup.joint result.2 := by
  rw [RegistrationNativeIdentityMainProgram.interpret_program] at supported
  exact simulateQ_run_preservesInv (RegistrationNativeIdentityMainProgram.compiled setup checks wire route representation created credential)
    (Inv setup.joint)
    (fun query current previous next reached => RegistrationNativeIdentityMainHistoryTyped.handler_inv
      setup checks wire route representation created credential query current next previous reached)
    work before prior result supported

/-- The literal original native CE compiler and ledger retain the same generated histories below every command. -/
theorem run_inv (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : State n KemSK mlSource × SourceState)
    (result : (Value × (RegistrationNativeLedger.State × State n KemSK mlSource)) × SourceState)
    (prior : Inv setup.joint before)
    (supported : result ∈ support ((simulateQ (implementation setup.joint)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work before.1)).run before.2)) :
    Inv setup.joint (result.1.2.2, result.2) := by
  rw [RegistrationNativeIdentityMain.run, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  apply program_inv setup checks wire route representation created credential
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before
    (inner.1.1, (inner.1.2, inner.2)) prior
  change (inner.1.1, (inner.1.2, inner.2)) ∈ support
    ((fun evaluated : ((Value × RegistrationNativeLedger.State) × State n KemSK mlSource) × SourceState =>
      (evaluated.1.1, (evaluated.1.2, evaluated.2))) <$>
      (simulateQ (implementation setup.joint)
        ((simulateQ (RegistrationNativeIdentityMain.handler setup checks wire route representation created credential)
          (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).run before.1)).run before.2)
  rw [support_map]
  exact Set.mem_image_of_mem _ reached

/-- The generated empty roster and literal empty indexed source establish all internal history obligations. -/
theorem initial_inv (joint : PqxdhJointIdentity.Primitives) (context : Context n KemSK) :
    Inv joint ((⟨context, []⟩ : State n KemSK mlSource), PqxdhDynamicIdentityPool.initialState) := by
  refine ⟨⟨?_, ?_, ?_⟩, RegistrationNativeIdentityHistoryReserved.initial_empty⟩
  · exact RegistrationNativeIdentitySourceCreateOwned.empty_owned joint _
  · simp [RegistrationNativeIdentityHistorySync.Distinct, RegistrationNativeIdentityHistorySync.handles]
  · exact RegistrationNativeIdentityHistorySync.synced_empty _

/-- Any complete original-ledger execution from actual empty Beacon initialization has synchronized histories at every generated handle. -/
theorem initialized_run_inv (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (context : Context n KemSK)
    (result : (Value × (RegistrationNativeLedger.State × State n KemSK mlSource)) × SourceState)
    (supported : result ∈ support ((simulateQ (implementation setup.joint)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work
        ⟨context, []⟩)).run PqxdhDynamicIdentityPool.initialState)) :
    Inv setup.joint (result.1.2.2, result.2) :=
  run_inv setup checks wire route representation created credential bounds mode work
    (⟨context, []⟩, PqxdhDynamicIdentityPool.initialState) result (initial_inv setup.joint context) supported

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.program_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.program_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.run_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.run_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.initial_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.initial_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.initialized_run_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun.initialized_run_inv
