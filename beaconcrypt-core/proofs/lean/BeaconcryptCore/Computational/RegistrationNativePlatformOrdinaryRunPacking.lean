-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
/-! Reassociate the literal dynamic runtime without changing the original returned value, full ledger or native/platform state. This supplies the generic full-compiler support relation for actual source event proofs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

variable {A : Type} [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "typed" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

/-- Reassociation retains the original ledger and both actual state components. -/
theorem run_source (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native) (previous : Platform) :
    (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
      ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous) =
    RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work (before,previous) := by
  unfold RegistrationNativePlatformOrdinaryKemClientJournal.actual
  rw [RegistrationNativeFullCompiler.compile_run]
  have packed := congrArg (fun execution => execution.run (before,previous))
    (RegistrationNativePlatformPackedState.simulate_pack
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto canonical created.server.server.metadata.sender bounds mode work))
  have moved := congrArg (fun distribution =>
    (fun result : (A × RegistrationNativeLedger.State) × (Native × Platform) => (result.1.1,(result.1.2,result.2))) <$> distribution) packed
  simpa only [RegistrationNativePlatformPackedState.pack,RegistrationNativePlatformOrdinaryExperiment.run,RegistrationNativePlatformOrdinaryKemClientJournal.actual,StateT.run,Functor.map_map] using moved

/-- Support transport keeps the same returned value, full ledger, native state and platform poststate. -/
theorem supported (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Native) (previous : Platform)
    (result : (((A × RegistrationNativeLedger.State) × Native) × Platform))
    (called : result ∈ support ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before).run previous)) :
    (result.1.1.1,(result.1.1.2,(result.1.2,result.2))) ∈ support
      (RegistrationNativeFullCompiler.run setup.source.crypto canonical created.server.server.metadata.sender bounds typed mode work (before,previous)) := by
  rw [← run_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before previous,support_map]
  exact Set.mem_image_of_mem _ called

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking.supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRunPacking.supported
