-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
/-! All actual dynamic ordinary routes preserve the complete earlier immutable owner prefix. The corrected registration branches use their literal metadata receipts, while ongoing source records retain the owner list exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

variable {A : Type} [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "typed" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
open RegistrationNativeOwnerRoster (Prefix)

omit primitive in
private theorem trans (first middle last : RegistrationNativeBeaconFrontend.State source)
    (earlier : Prefix first middle) (later : Prefix middle last) : Prefix first last := by
  obtain ⟨left,before⟩ := earlier
  obtain ⟨right,after⟩ := later
  exact ⟨left ++ right,by rw [after,before,List.append_assoc]⟩

/-- The packed literal current callback preserves its complete earlier immutable owner prefix and platform state. -/
theorem typed_prefix (query : TypedSpec.Domain) (before : Native × Platform)
    (result : TypedSpec.Range query × (Native × Platform))
    (supported : result ∈ support ((typed query).run before)) : Prefix before.1.beacons result.2.1.beacons := by
  simp only [RegistrationNativePlatformOrdinaryKemClientJournal.actual,RegistrationNativePlatformPackedState.pack,StateT.run,support_map] at supported
  obtain ⟨actual,called,equal⟩ := supported
  cases equal
  exact RegistrationNativePlatformOrdinaryOwnerRoster.handler setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query before.1 actual.1.2 before.2 actual.2 actual.1.1 called

/-- Every adaptive corrected typed program retains all prior owner metadata at their original indices. -/
theorem program_prefix (work : OracleComp TypedSpec A) (before : Native × Platform)
    (result : A × (Native × Platform)) (supported : result ∈ support ((simulateQ typed work).run before)) :
    Prefix before.1.beacons result.2.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => Prefix before.1.beacons current.1.beacons)
    (fun query current prior next reached => trans _ _ _ prior
      (typed_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current next reached))
    work before ⟨[],(List.append_nil _).symm⟩ result supported

/-- Literal raw parsing preserves the same actual owner roster relation. -/
theorem raw_prefix (work : OracleComp RegistrationNativeInterface.Spec A) (before : Native × Platform)
    (result : A × (Native × Platform))
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler canonical typed) work).run before)) :
    Prefix before.1.beacons result.2.1.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result supported

/-- Every original raw or secrecy callback retains earlier immutable owners beside the actual full native ledger. -/
theorem full_prefix (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × (Native × Platform))
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × (Native × Platform)))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto canonical created.server.server.metadata.sender bounds typed query).run before)) :
    Prefix before.2.1.beacons result.2.2.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨inner,reached,rfl⟩ := supported
  exact raw_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before.2 inner reached

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.typed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.typed_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.raw_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.raw_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.full_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRosterRun.full_prefix
