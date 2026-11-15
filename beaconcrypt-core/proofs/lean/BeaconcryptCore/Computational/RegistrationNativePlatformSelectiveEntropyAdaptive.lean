-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropySourceExecution
/-! The actual corrected raw frontend closes over its literal selective World backend. Registration callbacks retain their restricted source effects; ordinary routes keep their actual post-send allocator and full shared platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


open RegistrationNativeHiddenEnvironmentWorld (lower)
local notation "actualRaw" => RegistrationNativePlatformSelectiveEntropyNative.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actualTyped" => RegistrationNativePlatformSelectiveEntropyExecution.handler (n := n) setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "reference" => RegistrationNativePlatformSelectiveEntropyQuery.reference (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "JointState" => RegistrationNativePlatformHiddenAllocationCore.State n Platform
  (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret source
open RegistrationNativePlatformHiddenAllocationCore (Holds)
variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The actual raw callback retains the startup-derived physical-owner invariant through every source outcome. -/
theorem handler_holds (query : RegistrationNativeInterface.Spec.Domain) (before : JointState)
    (result : RegistrationNativeInterface.Spec.Range query × JointState) (valid : Holds before)
    (supported : result ∈ support ((lower service codec route (actualRaw query)).run before)) : Holds result.2 := by
  rw [RegistrationNativePlatformSelectiveEntropySourceExecution.handler_source] at supported
  exact RegistrationNativePlatformHiddenAllocation.raw_holds setup checks wire credential seed scalar candidate provider
    selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    service codec route query before result valid supported

omit primitive in
private theorem pair_id {X Y : Type} : Prod.map (id : X → X) (id : Y → Y) = (id : X × Y → X × Y) := by
  funext value
  cases value
  rfl

/-- Full adaptive source execution equals the gated native environment in the exact same source/P, cursor, Protocol and private World state. -/
theorem program_source
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) × State n KemSK ProviderState Platform source)))
    (work : OracleComp RegistrationNativeInterface.Spec Value) (before : JointState) (valid : Holds before) :
    (lower service codec route (simulateQ actualRaw work)).run before =
      (lower service codec route (simulateQ (reference startup) work)).run before := by
  rw [RegistrationNativeHiddenEnvironmentWorld.program_lower, RegistrationNativeHiddenEnvironmentWorld.program_lower]
  have represented := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (fun query => lower service codec route (actualRaw query))
    (fun query => lower service codec route (reference startup query)) Holds id
    (fun query current good answer reached => handler_holds setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route query current answer good reached)
    (fun query current good => by
      simpa only [pair_id, id_map, id_eq] using
        RegistrationNativePlatformSelectiveEntropyQuery.query_source setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup service codec route query current good)
    work before valid
  simpa only [pair_id, id_map, id_eq] using represented

/-- The complete original full secrecy ledger and all observation modes retain the same exact initialized source execution. -/
theorem full_source
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) × State n KemSK ProviderState Platform source)))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : JointState) (valid : Holds before) :
    (lower service codec route (simulateQ actualTyped
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds mode work))).run before =
      (lower service codec route (simulateQ (reference startup)
        (RegistrationNativeLedger.wrap setup.source.crypto
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds
          (RegistrationNativeInterface.asModeO mode work)))).run before := by
  have execution : simulateQ actualTyped
      (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds mode work) = simulateQ actualRaw
      (RegistrationNativeLedger.wrap setup.source.crypto
        (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds
        (RegistrationNativeInterface.asModeO mode work)) := by
    funext initial
    exact RegistrationNativePlatformSelectiveEntropySourceExecution.run_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work initial
  rw [execution]
  exact program_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route startup _ before valid
end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive.handler_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive.handler_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyAdaptive.full_source
