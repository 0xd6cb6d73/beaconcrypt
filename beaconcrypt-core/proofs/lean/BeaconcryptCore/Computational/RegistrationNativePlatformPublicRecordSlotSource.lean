-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotSafety
/-! The literal current source raw run computes the same opaque slot/installation observer as its actual complete selective World execution. Safety and backend footprints are derived from the current callbacks, not supplied as a source/controller conclusion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
variable {n : Nat} {KemSK A : Type}

/-- Any granularly safe public tree closes through the actual selective backend with the same opaque slot and ordinal output and complete original private state. -/
theorem source {I ProviderState : Type} {base : OracleSpec I}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (safe : RegistrationNativePlatformPublicSlotKind.Safe work)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    RegistrationNativePlatformRecordSlotGhost.program
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before) ghost.snapshot =
      (fun result => ((result.1.1,result.2),result.1.2.snapshot)) <$>
        (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          (RegistrationNativePlatformPublicRecordSlots.program work ghost)).run before := by
  have agreed := RegistrationNativePlatformPublicRecordSlotAgreement.run_agrees work safe ghost
  have closed := congrArg (fun tree => (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) tree).run before) agreed
  simp only [simulateQ_map,StateT.run_map] at closed
  rw [RegistrationNativePlatformRecordSlotBackend.program setup wire sign seed scalar candidate provider work ghost.snapshot before,← closed]
  simp only [Functor.map_map]

variable {E Platform I : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "Front" => RegistrationNativePlatformPublicFrontend.State source Platform
local notation "embed" => RegistrationNativePlatformPublicCoinEmbedding.embed


variable {ProviderState : Type}
/-- Every original canonical raw mode derives the opaque slot observation on its actual persistent backend run, with no caller kind, frame, material or controller premise. -/
theorem run (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : Front)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n)
    (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    RegistrationNativePlatformRecordSlotGhost.program
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
        (simulateQ embed (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run privateBefore) ghost.snapshot =
      (fun result => ((result.1.1,result.2),result.1.2.snapshot)) <$>
        (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          (RegistrationNativePlatformPublicRecordSlots.program
            (simulateQ embed (RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before)) ghost)).run privateBefore := by
  exact RegistrationNativePlatformPublicRecordSlotSource.source setup wire sign seed scalar candidate provider _
    (RegistrationNativePlatformPublicSlotSafety.run setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before) ghost privateBefore
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlotSource.run
