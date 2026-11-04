-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotSource
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealSelected
/-! Every actual native snapshot run has the same complete candidate-independent symbolic source execution. Native trace, public successful-session ledger, persistent platform/private state, and physical state are retained; the selected parsed accept coordinate remains separate from the public session coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotExecution
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Physical A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (candidate : MlKemSharedSecret)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "unused" => RegistrationNativePlatformLorIdealSelected.unused (n := n)
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedOwner pairs (Prod.fst chosen) challenge candidate
local notation "closedImpl" => RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selectedOwner pairs (Prod.fst chosen) challenge physical
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept
  (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
abbrev NativePrivate (n : Nat) (KemSK : Type) := RegistrationNativePlatformLorIdealSelected.NativePrivate n KemSK
abbrev Result (n : Nat) (KemSK Platform Physical A : Type) (source : RegistrationNativeMldsa.Source) :=
  ((A × RegistrationNativeLedger.State) × RegistrationNativePlatformPublicFrontend.State source Platform) ×
    RegistrationNativePlatformRecordPartnerSlotTrace.State n KemSK RegistrationNativeKemSwitchSource.Phase Physical

/-- A supported actual joint snapshot execution has one exact full symbolic source run, retaining the same trace and original public ledger. -/
theorem source_result (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (privateBefore : NativePrivate n KemSK) (physicalBefore : Physical)
    (pool : privateBefore.1.pool=PqxdhLiveKemBirth.empty) (phase : privateBefore.1.provider=none)
    (result : Result n KemSK Platform Physical A source)
    (supported : result∈support ((simulateQ (RegistrationNativePlatformRecordPartnerSlotTrace.handler setup wire sign seed scalar candidate actualProvider physical)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (RegistrationNativePlatformPublicFrontend.run setup checks RegistrationNativePlatformConcreteSource.wire source sign selectedOwner selectedAccept
          (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before))).run
            (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(privateBefore,physicalBefore)))) :
    ∃ reached : RegistrationNativePlatformLorIdealSelected.SourceResult n KemSK Platform Physical A source,
      reached∈support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (RegistrationNativePlatformLorStatefulSupport.traced closedImpl controller) mode work
          (RegistrationNativePlatformLorIdealSelected.sourceBefore source before privateBefore physicalBefore)) ∧
      RegistrationNativePlatformLorIdealTraceRun.projectResult candidate reached=
        RegistrationNativePlatformRecordPartnerSnapshotSource.project result := by
  have projected := Set.mem_image_of_mem RegistrationNativePlatformRecordPartnerSnapshotSource.project supported
  rw [←support_map,RegistrationNativePlatformRecordPartnerSnapshotSource.native_source] at projected
  have related := RegistrationNativePlatformLorIdealTraceRun.closed_source setup sign seed scalar candidate unused
    selectedOwner pairs (Prod.fst chosen) challenge checks selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer physical serverKeyId bounds mode work
    (RegistrationNativeG3NativeStartupFields.word before.1,before.2)
    (RegistrationNativePlatformLorIdealInitial.symbolicPrivate privateBefore) physicalBefore
  rw [RegistrationNativePlatformLorIdealInitial.frame_private candidate privateBefore pool phase] at related
  simp only [RegistrationNativePlatformSecretWordOrdinary.evaluate,Prod.map_apply,RegistrationNativeG3NativeStartupFields.word_eval,id_eq,Prod.mk.eta] at related
  simp only [RegistrationNativeG2Trace.program] at related
  rw [←related,support_map] at projected
  exact projected

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotExecution.source_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotExecution.source_result
