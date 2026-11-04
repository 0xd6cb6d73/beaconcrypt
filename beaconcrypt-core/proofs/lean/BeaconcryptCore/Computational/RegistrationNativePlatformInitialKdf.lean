-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceFinishContents

/-! Actual allocator/writer Platform record success retains the source initializer's exact reached fixed-HKDF callback and resume, before any later step, hash, allocation or publication. The receipt concerns the reached pending capability and never reconstructs an initializer from a later ratchet state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInitialKdf
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformSourceSealTrace (joint)
variable {n : Nat} {E Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

/-- Actual successful source record execution consumes the concrete fixed-HKDF reply at its actual source initializer callback and reaches the same retained first-record phase. -/
theorem server (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash)
    (before after : RegistrationServerRootCompiler.Local n × Platform)
    (supported : (.ok (.Ok completed), after) ∈ support ((joint (RegistrationNativePlatformSourceSealTrace.record
      coins setup codec view failure allocation erased helper initial)).run before)) :
    ∃ request atStep next,
      initial.request = .ok request ∧
      (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), atStep) ∈ support
        ((joint (RegistrationNativePlatformServerCompletion.records coins setup codec (.initialKdf request))).run before) ∧
      initial.resume (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request)) = .ok (.Ok next) := by
  obtain ⟨actual⟩ := RegistrationNativePlatformSourceSealTrace.run coins setup codec view failure allocation erased helper
    initial completed before after supported
  have called := (RegistrationNativePlatformRawFrame.joint_support _ _ _ _ _ _).mp actual.initialCalled
  have native : (actual.initialReply, actual.first.1) ∈ support
      ((RegistrationWorldRecords.handler setup codec (.initialKdf actual.initialRequest)).run before.1) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ before.2 actual.first.2 called
  have replyEq := RegistrationNativeInitialKdfCuts.world_reply setup codec actual.initialRequest before.1 actual.first.1 actual.initialReply native
  refine ⟨actual.initialRequest, actual.first, actual.ratchet, actual.initialRequested, ?_, ?_⟩
  · rw [← replyEq]; exact actual.initialCalled
  · rw [← replyEq]; exact actual.initialResumed

end BeaconcryptCore.Computational.RegistrationNativePlatformInitialKdf

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitialKdf.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitialKdf.server
