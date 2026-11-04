-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame
/-! The same source build joint supplies its complete actual local frame, rather than recovering it from an erased client view. This connects public earlier-root capabilities to the literal Native build marginal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePlatformServerCompilerJoint (joint nativeView)
variable {n : Nat} {E Platform I KemSK Reader Response : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]

/-- The full source joint preserves precisely the prior local auxiliary value and agreement history; the statement is derived from the actual SourceSeal SDK run. -/
theorem frame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (roots : RegistrationServerReferenceRestore.Roots)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : RegistrationServerRootCompiler.Local n) (previous : Platform)
    (result : RegistrationNativePlatformServerCompilerJoint.Outcome n Platform)
    (supported : result ∈ support (joint setup codec view failure allocation erased helper sign writer reserve roots handle application front before previous)) :
    result.1.2.2.auxiliary = before.auxiliary ∧ result.1.2.2.requests = before.requests := by
  have native : nativeView roots result ∈ support
      (((RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation erased reserve sign helper writer handle application).run
        (RegistrationNativePlatformServerMaterialState.restore roots (front, before))).run previous) := by
    simp only [RegistrationNativePlatformSourceSeal.build]
    rw [← RegistrationNativePlatformServerCompilerJoint.native_marginal]
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  have kept := RegistrationNativePlatformSourceSdkFrame.source RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation erased reserve sign helper writer handle application
    (RegistrationNativePlatformServerMaterialState.restore roots (front, before)) previous (nativeView roots result).1 (nativeView roots result).2 native
  exact Prod.mk.inj kept

open RegistrationNativePlatformPublicBuildJoint (Reply jointState stateView)

def restored (roots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (result : Reply × State n KemSK Platform source) :=
  (result.1, (RegistrationNativePublicSourceState.restore roots scalar result.2.1.1 result.2.2, result.2.1.2))

def nativeResult (roots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : State n KemSK Platform source) (result : RegistrationNativePlatformServerCompilerJoint.Outcome n Platform) :=
  (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    ({ (RegistrationNativePublicSourceState.restore roots scalar before.1.1 before.2) with server := RegistrationServerMaterialSourceState.nativeView (RegistrationNativePlatformServerMaterialState.restore roots result.1.2) }, result.2))

omit primitive in
private theorem reconstruct (roots : RegistrationServerReferenceRestore.Roots) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : State n KemSK Platform source) (result : RegistrationNativePlatformServerCompilerJoint.Outcome n Platform)
    (auxiliary : result.1.2.2.auxiliary = before.1.1.environment.auxiliary)
    (requests : result.1.2.2.requests = before.1.1.environment.requests) :
    restored roots scalar (jointState before result) = nativeResult roots scalar before result := by
  simp only [restored, jointState, RegistrationNativePlatformPublicBuildJoint.buildState,
    nativeResult, RegistrationNativePublicSourceState.restore, RegistrationServerMaterialSourceState.restore,
    RegistrationServerMaterialSourceState.nativeView, RegistrationNativePlatformServerMaterialState.restore,
    RegistrationServerReferenceRestore.restore, RegistrationWorldAgreementCompiler.join,
    RegistrationServerRecordWorldSource.project]
  rw [auxiliary, requests]

/-- The actual adaptive earlier-root build and the literal source SDK build have the same complete restored Native security state, including every private frame coordinate and persistent platform outcome. -/
theorem build_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : State n KemSK Platform source)
    (live : RegistrationNativePublicSourceState.Live before.1.1 before.2)
    (correct : RegistrationNativePublicSourceState.MemoCorrect setup seed scalar before.2.roots) :
    restored (RegistrationNativePublicSourceState.roots setup seed scalar) scalar <$>
      (Prod.map id stateView <$> (execute setup wire route sign seed scalar
        (RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source))).run before) =
    (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
      ({ (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup seed scalar) scalar before.1.1 before.2) with server := RegistrationServerMaterialSourceState.nativeView result.1.2 }, result.2))) <$>
      (((RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reserve sign helper writer handle application).run
        (RegistrationNativePlatformServerMaterialState.restore (RegistrationNativePublicSourceState.roots setup seed scalar)
          (before.1.1.server, RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world))).run before.1.2) := by
  rw [RegistrationNativePlatformPublicBuildJoint.source_state setup wire route sign seed scalar view failure allocation erased helper writer reserve handle application before live correct,
    Functor.map_map]
  have reassociated :
      (restored (RegistrationNativePublicSourceState.roots setup seed scalar) scalar ∘ jointState before) <$>
        joint setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper sign writer reserve
          (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
          (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 =
      nativeResult (RegistrationNativePublicSourceState.roots setup seed scalar) scalar before <$>
        joint setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper sign writer reserve
          (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
          (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro result supported
    have kept := frame setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased helper sign writer reserve
      (RegistrationNativePublicSourceState.roots setup seed scalar) handle application before.1.1.server
      (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2 result supported
    exact congrArg pure (reconstruct _ scalar before result kept.1 kept.2)
  simp only [Function.comp_def] at reassociated
  rw [reassociated]
  have actual := RegistrationNativePlatformServerCompilerJoint.native_marginal setup (RegistrationNativeWire.ledgerCodec wire)
    view failure allocation erased helper sign writer reserve (RegistrationNativePublicSourceState.roots setup seed scalar)
    handle application before.1.1.server (RegistrationWorldAgreementCompiler.join before.1.1.environment before.2.world) before.1.2
  have mapped := congrArg (Functor.map (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
    ({ (RegistrationNativePublicSourceState.restore (RegistrationNativePublicSourceState.roots setup seed scalar) scalar before.1.1 before.2) with server := RegistrationServerMaterialSourceState.nativeView result.1.2 }, result.2)))) actual
  convert mapped using 1 <;> simp only [Functor.map_map, nativeView, RegistrationNativePlatformSourceSeal.build]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative.frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildNative.build_source
