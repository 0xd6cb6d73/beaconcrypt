-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalMetricView
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptMetricView
/-! Every actual source build leaf and the complete moved-token SDK body ignores only the named instrumentation view. Source allocation and serialization retain arbitrary shared effects, and native signatures retain true uniform costs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildMetricView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerMaterialSourceState (nativeView)
open RegistrationStateView (Stable)
variable {n : Nat} {I KemSK Reader Response E A : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [primitive : AdapterSealPrimitive.Operations]

omit primitive in
private theorem external (work : m A) : Stable (nativeView (n := n)) (StateT.lift work) := by
  intro before
  simp only [StateT.run_lift, map_bind, map_pure, nativeView, Prod.map_def, id_eq, RegistrationNativeLocalView.project_idempotent]

omit primitive in
private theorem present (coins : QueryImpl unifSpec m) (keyId : U64) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId) := by
  apply RegistrationNativePlatformSdkMetricView.world
  intro before
  have actual := congrArg (simulateQ coins) (RegistrationNativeLocalView.capability_input (.peerPresent keyId) before)
  simpa only [RegistrationNativePlatformServerCompletion.capability,
    RegistrationNativePlatformServerCompletion.liftNative, StateT.run, simulateQ_map] using actual

omit primitive in
private theorem adHash (coins : QueryImpl unifSpec m) (pending : registration.ServerAdHash) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending) := by
  apply RegistrationNativePlatformSdkMetricView.world
  exact RegistrationNativePlatformSourceLocalMetricView.adHash coins pending

/-- The literal actual source build is stable on its complete Native/P execution, preserving true uniforms and all operational fields. -/
theorem build (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E m) (erased : commitment.CommitmentTranscript)
    (reserve : m Bool) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (handle : Nat) (application : Option (Slice U8)) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reserve sign helper writer handle application) := by
  unfold RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformSourceBuild.buildSource
  exact RegistrationNativePlatformSdkMetricView.build _ (adHash coins) _ _ _ _
    (RegistrationNativePlatformSourceAcceptMetricView.pin coins) (external reserve) (present coins)
    (RegistrationNativePlatformSourceLocalMetricView.finish coins setup codec view failure allocation erased sign helper writer) handle application
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildMetricView.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildMetricView.build
