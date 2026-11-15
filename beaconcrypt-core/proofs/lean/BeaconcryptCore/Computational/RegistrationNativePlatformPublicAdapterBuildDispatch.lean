-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
/-! Raw response building moves the actual one-use token before any later conversion failure. Missing and consumed handles make no source child call. This local dispatch preserves the stronger retained source-key invariant. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Platform R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
variable (before : StrongCarrier (R:=R) setup view views created credential current)

noncomputable def move (handle : Nat) : StrongCarrier (R:=R) setup view views created credential
    (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) :=
  ⟨RegistrationNativePlatformExtractedSdkCarrier.move view views setup.joint created credential current before.base handle,before.otkPublic⟩

theorem moved_objects (handle : Nat) :
    (move setup view views created credential current before handle).base.objects=
      {before.base.objects with tokens:=Function.update before.base.objects.tokens handle none} := rfl

variable (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (StateT Platform ProbComp))
variable (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp)
  (RustM (core.option.Option session.ServerAuthenticationPin)))
variable (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
variable (present : U64 →StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
variable (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT Platform ProbComp) (alloc.vec.Vec U8))

noncomputable def missing (handle : Nat) (absent : before.base.objects.tokens handle=none) (application : Option (Slice U8)) :
    TotalStep (StrongCarrier (R:=R) setup view views created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application)) current) := by
  rw [RegistrationNativePlatformExtractedSdkBuildDispatch.missing_model view views setup.joint created credential current before.base deriveAd pin reserve present finish handle absent application]
  exact {
    step:={
      Packet:=Unit
      sample:=pure ()
      sourceType:=core.option.Option beaconcrypt_public_wrapper.server.RegResponse ×beaconcrypt_public_wrapper.server.Server
      sourceReply:=fun _=>.ok (.None,before.base.objects.server)
      sourceState:=fun _=>before.base.objects.snapshot.committed
      sourceCall:=pure (.ok (.None,before.base.objects.server),before.base.objects.snapshot.committed)
      source_exact:=rfl
      native:=fun _=>(.ok none,current)
      native_exact:=rfl
      store:=fun _ _=>before }
    observe:=fun _=>.ok none
    normal:=fun _ _=>⟨_,rfl⟩
    reply:=fun _ _ _ _=>rfl }

noncomputable def cancel (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.base.objects.tokens handle=some token) :
    TotalStep (StrongCarrier (R:=R) setup view views created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle none)) current) := by
  rw [RegistrationNativePlatformExtractedSdkBuildDispatch.cancel_model view views setup.joint created credential current before.base deriveAd pin reserve present finish handle token stored]
  exact {
    step:={
      Packet:=Unit
      sample:=pure ()
      sourceType:=core.option.Option beaconcrypt_public_wrapper.server.RegResponse ×beaconcrypt_public_wrapper.server.Server
      sourceReply:=fun _=>.ok (.None,before.base.objects.server)
      sourceState:=fun _=>before.base.objects.snapshot.committed
      sourceCall:=pure (.ok (.None,before.base.objects.server),before.base.objects.snapshot.committed)
      source_exact:=rfl
      native:=fun _=>(.ok none,(AdapterPublicServerBuildOwnership.moved handle current.1,current.2))
      native_exact:=rfl
      store:=fun _ _=>move setup view views created credential current before handle }
    observe:=fun _=>.ok none
    normal:=fun _ _=>⟨_,rfl⟩
    reply:=fun _ _ _ _=>rfl }

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.move
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.moved_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.moved_objects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch.cancel
