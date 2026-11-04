-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The public native build adapter moves the same opaque source token associated with its native successful-session handle. Missing and already moved tokens reject without calling an SDK child. Failed raw application conversion consumes that token before returning None. The live branch is the exact completion model of the actual SDK common runner. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkAdaptive (Step)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
variable {n : Nat} {KemSK Platform R : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (before : Carrier (R:=R) view containers joint created credential current)
variable (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp)
    (RustM (core.option.Option session.ServerAuthenticationPin)))
variable (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
variable (present : U64 →StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
variable (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT Platform ProbComp) (alloc.vec.Vec U8))

theorem live_model (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) (application : Slice U8) :
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle (some application))) current=
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token.registration application))
      (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) := by
  have same:=RegistrationNativePlatformExtractedSdkCarrier.build_live view containers joint created credential current before pin reserve present finish handle token stored application
  simp only [StateT.run] at same
  simp only [RegistrationNativePlatformPackedState.pack,RegistrationNativePlatformExperiment.server,StateT.run]
  rw [same]
  rfl

noncomputable def live (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) (application : Slice U8)
    (call : TotalStep (Carrier (R:=R) view containers joint created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token.registration application))
        (AdapterPublicServerBuildOwnership.moved handle current.1,current.2))) :
    TotalStep (Carrier (R:=R) view containers joint created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle (some application))) current) := by
  rw [live_model view containers joint created credential current before pin reserve present finish handle token stored application]
  exact call

theorem missing_model (handle : Nat) (missing : before.objects.tokens handle=none) (application : Option (Slice U8)) :
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application)) current=
      pure (.ok none,current) := by
  have same:=RegistrationNativePlatformExtractedSdkCarrier.build_missing view containers joint created credential current before pin reserve present finish handle missing application
  simp only [StateT.run] at same
  simp only [RegistrationNativePlatformPackedState.pack,RegistrationNativePlatformExperiment.server,StateT.run]
  rw [same]
  rfl

theorem cancel_model (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) :
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle none)) current=
      pure (.ok none,(AdapterPublicServerBuildOwnership.moved handle current.1,current.2)) := by
  have same:=RegistrationNativePlatformExtractedSdkCarrier.build_cancel view containers joint created credential current before pin reserve present finish handle token stored
  simp only [StateT.run] at same
  simp only [RegistrationNativePlatformPackedState.pack,RegistrationNativePlatformExperiment.server,StateT.run]
  rw [same]
  rfl
noncomputable def missing (handle : Nat) (absent : before.objects.tokens handle=none) (application : Option (Slice U8)) :
    TotalStep (Carrier (R:=R) view containers joint created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application)) current) := by
  rw [missing_model view containers joint created credential current before pin reserve present finish handle absent application]
  refine {step:={
      Packet:=Unit
      sample:=pure ()
      sourceType:=core.option.Option beaconcrypt_public_wrapper.server.RegResponse ×beaconcrypt_public_wrapper.server.Server
      sourceReply:=fun _=>.ok (.None,before.objects.server)
      sourceState:=fun _=>before.objects.snapshot.raw
      sourceCall:=pure (.ok (.None,before.objects.server),before.objects.snapshot.raw)
      source_exact:=rfl
      native:=fun _=>(.ok none,current)
      native_exact:=rfl
      store:=fun _ _=>before},observe:=fun _=>.ok none,normal:=?_,reply:=?_}
  · intro packet supported
    exact ⟨_,rfl⟩
  · intro packet supported returned resultEq
    rfl

noncomputable def cancel (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) :
    TotalStep (Carrier (R:=R) view containers joint created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle none)) current) := by
  rw [cancel_model view containers joint created credential current before pin reserve present finish handle token stored]
  refine {step:={
      Packet:=Unit
      sample:=pure ()
      sourceType:=core.option.Option beaconcrypt_public_wrapper.server.RegResponse ×beaconcrypt_public_wrapper.server.Server
      sourceReply:=fun _=>.ok (.None,before.objects.server)
      sourceState:=fun _=>before.objects.snapshot.raw
      sourceCall:=pure (.ok (.None,before.objects.server),before.objects.snapshot.raw)
      source_exact:=rfl
      native:=fun _=>(.ok none,(AdapterPublicServerBuildOwnership.moved handle current.1,current.2))
      native_exact:=rfl
      store:=(fun _ _=>RegistrationNativePlatformExtractedSdkCarrier.move view containers joint created credential current before handle)},observe:=fun _=>.ok none,normal:=?_,reply:=?_}
  · intro packet supported
    exact ⟨_,rfl⟩
  · intro packet supported returned resultEq
    rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.live_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.live_model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.missing_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.missing_model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.cancel_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.cancel_model

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildDispatch.cancel
