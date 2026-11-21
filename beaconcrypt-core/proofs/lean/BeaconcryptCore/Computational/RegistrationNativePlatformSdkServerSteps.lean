-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptReification
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch
import BeaconcryptCore.Refinement.AdapterPublicServerBuildNative
import BeaconcryptCore.Refinement.AdapterPublicServerBuildPost
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal
/-! Genuine current extracted SDK Server acceptance and response-building share their analysis-instrumented source execution with the corrected native callback. Source Self/RNG/errors and the complete persistent primitive/platform state are retained. Contracts concern only individual primitive/getter/storage/allocation leaves. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerSteps
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerReservationNative (project AllocationReply)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response PlatformState : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource (StateT PlatformState ProbComp)
attribute [local irreducible] RegistrationAuthenticationExecutor.begin
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]

local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource


noncomputable def accept {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×PlatformState)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (input : Slice U8)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      before.objects.server.consumed_registrations identifier = pure (views.replay before.objects.server.consumed_registrations identifier))
    (allocated : (StateT PlatformState ProbComp) AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) before.objects.server.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views before.objects.server.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {before.objects.server with consumed_registrations := history})
 :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$>allocated) route verify model.representation created input) current) := by
  let Private : Native×PlatformState→Type:=RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential
  apply RegistrationNativePlatformSdkAcceptInstrumentedSource.step coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential before.objects.server input before.objects.rng current.1 before.server
    edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
    before.objects.nextSession before.sessionCount current.2 Private
  intro receipt word rawAfter platformAfter supported handle nativeAfter projected returned
  let witness:=RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Accept.step coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential before.objects.server input before.objects.rng current.1 before.server
    edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion current.2 (fun _=>PUnit)
    (fun _ _ _ _ _ _ _ _ _=>PUnit.unit)
  have reached:=RegistrationNativePlatformSdkBeaconFrame.step_support witness (((receipt,.ok word),rawAfter),platformAfter) supported
  have projection : witness.native (((receipt,.ok word),rawAfter),platformAfter)=(.ok handle,(nativeAfter,platformAfter)) := by
    dsimp only [witness,RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Accept.step]
    simp only [projected]
    rfl
  rw [projection] at reached
  have actual : ((.ok handle,nativeAfter),platformAfter)∈support
      (((RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
        (AdapterPublicServerSourceLens.admitted <$>allocated) route verify model.representation created input).run current.1).run current.2) := by
    rw [RegistrationNativePlatformPackedState.pack,support_map] at reached
    obtain ⟨⟨⟨reply,after⟩,next⟩,called,equal⟩:=reached
    simp only [Prod.mk.injEq] at equal
    obtain ⟨replyEq,afterEq,platformEq⟩:=equal
    cases replyEq
    cases afterEq
    cases platformEq
    exact called
  have shape:=RegistrationNativePlatformSdkAcceptSessions.native coins setup codec checks
    (AdapterPublicServerSourceLens.admitted <$>allocated) route verify model.representation created edLaws input current.1 current.2 _ actual
  have frame:=RegistrationNativePlatformSdkBeaconFrame.accept coins setup codec checks
    (AdapterPublicServerSourceLens.admitted <$>allocated) route verify model.representation created edLaws input current.1 current.2 _ actual
  have backend:=RegistrationNativePlatformSdkAcceptReification.accepted coins setup codec route verify edLaws recording writer generator
    before.objects.server input before.objects.rng view views created credential current.1 rawAfter before.server
    edGetter mlGetter membershipOperation allocated allocationOperation insertion receipt word current.2 platformAfter supported
    (.ok handle) nativeAfter projected returned
  exact RegistrationNativePlatformExtractedSdkCarrierServer.acceptPut view views joint created credential current before word handle nativeAfter platformAfter
    returned shape frame (RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot view views input current.1 (receipt,word) (rawAfter,platformAfter)) backend
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerSteps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerSteps.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerSteps.accept
