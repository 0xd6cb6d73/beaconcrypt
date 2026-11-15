-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServerSupported
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptPublicCount
/-! The actual returned SDK token drives the public accept reply through the source adapter's successful-session counter. Concrete source normality and the handle representation are derived on the same receipt; no private receipt is exposed to the client continuation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic
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


noncomputable def step {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      self.consumed_registrations identifier = pure (views.replay self.consumed_registrations identifier))
    (allocated : (StateT PlatformState ProbComp) AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {self with consumed_registrations := history})
    (count : Nat) (countEq : count=before.server.sessions.length)
    (previous : PlatformState) (Private : Native×PlatformState →Type)
    (embed : ∀(receipt : AdapterPublicServerReservationReceipt.Receipt R)
      (word : AdapterPublicServerAgreementReceipt.Word R) (sourceAfter : Native) (platformAfter : PlatformState)
      (_supported : (((receipt,.ok word),sourceAfter),platformAfter) ∈ support
        (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous))
      (handle : Option Nat) (nativeAfter : Native),
      project view (AdapterPublicServerAcceptDispatch.charged input before) ((receipt,.ok word),sourceAfter)=.ok (.ok handle,nativeAfter) →
      AdapterPublicServerAgreementPost.Returned view views created credential word (.ok handle,nativeAfter) →
      Private (nativeAfter,platformAfter)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep Private
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$> allocated) route verify model.representation created input) (before,previous)) := by
  let call:=RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Accept.step coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential self input rng before related edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion previous Private embed
  refine {step:=call,observe:=RegistrationNativePlatformExtractedSdkAcceptPublicCount.observe count,normal:=?_,reply:=?_}
  · intro packet supported
    exact RegistrationNativePlatformExtractedSdkAcceptNormal.normal coins setup codec checks route verify edLaws recording writer generator
      view views model entropy created credential self input rng before related edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion previous packet supported
  · rintro ⟨⟨⟨receipt,sourceResult⟩,sourceAfter⟩,platformAfter⟩ supported returned resultEq
    change sourceResult=.ok returned at resultEq
    cases resultEq
    obtain ⟨handle,nativeAfter,projected,materialResult⟩ := RegistrationNativePlatformExtractedSdkServer.Accept.post coins setup codec route verify edLaws recording writer generator self input rng
      view views created credential before sourceAfter related edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
      receipt returned previous platformAfter supported
    have represented:=RegistrationNativePlatformExtractedSdkAcceptPublicCount.represented view views created credential
      (AdapterPublicServerAcceptDispatch.charged input before) ((receipt,.ok returned),sourceAfter) returned handle nativeAfter projected materialResult
    have counter:(AdapterPublicServerAcceptDispatch.charged input before).server.sessions.length=before.server.sessions.length := by
      unfold AdapterPublicServerAcceptDispatch.charged
      cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) <;>rfl
    rw [counter] at represented
    rw [countEq]
    rw [represented]
    dsimp only [call,RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Accept.step]
    simp only [projected]
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic.step
