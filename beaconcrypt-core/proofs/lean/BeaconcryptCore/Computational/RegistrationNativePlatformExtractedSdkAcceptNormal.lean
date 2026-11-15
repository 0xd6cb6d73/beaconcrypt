-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAcceptNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServerNormalReflection
/-! Every supported actual common SDK accept receipt returns its actual source word normally. The native normality and failure reflection are applied to the same projected receipt; all source Self, RNG and platform poststates remain in that receipt. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptNormal
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

/-- Actual lifted authentication inside the same parsed-accept administrative entry. -/
theorem normal {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
    (previous : PlatformState)
    (result : ((AdapterPublicServerReservationReceipt.Receipt R×RustM (AdapterPublicServerAgreementReceipt.Word R))×Native)×PlatformState)
    (supported : result∈support (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous)) :
    ∃word,result.1.1.2=.ok word := by
  have law:=RegistrationNativePlatformExtractedSdkServer.Accept.coupled coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential self input rng before related edGetter mlGetter membershipOperation
    allocated allocationOperation footprint insertion
  have projected : (project view (AdapterPublicServerAcceptDispatch.charged input before) result.1,result.2)∈support
      ((project view (AdapterPublicServerAcceptDispatch.charged input before) <$>
        (RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous) := by
    rw [StateT.run_map,support_map]
    exact ⟨result,supported,rfl⟩
  rw [law,StateT.run_map,support_map] at projected
  obtain ⟨nativeResult,called,same⟩ := projected
  obtain ⟨handle,normal⟩ := RegistrationNativePlatformSourceAcceptNormal.dispatch coins setup codec checks
    (AdapterPublicServerSourceLens.admitted <$>allocated) route verify model.representation created edLaws input before previous nativeResult called
  have projectionEq := (congrArg (fun value=>value.1) same).symm
  rcases nativeResult with ⟨⟨nativeReply,nativeAfter⟩,platformAfter⟩
  dsimp only at normal projectionEq
  rw [normal] at projectionEq
  exact RegistrationNativePlatformExtractedSdkServerNormalReflection.accept view
    (AdapterPublicServerAcceptDispatch.charged input before) result.1.2 result.1.1.1 result.1.1.2 handle nativeAfter projectionEq

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptNormal.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAcceptNormal.normal
