import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongStep
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongServerSteps
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
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×PlatformState)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (input : Slice U8)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      before.base.objects.server.consumed_registrations identifier = pure (views.replay before.base.objects.server.consumed_registrations identifier))
    (allocated : (StateT PlatformState ProbComp) AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) before.base.objects.server.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views before.base.objects.server.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {before.base.objects.server with consumed_registrations := history})
 :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$>allocated) route verify model.representation created input) current) := by
  let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views setup.joint model entropy
    created credential current before.base input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
  apply RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential call
  intro packet
  rw [RegistrationNativePlatformSdkServerStoreObjects.accept_objects coins setup codec checks route verify edLaws recording writer generator view views setup.joint model entropy
    created credential current before.base input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion packet]
  exact before.otkPublic
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongServerSteps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongServerSteps.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongServerSteps.accept
