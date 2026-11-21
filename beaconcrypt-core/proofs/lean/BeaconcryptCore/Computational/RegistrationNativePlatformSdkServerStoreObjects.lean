import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerSteps
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects
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


omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original localOps containers in
private theorem transport_objects {R : Type}
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (current after : Native×PlatformState)
    (same : current=after)
    (stored : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential after) :
    ((congrArg (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential) same).mpr stored).objects=stored.objects := by
  cases same
  rfl

theorem accept_raw_objects {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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

    (receipt : AdapterPublicServerReservationReceipt.Receipt R) (word : AdapterPublicServerAgreementReceipt.Word R)
    (rawAfter : Native) (platformAfter : PlatformState)
    (supported : (((receipt,.ok word),rawAfter),platformAfter)∈support
      (RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion).step.sample) :
    let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
    (call.step.store (((receipt,.ok word),rawAfter),platformAfter) supported).objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.acceptUpdate before.objects word
        (RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot view views input current.1 (receipt,word) (rawAfter,platformAfter)) := by
  dsimp only [RegistrationNativePlatformSdkServerSteps.accept,RegistrationNativePlatformSdkAcceptInstrumentedSource.step,
    RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic.step,
    RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Accept.step]
  rw [transport_objects]
  · rfl
  · have post:=RegistrationNativePlatformExtractedSdkServer.Accept.post coins setup codec route verify edLaws recording writer generator
      before.objects.server input before.objects.rng view views created credential current.1 rawAfter before.server
      edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion receipt word current.2 platformAfter supported
    have projected:=(Classical.choose_spec (Classical.choose_spec post)).1
    conv_lhs => rw [projected]
    rfl
theorem accept_store_objects {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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

    (receipt : AdapterPublicServerReservationReceipt.Receipt R) (word : AdapterPublicServerAgreementReceipt.Word R)
    (rawAfter : Native) (platformAfter : PlatformState)
    (supported : (((receipt,.ok word),rawAfter),platformAfter)∈support
      (RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion).step.sample) :
    let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
    (RegistrationNativePlatformExtractedSdkPublic.store call ⟨(((receipt,.ok word),rawAfter),platformAfter),supported⟩).objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.acceptUpdate before.objects word
        (RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot view views input current.1 (receipt,word) (rawAfter,platformAfter)) := by
  let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
  have same : RegistrationNativePlatformExtractedSdkPublic.returned call ⟨(((receipt,.ok word),rawAfter),platformAfter),supported⟩=(receipt,word) :=
    (RustM.ok.inj (RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨(((receipt,.ok word),rawAfter),platformAfter),supported⟩)).symm
  dsimp only
  unfold RegistrationNativePlatformExtractedSdkPublic.store
  rw [same]
  exact accept_raw_objects coins setup codec checks route verify edLaws recording writer generator view views joint model entropy
    created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
    receipt word rawAfter platformAfter supported
theorem accept_objects {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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

    (packet : {value // value∈support (RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion).step.sample}) :
    let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.acceptUpdate before.objects
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2
        (RegistrationNativePlatformSdkAcceptInstrumentedSource.sourceSnapshot view views input current.1
          (RegistrationNativePlatformExtractedSdkPublic.returned call packet) (call.step.sourceState packet.val)) := by
  let call:=RegistrationNativePlatformSdkServerSteps.accept coins setup codec checks route verify edLaws recording writer generator view views joint model entropy created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
  have normal:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
  rcases packet with ⟨⟨⟨⟨receipt,word⟩,rawAfter⟩,platformAfter⟩,supported⟩
  change RegistrationNativePlatformSdkAcceptInstrumentedSource.reply receipt word=.ok
    (RegistrationNativePlatformExtractedSdkPublic.returned call ⟨(((receipt,word),rawAfter),platformAfter),supported⟩) at normal
  cases word with
  | fail error | div=>cases normal
  | ok word=>
    have same : RegistrationNativePlatformExtractedSdkPublic.returned call ⟨(((receipt,.ok word),rawAfter),platformAfter),supported⟩=(receipt,word):=
      (RustM.ok.inj normal).symm
    change (RegistrationNativePlatformExtractedSdkPublic.store call ⟨(((receipt,.ok word),rawAfter),platformAfter),supported⟩).objects=_
    rw [same]
    exact accept_store_objects coins setup codec checks route verify edLaws recording writer generator view views joint model entropy
      created credential current before input edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
      receipt word rawAfter platformAfter supported
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects.accept_raw_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects.accept_raw_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects.accept_store_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects.accept_store_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects.accept_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerStoreObjects.accept_objects
