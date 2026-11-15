-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource
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


abbrev Word (R : Type) := AdapterPublicServerReservationReceipt.Receipt R ×AdapterPublicServerAgreementReceipt.Word R

def reply {R : Type} (receipt : AdapterPublicServerReservationReceipt.Receipt R)
    (word : RustM (AdapterPublicServerAgreementReceipt.Word R)) : RustM (Word R) :=
  match word with | .ok value=>.ok (receipt,value) | .fail error=>.fail error | .div=>.div

def erase {R : Type} (word : RustM (Word R)) : RustM (AdapterPublicServerAgreementReceipt.Word R) :=
  Prod.snd <$>word
noncomputable def source {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R)
    (before : Native) (previous : PlatformState) :=
  (fun packet=>(reply packet.1.1.1 packet.1.1.2,(packet.1.2,packet.2))) <$>
    (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous)
noncomputable def sourceSnapshot {R : Type}
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (input : Slice U8) (before : Native) (returned : Word R) (after : Native×PlatformState) :=
  RegistrationNativePlatformSdkServerReification.snapshot view views returned.2.2.1
    (RegistrationNativePlatformSdkServerReification.acceptEnvironment view
      (AdapterPublicServerAcceptDispatch.charged input before) returned.1) after

theorem erasure {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R) (before : Native) (previous : PlatformState) :
    let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
    let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
    Prod.map erase id <$>source coins setup codec route verify edLaws recording writer generator self input rng before previous =
      (fun packet=>(packet.1.1,(packet.1.2,packet.2))) <$>
        (((AdapterPublicServerAcceptDispatch.entry input
          ((beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m := RustT NativeM) generator self input rng).run)).run before).run previous) := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  have law:=RegistrationNativePlatformExtractedSdkServer.Accept.sdk coins setup codec route verify edLaws recording writer generator self input rng
  have called:=congrArg (fun work=>((work.run before).run previous)) law
  have arranged:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>work) called
  calc
    _ = (fun packet=>(packet.1.1.2,(packet.1.2,packet.2))) <$>
        (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous) := by
      simp only [source,Functor.map_map]
      apply congrArg (fun function=>function <$> _)
      funext packet
      rcases packet with ⟨⟨⟨receipt,word⟩,raw⟩,platformAfter⟩
      cases word <;> rfl
    _ = _ := by
      simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged
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
  let old:=RegistrationNativePlatformExtractedSdkAdaptiveAcceptSupportedPublic.step coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential self input rng before related edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion count countEq previous Private embed
  let call : RegistrationNativePlatformExtractedSdkAdaptive.Step Private
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$> allocated) route verify model.representation created input) (before,previous)) := {
    Packet:=old.step.Packet
    sample:=old.step.sample
    sourceType:=Word R
    sourceReply:=fun packet=>reply packet.1.1.1 packet.1.1.2
    sourceState:=old.step.sourceState
    sourceCall:=source coins setup codec route verify edLaws recording writer generator self input rng before previous
    source_exact:=rfl
    native:=old.step.native
    native_exact:=old.step.native_exact
    store:=by
      rintro ⟨⟨⟨receipt,word⟩,rawAfter⟩,platformAfter⟩ supported
      cases word with
      | fail error | div=>exact PUnit.unit
      | ok word=>exact old.step.store (((receipt,.ok word),rawAfter),platformAfter) supported }
  refine {step:=call,observe:=fun returned=>old.observe returned.2,normal:=?_,reply:=?_}
  · rintro ⟨⟨⟨receipt,word⟩,rawAfter⟩,platformAfter⟩ supported
    obtain ⟨returned,resultEq⟩:=old.normal (((receipt,word),rawAfter),platformAfter) supported
    change word=.ok returned at resultEq
    cases resultEq
    exact ⟨(receipt,returned),rfl⟩
  · rintro ⟨⟨⟨receipt,word⟩,rawAfter⟩,platformAfter⟩ supported returned resultEq
    change reply receipt word=.ok returned at resultEq
    cases word with
    | fail error | div=>cases resultEq
    | ok word=>
      have same : (receipt,word)=returned:=RustM.ok.inj resultEq
      cases same
      exact old.reply (((receipt,.ok word),rawAfter),platformAfter) supported word rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource.erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptInstrumentedSource.step
