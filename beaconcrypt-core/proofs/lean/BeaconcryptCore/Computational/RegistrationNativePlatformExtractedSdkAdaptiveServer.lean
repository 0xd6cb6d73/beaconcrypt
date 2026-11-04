-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
/-! Actual SDK Server steps instantiate the support-certified adaptive source runner. Raw SDK snapshots remain separate from projected native states; normal continuations receive only the actual returned source object and proved material relation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer
open BeaconcryptCore.Refinement
private def totalize {Reply N : Type} (fallback : Reply×N) : RustM (Reply×N) →Reply×N
  | .ok value=>value
  | .fail _ | .div=>fallback
private def withPlatform {Reply N Platform : Type} (value : RustM (Reply×N) ×Platform) : RustM (Reply×(N×Platform)) := do
  let returned←value.1
  .ok (returned.1,(returned.2,value.2))
private theorem totalize_exact {Packet Reply N : Type} (sampled : ProbComp Packet)
    (model : ProbComp (Reply×N)) (projectionResult : Packet →RustM (Reply×N)) (fallback : Reply×N)
    (same : projectionResult <$>sampled=RustM.ok <$>model) :
    (fun packet=>totalize fallback (projectionResult packet)) <$>sampled=model := by
  have mapped:=congrArg (fun work=>totalize fallback <$>work) same
  simp only [Functor.map_map,totalize] at mapped
  exact mapped.trans (id_map model)
namespace Accept
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
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
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
    (previous : PlatformState) (Private : Native×PlatformState →Type)
    (embed : ∀(receipt : AdapterPublicServerReservationReceipt.Receipt R)
      (word : AdapterPublicServerAgreementReceipt.Word R) (sourceAfter : Native) (platformAfter : PlatformState)
      (handle : Option Nat) (nativeAfter : Native),
      project view (AdapterPublicServerAcceptDispatch.charged input before) ((receipt,.ok word),sourceAfter)=.ok (.ok handle,nativeAfter) →
      AdapterPublicServerAgreementPost.Returned view views created credential word (.ok handle,nativeAfter) →
      Private (nativeAfter,platformAfter)) :
    RegistrationNativePlatformExtractedSdkAdaptive.Step Private
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$> allocated) route verify model.representation created input) (before,previous)) := by
  letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  letI : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  letI : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  let sampled:=((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous
  let projectionResult (packet : ((AdapterPublicServerReservationReceipt.Receipt R ×RustM (AdapterPublicServerAgreementReceipt.Word R))×Native)×PlatformState) :=
    withPlatform (project view (AdapterPublicServerAcceptDispatch.charged input before) packet.1,packet.2)
  let fallback : RustM (Option Nat) ×(Native×PlatformState):=(.ok none,(before,previous))
  have partialExact : projectionResult <$> sampled=RustM.ok <$>
      RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExtractedSdkServer.Accept.native coins setup codec checks
          (AdapterPublicServerSourceLens.admitted <$> allocated) route verify model.representation created input) (before,previous) := by
    have law:=RegistrationNativePlatformExtractedSdkServer.Accept.coupled coins setup codec checks route verify edLaws recording writer generator
      view views model entropy created credential self input rng before related edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
    have called:=congrArg (fun work=>work.run previous) law
    have lifted:=congrArg (fun work=>withPlatform <$> work) called
    simpa only [sampled,projectionResult,RegistrationNativePlatformPackedState.pack,StateT.run_map,Functor.map_map,withPlatform,bind_tc_ok] using lifted
  refine {
    Packet:=((AdapterPublicServerReservationReceipt.Receipt R ×RustM (AdapterPublicServerAgreementReceipt.Word R))×Native)×PlatformState
    sample:=sampled
    sourceType:=AdapterPublicServerAgreementReceipt.Word R
    sourceReply:=fun packet=>packet.1.1.2
    sourceState:=fun packet=>(packet.1.2,packet.2)
    sourceCall:=(fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (((AdapterPublicServerAcceptDispatch.entry input
        ((beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m:=RustT NativeM) generator self input rng).run)).run before).run previous)
    source_exact:=?_
    native:=fun packet=>totalize fallback (projectionResult packet)
    native_exact:=totalize_exact sampled _ projectionResult fallback partialExact
    store:=?_ }
  · have law:=RegistrationNativePlatformExtractedSdkServer.Accept.sdk coins setup codec route verify edLaws recording writer generator self input rng
    have called:=congrArg (fun work=>((work.run before).run previous)) law
    have arranged:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>work) called
    simpa only [sampled,StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged
  · rintro ⟨⟨⟨receipt,word⟩,sourceAfter⟩,platformAfter⟩ supported
    cases word with
    | fail error | div=>exact PUnit.unit
    | ok word=>
      have post:=RegistrationNativePlatformExtractedSdkServer.Accept.post coins setup codec route verify edLaws recording writer generator self input rng
        view views created credential before sourceAfter related edGetter mlGetter membershipOperation allocated allocationOperation footprint insertion
        receipt word previous platformAfter supported
      let handle:=Classical.choose post
      let nativeAfter:=Classical.choose (Classical.choose_spec post)
      have projected:=(Classical.choose_spec (Classical.choose_spec post)).1
      have returned:=(Classical.choose_spec (Classical.choose_spec post)).2
      have sameNative : (totalize fallback (projectionResult (((receipt,.ok word),sourceAfter),platformAfter))).2=(nativeAfter,platformAfter) :=
        congrArg (fun value=>(totalize fallback (withPlatform (value,platformAfter))).2) projected
      exact (congrArg Private sameNative).mpr
        (embed receipt word sourceAfter platformAfter handle nativeAfter projected returned)

end Accept
namespace Build
open BeaconcryptCore.Computational
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open AdapterPublicServerBuildBody (Server Reply)
variable {n : Nat} {KemSK Platform E I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "Cut" => RegistrationNativePlatformCutJournal.State Native
local notation "Base" => StateT Platform ProbComp
local notation "NativeM" => StateT Native Base
local notation "SourceM" => StateT Cut Base
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [primitive : AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]

variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State
  (RegistrationNativeExperiment.State n KemSK mlSource)) (StateT Platform ProbComp)))]
open AdapterPublicServerBuildPrefix (completion finish admitted project application AllocationReply reserveNative)

omit localOps in
noncomputable def step
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (previousLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views self.known_ids reply)
    (containsOperation : ∀ identifier,
      (containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) self.known_ids identifier).run =
      RustM.ok <$> RegistrationNativePlatformCutErasure.liftWorld
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.nativePresent coins identifier)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert self.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey)
    (previous : Platform) (Private : Native×Platform →Type)
    (embed : ∀(publication : Option AdapterPublicServerBuildTrace.Publication)
      (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
      (sourceAfter : Cut) (platformAfter : Platform),
      AdapterPublicWrapperState.Server view views created credential current
        (project self.control ((publication,.ok (reply,current)),sourceAfter)).2.server →
      Private ((project self.control ((publication,.ok (reply,current)),sourceAfter)).2,platformAfter)) :
    RegistrationNativePlatformExtractedSdkAdaptive.Step Private
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
            (admitted <$> StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
            (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure allocation helper erased sign writer)
            token.registration (application data))) (before.1,previous)) := by
  letI selectedLocal : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
  letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
    (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A)=>AdapterPublicServerCompletionNative.inCut work)
    (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
    (AdapterPublicServerCompletionNative.writer writer)
  let sampled:=((RegistrationNativePlatformExtractedSdkServer.Build.run coins setup codec keyView failure allocation helper erased sign writer fallback self token data).run before).run previous
  have law:=RegistrationNativePlatformExtractedSdkServer.Build.actual coins setup codec keyView failure allocation helper erased sign writer fallback previousLocal previousChildren
    view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
  refine {
    Packet:=(AdapterPublicServerBuildTrace.Word×Cut)×Platform
    sample:=sampled
    sourceType:=Reply
    sourceReply:=fun packet=>packet.1.1.2
    sourceState:=fun packet=>(packet.1.2.1,packet.2)
    sourceCall:=(fun result=>(result.1.1,(result.1.2.1,result.2))) <$>
      ((((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m:=RustT SourceM) self token data).run).run before).run previous)
    source_exact:=?_
    native:=fun packet=>let result:=project self.control packet.1;(result.1,(result.2,packet.2))
    native_exact:=?_
    store:=?_ }
  · have called:=congrArg (fun work=>((work.run before).run previous)) law.1
    have arranged:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2.1,result.2))) <$>work) called
    simpa only [sampled,StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged
  · have called:=congrArg (fun work=>work.run previous) law.2
    have arranged:=congrArg (fun work=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>work) called
    simpa only [sampled,RegistrationNativePlatformPackedState.pack,StateT.run_map,Functor.map_map,Prod.map,id_eq] using arranged
  · rintro ⟨⟨⟨publication,word⟩,sourceAfter⟩,platformAfter⟩ supported
    cases word with
    | fail error | div=>exact PUnit.unit
    | ok word=>
      rcases word with ⟨reply,current⟩
      have held:=RegistrationNativePlatformExtractedSdkServer.Build.source_post (localOps:=selectedLocal) coins setup codec keyView failure allocation helper erased sign writer fallback previousChildren
        view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
        publication reply current sourceAfter previous platformAfter supported
      exact embed publication reply current sourceAfter platformAfter held

end Build
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer.Accept.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer.Accept.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer.Build.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveServer.Build.step
