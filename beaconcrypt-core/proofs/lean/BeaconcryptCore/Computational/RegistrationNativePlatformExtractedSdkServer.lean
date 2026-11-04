-- SPDX-License-Identifier: 0BSD
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
open BeaconcryptCore.Refinement
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

/-- Actual lifted authentication inside the same parsed-accept administrative entry. -/
noncomputable def native (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT PlatformState ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (input : Slice U8) : NativeM (RustM (Option Nat)) :=
  match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>pure (.ok none)
  | some packet=>do
      modify fun before=>{before with parsedAccepts:=before.parsedAccepts+1}
      RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformExtractedAuthentication.accept coins setup codec route verify checks representation created reserve packet)

omit material platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original localOps containers in
theorem native_current (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT PlatformState ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (input : Slice U8)
    (functional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    native (n:=n) (mlSource:=mlSource) coins setup codec checks reserve route verify representation created input=
      AdapterPublicServerAcceptDispatch.native coins setup codec checks reserve route verify representation created input := by
  unfold native AdapterPublicServerAcceptDispatch.native
  cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>rfl
  | some packet=>
    dsimp only
    rw [RegistrationNativePlatformExtractedAuthentication.accept_source coins setup codec route verify checks representation created functional reserve packet]

noncomputable def run {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R) :=
  AdapterPublicServerAcceptDispatch.entry input (AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng)

theorem sdk {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R) :
    letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    letI : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
    letI : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
    Prod.snd <$> run coins setup codec route verify edLaws recording writer generator self input rng =
      AdapterPublicServerAcceptDispatch.entry input ((beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m := RustT NativeM) generator self input rng).run) := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  exact congrArg (fun work => AdapterPublicServerAcceptDispatch.entry input work)
    (AdapterPublicServerEntryReceipt.sdk coins setup codec route verify edLaws recording writer generator self input rng)

theorem coupled {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {self with consumed_registrations := history}) :
    project view (AdapterPublicServerAcceptDispatch.charged input before) <$>
      ((run coins setup codec route verify edLaws recording writer generator self input rng).run before) =
      RustM.ok <$> (native coins setup codec checks (AdapterPublicServerSourceLens.admitted <$> allocated)
        route verify model.representation created input).run before := by
  have current:=AdapterPublicServerAcceptDispatch.coupled coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential self input rng before related edGetter mlGetter membershipOperation
    allocated allocationOperation footprint insertion
  rw [native_current coins setup codec checks (AdapterPublicServerSourceLens.admitted <$> allocated)
    route verify model.representation created input edLaws]
  exact current

open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt)
open AdapterPublicServerAgreementPost (Returned)
theorem post {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before after : Native) (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations identifier =
        pure (views.replay self.consumed_registrations identifier))
    (allocated : StateT PlatformState ProbComp AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT PlatformState ProbComp) views {self with consumed_registrations := history})
    (receipt : Receipt R) (word : Word R) (previous next : PlatformState)
    (supported : (((receipt, .ok word), after), next) ∈ support
      (((run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous)) :
    ∃ handle nativeAfter, project view (AdapterPublicServerAcceptDispatch.charged input before) ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
      Returned view views created credential word (.ok handle, nativeAfter) := by
  exact AdapterPublicServerAcceptDispatch.post coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential before after related edGetter mlGetter membershipOperation allocated operation footprint insertion
    receipt word previous next supported

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

noncomputable def sourceFinish
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base) :
    RegistrationNativePlatformCompletionSdk.Completion n Base (alloc.vec.Vec U8) :=
  RegistrationNativePlatformSourceBuild.finishSource coins setup codec
    (RegistrationNativePlatformExtractedSourceSeal.sealing coins setup codec keyView failure allocation)
    (RegistrationNativePlatformSourceSeal.hash coins setup codec erased) sign helper writer

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] containers localOps crypto in
theorem finish_current
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base) :
    sourceFinish (n:=n) coins setup codec keyView failure allocation helper erased sign writer=
      finish coins setup codec keyView failure allocation helper erased sign writer := by
  unfold sourceFinish finish
  have same : RegistrationNativePlatformExtractedSourceSeal.sealing (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) coins setup codec keyView failure allocation=
      RegistrationNativePlatformSourceSeal.sealing coins setup codec keyView failure allocation := by
    funext request
    exact RegistrationNativePlatformExtractedSourceSeal.sealing_source coins setup codec keyView failure allocation request
  rw [same]

noncomputable def run [ChildOperations (RustT SourceM)]
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest →NativeM RegistrationSigningShared.SignReply)
(self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8)) :=
  AdapterPublicServerBuildTrace.build (completion coins setup codec keyView failure allocation helper erased sign writer fallback) self token data

omit localOps in
theorem actual
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
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {self with known_ids := known} inserting publicKey) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    (Prod.snd <$> run coins setup codec keyView failure allocation helper erased sign writer fallback self token data =
      (beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT SourceM) self token data).run) ∧
    project self.control <$>
      ((run coins setup codec keyView failure allocation helper erased sign writer fallback self token data).run before) =
      (RegistrationNativePlatformExperiment.server
        (RegistrationNativePlatformCompletionSdk.complete
          (RegistrationNativePlatformSourceBuild.pin coins)
          (admitted <$> StateT.lift allocated)
          (RegistrationNativePlatformCompletionSdk.nativePresent coins)
          (sourceFinish coins setup codec keyView failure allocation helper erased sign writer)
          token.registration (application data))).run before.1 := by
  rw [finish_current coins setup codec keyView failure allocation helper erased sign writer]
  exact AdapterPublicServerBuildNative.actual coins setup codec keyView failure allocation helper erased sign writer fallback previousLocal previousChildren
    view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard

omit localOps in
theorem post
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
    (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
    (after : Cut) (external next : Platform) :
    letI : LocalOperations (RustT SourceM) := AdapterPublicServerCompletionSource.localOperations
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) fallback previousLocal coins setup codec keyView failure allocation helper
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    ((.ok (reply, current), after), next) ∈ support
      ((((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT SourceM) self token data).run).run before).run external) →
    ∃ published, (((published, .ok (reply, current)), after), next) ∈ support
      (((run coins setup codec keyView failure allocation helper erased sign writer fallback self token data).run before).run external) ∧
      AdapterPublicWrapperState.Server view views created credential current
        (project self.control ((published, .ok (reply, current)), after)).2.server := by
  exact AdapterPublicServerBuildPost.actual coins setup codec keyView failure allocation helper erased sign writer fallback previousLocal previousChildren
    view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
    reply current after external next

theorem source_post
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
(allocation : RegistrationNativePlatformSourceSeal.Allocation E Base)
(helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : Server) (before : Cut) (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
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
    (published : Option AdapterPublicServerBuildTrace.Publication)
    (reply : core.option.Option beaconcrypt_public_wrapper.server.RegResponse) (current : Server)
    (after : Cut) (external next : Platform) :
    letI : ChildOperations (RustT SourceM) := AdapterPublicServerCompletionSource.children
      (fun {A} (work : StateT (RegistrationServerRootCompiler.Local n) Base A) => AdapterPublicServerCompletionNative.inCut work)
      (AdapterPublicServerCompletionNative.outgoing coins sign) previousChildren coins setup codec erased
      (AdapterPublicServerCompletionNative.writer writer)
    (((published, .ok (reply, current)), after), next) ∈ support
      (((run coins setup codec keyView failure allocation helper erased sign writer fallback self token data).run before).run external) →
    AdapterPublicWrapperState.Server view views created credential current
      (project self.control ((published, .ok (reply, current)), after)).2.server := by
  exact AdapterPublicServerBuildPost.source coins setup codec keyView failure allocation helper erased sign writer fallback previousChildren
    view views created credential self before related token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
    published reply current after external next

end Build
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.native_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.native_current

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.sdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.coupled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Accept.post

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.finish_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.finish_current

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.actual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.post

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.source_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer.Build.source_post
