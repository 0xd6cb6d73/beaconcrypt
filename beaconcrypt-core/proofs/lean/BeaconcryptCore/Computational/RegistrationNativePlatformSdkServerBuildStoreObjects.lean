import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStep
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! The concrete reached SDK builder obtains its public response directly from the same normal source return. Its continuation retains the actual supported raw receipt and complete source/platform poststate. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects
open BeaconcryptCore.Refinement
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
theorem complete_raw_objects {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(reservePackets : Usize→Base (core.result.Result Unit E))
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (joint : PqxdhJointIdentity.Primitives) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (previousLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.objects.server.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views before.objects.server.known_ids reply)
    (containsOperation : ∀ (current : Cut),
      AdapterPublicWrapperState.Server view views created credential before.objects.server current.1.server →
      ∀ identifier,
      ((containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) before.objects.server.known_ids identifier).run).run current =
      pure (.ok (views.peer before.objects.server.known_ids identifier).isSome,
        ({current.1 with server := AdapterPublicServerPresenceNative.charged current.1.server identifier}, current.2)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert before.objects.server.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {before.objects.server with known_ids := known} inserting publicKey)

    (publication : Option AdapterPublicServerBuildTrace.Publication) (word : AdapterPublicServerBuildBody.Reply)
    (rawAfter : Cut) (platformAfter : Platform)
    (supported : (((publication,.ok word),rawAfter),platformAfter)∈support
      (RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard).step.sample) :
    let call:=RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
    (call.step.store (((publication,.ok word),rawAfter),platformAfter) supported).objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.buildUpdate before.objects word.2
        (RegistrationNativePlatformSdkServerReification.snapshot view views word.2 none (rawAfter.1,platformAfter)) := by
  dsimp only [RegistrationNativePlatformSdkServerBuildStep.complete,
    RegistrationNativePlatformExtractedSdkBuildSupportedPublic.step,
    RegistrationNativePlatformExtractedSdkAdaptiveServerSupported.Build.step]
  rfl
omit localOps in
theorem complete_store_objects {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(reservePackets : Usize→Base (core.result.Result Unit E))
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (joint : PqxdhJointIdentity.Primitives) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (previousLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.objects.server.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views before.objects.server.known_ids reply)
    (containsOperation : ∀ (current : Cut),
      AdapterPublicWrapperState.Server view views created credential before.objects.server current.1.server →
      ∀ identifier,
      ((containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) before.objects.server.known_ids identifier).run).run current =
      pure (.ok (views.peer before.objects.server.known_ids identifier).isSome,
        ({current.1 with server := AdapterPublicServerPresenceNative.charged current.1.server identifier}, current.2)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert before.objects.server.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {before.objects.server with known_ids := known} inserting publicKey)

    (publication : Option AdapterPublicServerBuildTrace.Publication) (word : AdapterPublicServerBuildBody.Reply)
    (rawAfter : Cut) (platformAfter : Platform)
    (supported : (((publication,.ok word),rawAfter),platformAfter)∈support
      (RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard).step.sample) :
    let call:=RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
    (RegistrationNativePlatformExtractedSdkPublic.store call ⟨(((publication,.ok word),rawAfter),platformAfter),supported⟩).objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.buildUpdate before.objects word.2
        (RegistrationNativePlatformSdkServerReification.snapshot view views word.2 none (rawAfter.1,platformAfter)) := by
  let call:=RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
  have same : RegistrationNativePlatformExtractedSdkPublic.returned call ⟨(((publication,.ok word),rawAfter),platformAfter),supported⟩=word :=
    (RustM.ok.inj (RegistrationNativePlatformExtractedSdkPublic.returned_exact call ⟨(((publication,.ok word),rawAfter),platformAfter),supported⟩)).symm
  dsimp only
  unfold RegistrationNativePlatformExtractedSdkPublic.store
  rw [same]
  exact complete_raw_objects coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback
    previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated
    reserveOperation footprint containsOperation standard publication word rawAfter platformAfter supported
omit localOps in
theorem complete_objects {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
(reservePackets : Usize→Base (core.result.Result Unit E))
(fallback : registration.MldsaSigningRequest → NativeM RegistrationSigningShared.SignReply)

    (previousLocal : LocalOperations (RustT SourceM))
    (previousChildren : ChildOperations (RustT SourceM))
    (view : MaterialView mlSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (joint : PqxdhJointIdentity.Primitives) (current : Native×Platform)
    (before : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views joint created credential current)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
    (parsed : AdapterPublicServerToken.ParsedToken token)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (previousLocal.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (allocated : Base AllocationReply)
    (reserveOperation : (containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
      beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
      hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.objects.server.known_ids 1#usize).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ external reply next, (reply, next) ∈ support (allocated.run external) → PeerReserve views before.objects.server.known_ids reply)
    (containsOperation : ∀ (current : Cut),
      AdapterPublicWrapperState.Server view views created credential before.objects.server current.1.server →
      ∀ identifier,
      ((containers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
        beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
        hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
        core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
          (core.borrow.Borrow.Blanket U64)) before.objects.server.known_ids identifier).run).run current =
      pure (.ok (views.peer before.objects.server.known_ids identifier).isSome,
        ({current.1 with server := AdapterPublicServerPresenceNative.charged current.1.server identifier}, current.2)))
    (standard : ∀ known publication inserting publicKey,
      peer.begin_peer_insert before.objects.server.control publication = .ok (.Ok inserting) →
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := SourceM) views {before.objects.server with known_ids := known} inserting publicKey)

    (packet : {value //value∈support (RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard).step.sample}) :
    let call:=RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.buildUpdate before.objects
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2
        (RegistrationNativePlatformSdkServerReification.snapshot view views
          (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2 none (call.step.sourceState packet.val)) := by
  let call:=RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated reserveOperation footprint containsOperation standard
  have normal:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
  rcases packet with ⟨⟨⟨⟨publication,word⟩,rawAfter⟩,platformAfter⟩,supported⟩
  change word=.ok (RegistrationNativePlatformExtractedSdkPublic.returned call ⟨(((publication,word),rawAfter),platformAfter),supported⟩) at normal
  cases word with
  | fail error | div=>cases normal
  | ok word=>
    have same : RegistrationNativePlatformExtractedSdkPublic.returned call ⟨(((publication,.ok word),rawAfter),platformAfter),supported⟩=word:=(RustM.ok.inj normal).symm
    change (RegistrationNativePlatformExtractedSdkPublic.store call ⟨(((publication,.ok word),rawAfter),platformAfter),supported⟩).objects=_
    rw [same]
    exact complete_store_objects coins setup codec keyView converted failure allocate reserveFrame erased sign reservePackets fallback
      previousLocal previousChildren view views created credential joint current before token data parsed edGetter mlGetter allocated
      reserveOperation footprint containsOperation standard publication word rawAfter platformAfter supported
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects.complete_raw_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects.complete_raw_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects.complete_store_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects.complete_store_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects.complete_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects.complete_objects
