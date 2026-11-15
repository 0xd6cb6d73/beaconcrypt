import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildStore
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDictionaries
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongServerBuildStep
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerBuildStoreObjects
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildSupportedPublic
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBuildNormal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! The selected Strong SDK Builder derives parsed-token provenance, getters and chronological map-read instrumentation internally from the same actual source objects and individual primitive/container operations. The complete source result and persistent platform state determine its continuation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource
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
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
open AdapterPublicServerBuildPrefix (completion finish admitted project application AllocationReply reserveNative)


theorem source {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(reservePackets : Usize→Base (core.result.Result Unit E))
(originalLocal : LocalOperations (RustT Base))
(originalContainers : ContainerOperations (RustT Base))
(previousChildren : ChildOperations (RustT SourceM))
(view : MaterialView mlSource KemSK) (views : Views)
(created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
(current : Native×Platform)
(before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
(token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
(edContract : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
(allocated : Base AllocationReply)
(reserveLeaf : (originalContainers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
  beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
  hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.base.objects.server.known_ids 1#usize).run=
  RustM.ok <$>allocated)
(footprint : ∀external reply next,(reply,next)∈support (allocated.run external)→PeerReserve views before.base.objects.server.known_ids reply)
(containsLeaf : ∀identifier,(originalContainers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
  beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
  hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
  core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
    (core.borrow.Borrow.Blanket U64)) before.base.objects.server.known_ids identifier).run=
  pure (RustM.ok (views.peer before.base.objects.server.known_ids identifier).isSome))
(installLeaves : let : ContainerOperations (RustT Base):=originalContainers
  ∀known publication inserting publicKey,
  peer.begin_peer_insert before.base.objects.server.control publication=.ok (.Ok inserting)→
  beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice=.ok (.Ok publicKey)→
  AdapterPublicServerInstallFunctional.Standard (m:=Base) views {before.base.objects.server with known_ids:=known} inserting publicKey) :
    let call:=RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves
    Prod.map id RegistrationNativePlatformSdkReification.persistent <$>call.step.sourceCall=
      (fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (((Prod.snd <$>RegistrationNativePlatformPublicAdapterBuildSource.program coins setup codec keyView failure
          (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
          (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
          (RegistrationNativeMldsa.owned mlSource (view.mldsa (platform.arcView before.base.objects.server.identity).mldsa_identity))
          (RegistrationNativePlatformConcreteSource.writer reservePackets) view originalContainers before.base.objects.server token data).run
          (RegistrationNativePlatformSdkReification.backend current.1)).run current.2) := by
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (coins query) :QueryImpl unifSpec SourceM) originalCrypto
  let fallback (request :registration.MldsaSigningRequest) :NativeM RegistrationSigningShared.SignReply:=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.owned mlSource credential request)))
  change Prod.map id RegistrationNativePlatformSdkReification.persistent <$>
    ((fun result=>(result.1.1,(result.1.2.1,result.2))) <$>
    ((RegistrationNativePlatformPublicAdapterBuildSource.nativeSdk coins setup codec keyView failure
      (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
      (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
      (RegistrationNativeMldsa.owned mlSource credential)
      (RegistrationNativePlatformConcreteSource.writer reservePackets) view originalLocal originalContainers previousCrypto previousChildren
      fallback before.base.objects.server token data).run (current.1,none)).run current.2) = _
  have localLaw:=RegistrationNativePlatformPublicAdapterBuildSource.sdk_source coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
    (RegistrationNativeMldsa.owned mlSource credential)
    (RegistrationNativePlatformConcreteSource.writer reservePackets) view originalLocal originalContainers previousCrypto previousChildren
    fallback before.base.objects.server token data (current.1,none)
  have whole:=congrArg (fun computation=>(fun result=>(result.1.1,(result.1.2,result.2))) <$>computation.run current.2) localLaw
  simpa only [StateT.run_map,Functor.map_map,Prod.map,id_eq,RegistrationNativePlatformSdkReification.persistent,before.base.server.identity.mldsa] using whole

theorem objects {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(reservePackets : Usize→Base (core.result.Result Unit E))
(originalLocal : LocalOperations (RustT Base))
(originalContainers : ContainerOperations (RustT Base))
(previousChildren : ChildOperations (RustT SourceM))
(view : MaterialView mlSource KemSK) (views : Views)
(created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
(current : Native×Platform)
(before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
(token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
(edContract : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
(allocated : Base AllocationReply)
(reserveLeaf : (originalContainers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
  beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
  hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.base.objects.server.known_ids 1#usize).run=
  RustM.ok <$>allocated)
(footprint : ∀external reply next,(reply,next)∈support (allocated.run external)→PeerReserve views before.base.objects.server.known_ids reply)
(containsLeaf : ∀identifier,(originalContainers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
  beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
  hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
  core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
    (core.borrow.Borrow.Blanket U64)) before.base.objects.server.known_ids identifier).run=
  pure (RustM.ok (views.peer before.base.objects.server.known_ids identifier).isSome))
(installLeaves : let : ContainerOperations (RustT Base):=originalContainers
  ∀known publication inserting publicKey,
  peer.begin_peer_insert before.base.objects.server.control publication=.ok (.Ok inserting)→
  beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice=.ok (.Ok publicKey)→
  AdapterPublicServerInstallFunctional.Standard (m:=Base) views {before.base.objects.server with known_ids:=known} inserting publicKey)
(packet : {value //value∈support (RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves).step.sample}) :
    let call:=RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      RegistrationNativePlatformExtractedSdkCarrierServer.buildUpdate before.base.objects
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2
        (RegistrationNativePlatformSdkServerReification.snapshot view views
          (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2 none (call.step.sourceState packet.val)) := by
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  let :LocalOperations (RustT SourceM):=previousLocal
  let :ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) originalContainers
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (coins query) :QueryImpl unifSpec SourceM) originalCrypto
  let :CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let fallback (request :registration.MldsaSigningRequest) :NativeM RegistrationSigningShared.SignReply:=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.owned mlSource credential request)))
  obtain ⟨identityKey, copiedIdentity, _⟩ :=
    TranscriptAuthInputsRefinement.identity_public_key_exact token.registration.agreement.binding.init_fields
  let parsed : AdapterPublicServerToken.ParsedToken token :=
    ⟨identityKey, copiedIdentity, RegistrationNativePlatformPublicAdapterPinArrays.parsed view edContract identityKey⟩
  have reserveOperation:=RegistrationNativePlatformPublicAdapterBuildDictionaries.reserve (n:=n) (KemSK:=KemSK) (source:=mlSource) originalContainers before.base.objects.server allocated reserveLeaf
  have containsOperation := fun (_current :Cut) (_related : AdapterPublicWrapperState.Server view views created credential before.base.objects.server _current.1.server) identifier=>
    RegistrationNativePlatformPublicAdapterBuildDictionaries.contains originalContainers views before.base.objects.server identifier (containsLeaf identifier) _current
  have standard := fun known publication inserting publicKey began wasParsed=>
    RegistrationNativePlatformPublicAdapterBuildDictionaries.standard (n:=n) (KemSK:=KemSK) (source:=mlSource) originalContainers views
      {before.base.objects.server with known_ids:=known} inserting publicKey (installLeaves known publication inserting publicKey began wasParsed)
  let baseCall:=RegistrationNativePlatformSdkServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased (RegistrationNativeMldsa.owned mlSource credential) reservePackets fallback previousLocal previousChildren view views created credential setup.joint current before.base token data parsed (fun _=>rfl) (fun _=>rfl) allocated reserveOperation footprint containsOperation standard
  have objectLaw:=RegistrationNativePlatformSdkServerBuildStoreObjects.complete_objects coins setup codec keyView converted failure allocate reserveFrame erased (RegistrationNativeMldsa.owned mlSource credential) reservePackets fallback previousLocal previousChildren view views created credential setup.joint current before.base token data parsed (fun _=>rfl) (fun _=>rfl) allocated reserveOperation footprint containsOperation standard
  have coherent : ∀ p :{value //value∈support baseCall.step.sample},
    RegistrationNativePlatformSdkStrongCarrier.OtkPublic
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) view
      (RegistrationNativePlatformExtractedSdkPublic.store baseCall p).objects.beacons := by
    intro p
    rw [objectLaw p]
    exact before.otkPublic
  change (RegistrationNativePlatformExtractedSdkPublic.store
    (RegistrationNativePlatformSdkStrongStep.of_base setup view views created credential baseCall coherent) packet).base.objects=_
  rw [RegistrationNativePlatformSdkStrongStep.of_base_base]
  exact objectLaw packet

theorem stored {R : Type}
(coins : QueryImpl unifSpec Base) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
(codec : PqxdhServerAuthExperiment.Codec Reader Response)
(keyView : RegistrationNativePlatformSourceSeal.KeyView)
(converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView) (failure : primitive.Error)
(allocate : alloc.vec.Vec U8→Usize→Base (core.result.Result Unit E))
(reserveFrame : Nat→Base (core.result.Result Unit E))
(erased : commitment.CommitmentTranscript)
(reservePackets : Usize→Base (core.result.Result Unit E))
(originalLocal : LocalOperations (RustT Base))
(originalContainers : ContainerOperations (RustT Base))
(previousChildren : ChildOperations (RustT SourceM))
(view : MaterialView mlSource KemSK) (views : Views)
(created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
(current : Native×Platform)
(before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
(token : beaconcrypt_public_wrapper.server.RegistrationOutput) (data : core.option.Option (Slice U8))
(edContract : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
(allocated : Base AllocationReply)
(reserveLeaf : (originalContainers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
  beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
  hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator before.base.objects.server.known_ids 1#usize).run=
  RustM.ok <$>allocated)
(footprint : ∀external reply next,(reply,next)∈support (allocated.run external)→PeerReserve views before.base.objects.server.known_ids reply)
(containsLeaf : ∀identifier,(originalContainers.mapContains core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
  beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
  hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator
  core.U64.Insts.CoreHashHash (hashbrown.Equivalent.Blanket core.U64.Insts.CoreCmpEq
    (core.borrow.Borrow.Blanket U64)) before.base.objects.server.known_ids identifier).run=
  pure (RustM.ok (views.peer before.base.objects.server.known_ids identifier).isSome))
(installLeaves : let : ContainerOperations (RustT Base):=originalContainers
  ∀known publication inserting publicKey,
  peer.begin_peer_insert before.base.objects.server.control publication=.ok (.Ok inserting)→
  beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes inserting.peer.binding.beacon_identity_public_key.to_slice=.ok (.Ok publicKey)→
  AdapterPublicServerInstallFunctional.Standard (m:=Base) views {before.base.objects.server with known_ids:=known} inserting publicKey)
(packet : {value //value∈support (RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves).step.sample}) :
    let call:=RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves
    RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects=
      RegistrationNativePlatformPublicAdapterStore.server
        (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)
        (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2
        (RegistrationNativePlatformPublicAdapterBuildStore.committed view views
          (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2
          (RegistrationNativePlatformSdkReification.persistent (call.step.sourceState packet.val))) := by
  dsimp only
  rw [objects coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves packet,
    RegistrationNativePlatformPublicAdapterStore.server_update,
    RegistrationNativePlatformPublicAdapterBuildStore.snapshot_source]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource.objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource.stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource.stored
