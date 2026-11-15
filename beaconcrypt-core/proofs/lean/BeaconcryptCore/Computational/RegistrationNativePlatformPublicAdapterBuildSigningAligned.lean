-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningDelta
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildLog
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned
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



theorem aligned {R :Type}
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
    (prior :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R Platform)
    (held :RegistrationNativePlatformPublicAdapterBuildSigningDelta.Aligned ((current.1,none),prior))
    (result :(RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves).step.Packet×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R Platform)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterStrongBuildLog.augment coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior).sample)) :
    ((RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves).step.native result.1).2.1.server.world.world.2=
      RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
        (RegistrationNativePlatformPublicAdapterSourceAuthentication.stages result.2) :=by
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (coins query) :QueryImpl unifSpec SourceM) originalCrypto
  let fallback (request :registration.MldsaSigningRequest) :NativeM RegistrationSigningShared.SignReply:=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.owned mlSource credential request)))
  exact RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample_project coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned mlSource credential)
    (RegistrationNativePlatformConcreteSource.writer reservePackets) view originalLocal originalContainers previousCrypto previousChildren fallback
    before.base.objects.server.control before.base.objects.server token data (current.1,none) current.2 prior held result supported

theorem delta {R :Type}
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
    (prior :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R Platform)
    (result :(RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves).step.Packet×RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R Platform)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterStrongBuildLog.augment coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior).sample)) :
    ∃middle :List RegistrationNativePlatformPublicAdapterSourceTrace.Stage,
      result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (coins query) :QueryImpl unifSpec SourceM) originalCrypto
  let fallback (request :registration.MldsaSigningRequest) :NativeM RegistrationSigningShared.SignReply:=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.owned mlSource credential request)))
  exact RegistrationNativePlatformPublicAdapterBuildSigningDelta.sample_delta coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned mlSource credential)
    (RegistrationNativePlatformConcreteSource.writer reservePackets) view originalLocal originalContainers previousCrypto previousChildren fallback
    before.base.objects.server token data (current.1,none) current.2 prior result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned.aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned.delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningAligned.delta
