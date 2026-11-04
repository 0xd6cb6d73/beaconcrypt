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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuild
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


noncomputable def complete {R : Type}
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
(created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
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
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins)
            (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
            (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure
              (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
              (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned mlSource credential)
              (RegistrationNativePlatformConcreteSource.writer reservePackets)) token.registration (application data))) current) := by
  let previousLocal:=RegistrationNativePlatformPublicAdapterBuildDictionaries.locals (n:=n) view originalLocal
  letI : LocalOperations (RustT SourceM):=previousLocal
  letI : ContainerOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.containers (n:=n) (source:=mlSource) originalContainers
  let previousCrypto:=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (fun query=>StateT.lift (coins query) : QueryImpl unifSpec SourceM) originalCrypto
  letI : CryptoOperations (RustT SourceM):=RegistrationNativePlatformPublicAdapterBuildDictionaries.crypto view previousCrypto
  let fallback (request : registration.MldsaSigningRequest) :NativeM RegistrationSigningShared.SignReply:=
    RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.owned mlSource credential request)))
  apply RegistrationNativePlatformSdkStrongServerBuildStep.complete coins setup codec keyView converted failure allocate reserveFrame erased
    (RegistrationNativeMldsa.owned mlSource credential) reservePackets fallback previousLocal previousChildren view views created credential current before token data
    (RegistrationNativePlatformPublicAdapterPinArrays.parsed view edContract token.registration.agreement.binding.beacon_identity_public_key)
    (fun _=>rfl) (fun _=>rfl) allocated
    (RegistrationNativePlatformPublicAdapterBuildDictionaries.reserve (n:=n) (source:=mlSource) originalContainers before.base.objects.server allocated reserveLeaf)
    footprint
  · intro _current _related identifier
    exact RegistrationNativePlatformPublicAdapterBuildDictionaries.contains originalContainers views before.base.objects.server identifier
      (containsLeaf identifier) _current
  · intro known publication inserting publicKey began parsed
    exact RegistrationNativePlatformPublicAdapterBuildDictionaries.standard (n:=n) (source:=mlSource) originalContainers views
      {before.base.objects.server with known_ids:=known} inserting publicKey (installLeaves known publication inserting publicKey began parsed)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuild.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuild.complete
