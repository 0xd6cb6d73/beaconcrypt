import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw
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


noncomputable def modelCast {N Reply :Type} {Private :N →Type}
    {left right :ProbComp (Reply×N)} (same :left=right)
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep Private left) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep Private right := {
  step:={
    Packet:=call.step.Packet
    sample:=call.step.sample
    sourceType:=call.step.sourceType
    sourceReply:=call.step.sourceReply
    sourceState:=call.step.sourceState
    sourceCall:=call.step.sourceCall
    source_exact:=call.step.source_exact
    native:=call.step.native
    native_exact:=call.step.native_exact.trans same
    store:=call.step.store }
  observe:=call.observe
  normal:=call.normal
  reply:=call.reply }

private noncomputable def declined {R :Type}
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (view :MaterialView mlSource KemSK) (views :Views)
    (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    (current nextCurrent :Native×Platform)
    (before :RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (next :RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential nextCurrent) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (pure (RustM.ok (none :Option (U64×alloc.vec.Vec U8)),nextCurrent)) := {
  step:={
    Packet:=Unit
    sample:=pure ()
    sourceType:=AdapterPublicServerBuildBody.Reply
    sourceReply:=fun _=>.ok (.None,before.base.objects.server)
    sourceState:=fun _=>before.base.objects.snapshot.committed
    sourceCall:=pure (.ok (.None,before.base.objects.server),before.base.objects.snapshot.committed)
    source_exact:=rfl
    native:=fun _=>(.ok none,nextCurrent)
    native_exact:=rfl
    store:=fun _ _=>next }
  observe:=fun _=>.ok none
  normal:=fun _ _=>⟨_,rfl⟩
  reply:=fun _ _ _ _=>rfl }

def bytes (result :RustM (Option (U64×alloc.vec.Vec U8))) :RustM (Option (U64×Pqxdh.Bytes)) :=do
  let optional←result
  pure (optional.map (fun value=>(value.1,TranscriptAuthParts.absSlice value.2)))

def response (result :RustM (Option (U64×alloc.vec.Vec U8))) :Option PqxdhServerRegistrationPublication.Response :=
  RegistrationNativeRawAdapter.responseOption (bytes result)

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] originalCrypto in
theorem declined_raw {R :Type}
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (view :MaterialView mlSource KemSK) (views :Views)
    (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    (current nextCurrent :Native×Platform)
    (before :RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (next :RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential nextCurrent) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map response
        (declined setup view views created credential current nextCurrent before next))=
      pure (RustM.ok ((none :Option PqxdhServerRegistrationPublication.Response),RegistrationNativePlatformPublicAdapterStore.erase next.base.objects),
        (RegistrationNativePlatformPublicAdapterStore.erase next.base.objects).backend) :=by
  unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw RegistrationNativePlatformPublicAdapterReply.map declined
  rfl

noncomputable def nativeStep {R : Type}
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
(handle :Nat) (payload :Option Pqxdh.Bytes)
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
            (RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (RegistrationNativePlatformSourceBuild.pin coins)
              (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
              (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure
                (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
                (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned mlSource credential)
                (RegistrationNativePlatformConcreteSource.writer reservePackets)) handle (RegistrationNativeRawAdapter.application payload))) current) :=by
  let pin:=RegistrationNativePlatformSourceBuild.pin (n:=n) coins
  let reserve:=(admitted <$>StateT.lift allocated :StateT (RegistrationServerFrontendCompiler.State n) Base Bool)
  let present:=RegistrationNativePlatformCompletionSdk.nativePresent (n:=n) coins
  let finish:=RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish (n:=n) coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned mlSource credential)
    (RegistrationNativePlatformConcreteSource.writer reservePackets)
  classical
  exact if selected :before.base.objects.tokens handle=none then
    modelCast (RegistrationNativePlatformExtractedSdkBuildDispatch.missing_model view views setup.joint created credential current before.base
      (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) pin reserve present finish handle selected (RegistrationNativeRawAdapter.application payload)).symm
      (declined setup view views created credential current current before before)
  else by
    have has : (before.base.objects.tokens handle).isSome=true :=by
      cases found :before.base.objects.tokens handle with
      | none=>exact False.elim (selected found)
      | some _=>rfl
    let token:=(before.base.objects.tokens handle).get has
    have stored :before.base.objects.tokens handle=some token :=(Option.some_get has).symm
    exact if convertedPayload :RegistrationNativeRawAdapter.application payload=none then
      modelCast (by
        rw [convertedPayload,RegistrationNativePlatformExtractedSdkBuildDispatch.cancel_model view views setup.joint created credential current before.base
          (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) pin reserve present finish handle token stored])
        (declined setup view views created credential current
          (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) before
          (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup view views created credential current before handle))
    else by
      have valid : (RegistrationNativeRawAdapter.application payload).isSome=true :=by
        cases found :RegistrationNativeRawAdapter.application payload with
        | none=>exact False.elim (convertedPayload found)
        | some _=>rfl
      let app:=(RegistrationNativeRawAdapter.application payload).get valid
      have applicationEq :RegistrationNativeRawAdapter.application payload=some app :=(Option.some_get valid).symm
      apply modelCast (by rw [applicationEq,RegistrationNativePlatformExtractedSdkBuildDispatch.live_model view views setup.joint created credential current before.base
        (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) pin reserve present finish handle token stored app])
      exact RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets
        originalLocal originalContainers previousChildren view views created credential
        (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup view views created credential current before handle)
        token (.Some app) edContract allocated reserveLeaf footprint containsLeaf installLeaves

noncomputable def step {R : Type}
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
(handle :Nat) (payload :Option Pqxdh.Bytes)
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
      (Prod.map response id <$>
        RegistrationNativePlatformPackedState.pack
          (RegistrationNativePlatformExperiment.server
            (RegistrationNativePlatformCompletionSdk.build (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (RegistrationNativePlatformSourceBuild.pin coins)
              (admitted <$>StateT.lift allocated) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
              (RegistrationNativePlatformExtractedSdkServer.Build.sourceFinish coins setup codec keyView failure
                (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
                (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased (RegistrationNativeMldsa.owned mlSource credential)
                (RegistrationNativePlatformConcreteSource.writer reservePackets)) handle (RegistrationNativeRawAdapter.application payload))) current) :=
  RegistrationNativePlatformPublicAdapterReply.map response (nativeStep coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before handle payload edContract allocated reserveLeaf footprint containsLeaf installLeaves)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw.declined_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw.declined_raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep
