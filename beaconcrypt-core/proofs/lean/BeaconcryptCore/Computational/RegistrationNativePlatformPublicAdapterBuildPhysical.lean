import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildNormalization
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterNormalizedRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStrongBuildSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical
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



omit material platform ed primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] originalCrypto in
private theorem source_eq {N Reply T :Type} {Private :N →Type} {model :ProbComp (Reply×N)}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep Private model)
    (first :{packet //packet∈support call.step.sample} →T)
    (update :RustM call.step.sourceType×N →T)
    (retained :∀packet,first packet=update (call.step.sourceReply packet.val,call.step.sourceState packet.val)) :
    first <$>PFunctor.FreeM.attachSupp call.step.sample=update <$>call.step.sourceCall :=by
  rw [←call.step.source_exact,Functor.map_map]
  have erased:=congrArg (fun work=>(fun packet=>update (call.step.sourceReply packet,call.step.sourceState packet)) <$>work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
  simp only [Functor.map_map] at erased
  rw [←erased]
  congr 1
  funext packet
  exact retained packet

noncomputable def finish {R :Type} (view :MaterialView mlSource KemSK) (views :Views)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform)
    (result :RustM AdapterPublicServerBuildBody.Reply×(RegistrationNativePlatformSdkReification.Backend n KemSK×Platform)) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.Raw (n:=n) (KemSK:=KemSK) (R:=R) (Platform:=Platform) (Option PqxdhServerRegistrationPublication.Response) :=
  match result.1 with
  | .fail error=>(.fail error,result.2)
  | .div=>(.div,result.2)
  | .ok word=>
    let backend:=RegistrationNativePlatformPublicAdapterBuildStore.committed view views word.2 result.2
    (.ok (RegistrationNativePlatformPublicAdapterBuildRaw.response (AdapterPublicServerPublicationInstall.project (.ok word)),
      RegistrationNativePlatformPublicAdapterStore.server before word.2 backend),backend)

noncomputable def active {R :Type}
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :MaterialView mlSource KemSK) (views :Views) (original :ContainerOperations (RustT Base))
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8))
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :=
  (fun result=>finish view views before (result.1.1.2,(result.1.2,result.2))) <$>
    ((RegistrationNativePlatformPublicAdapterBuildSource.program coins setup codec keyView failure allocation helper erased
      (RegistrationNativeMldsa.owned mlSource (view.mldsa (platform.arcView before.server.identity).mldsa_identity))
      writer view original before.server token data).run before.backend.1).run before.backend.2


noncomputable def run {R :Type}
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :MaterialView mlSource KemSK) (views :Views) (original :ContainerOperations (RustT Base))
    (handle :Nat) (payload :Option Pqxdh.Bytes)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :
    ProbComp (RegistrationNativePlatformPublicAdapterPhysicalOrdinary.Raw (n:=n) (KemSK:=KemSK) (R:=R) (Platform:=Platform) (Option PqxdhServerRegistrationPublication.Response)) :=
  match before.tokens handle with
  | none=>pure (RustM.ok (none,before),before.backend)
  | some token=>
    let moved:=RegistrationNativePlatformPublicAdapterStore.move before handle
    match RegistrationNativeRawAdapter.application payload with
    | none=>pure (RustM.ok (none,moved),moved.backend)
    | some app=>active coins setup codec keyView failure allocation helper erased writer view views original token (.Some app) moved

theorem complete_query {R : Type}
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
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response call)=
      active coins setup codec keyView failure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
        (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
        (RegistrationNativePlatformConcreteSource.writer reservePackets) view views originalContainers token data
        (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) :=by
  let call:=RegistrationNativePlatformPublicAdapterStrongBuild.complete coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves
  have attached : RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativePlatformPublicAdapterBuildRaw.response call)=
      (fun result=>finish view views (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)
        (result.1,RegistrationNativePlatformSdkReification.persistent result.2)) <$>call.step.sourceCall :=by
    unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
    apply source_eq call
    intro packet
    have kept:=RegistrationNativePlatformPublicAdapterStrongBuildSource.stored coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves packet
    have normal:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
    change (RustM.ok
      (RegistrationNativePlatformPublicAdapterBuildRaw.response
        (AdapterPublicServerPublicationInstall.project (.ok (RegistrationNativePlatformExtractedSdkPublic.returned call packet))),
        RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects),
      (RegistrationNativePlatformPublicAdapterStore.erase (RegistrationNativePlatformExtractedSdkPublic.store call packet).base.objects).backend)=_
    rw [kept]
    unfold finish
    rw [normal]
    rfl
  have projected:=congrArg
    (fun computation=>finish view views (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) <$>computation)
    (RegistrationNativePlatformPublicAdapterStrongBuildSource.source coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before token data edContract allocated reserveLeaf footprint containsLeaf installLeaves)
  unfold active
  rw [RegistrationNativePlatformPublicAdapterStore.retained view views setup.joint created credential current before.base]
  simp only [Functor.map_map,Prod.map,id_eq,StateT.run_map] at projected attached ⊢
  exact attached.trans projected

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] originalCrypto in
private theorem raw_map_cast {R N ReplyA ReplyB :Type} {Private :N →Type}
    {left right :ProbComp (ReplyA×N)} (same :left=right)
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep Private left)
    (observe :ReplyA →ReplyB)
    (physical :∀current,Private current →RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical
      (RegistrationNativePlatformPublicAdapterReply.map observe (RegistrationNativePlatformPublicAdapterBuildRaw.modelCast same call))=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (RegistrationNativePlatformPublicAdapterReply.map observe call) :=by
  cases same
  rfl

theorem query {R : Type}
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
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterBuildRaw.step coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before handle payload edContract allocated reserveLeaf footprint containsLeaf installLeaves)=
      run coins setup codec keyView failure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
        (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
        (RegistrationNativePlatformConcreteSource.writer reservePackets) view views originalContainers handle payload
        (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects) :=by
  classical
  by_cases missing :before.base.objects.tokens handle=none
  · simp [RegistrationNativePlatformPublicAdapterBuildRaw.step,RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep,raw_map_cast,
      RegistrationNativePlatformPublicAdapterBuildRaw.declined_raw,run,missing,RegistrationNativePlatformPublicAdapterStore.erase]

  · have has :(before.base.objects.tokens handle).isSome=true :=by
      cases found :before.base.objects.tokens handle with
      | none=>exact False.elim (missing found)
      | some _=>rfl
    let token:=(before.base.objects.tokens handle).get has
    have stored :before.base.objects.tokens handle=some token :=(Option.some_get has).symm
    by_cases cancelled :RegistrationNativeRawAdapter.application payload=none
    · simp [RegistrationNativePlatformPublicAdapterBuildRaw.step,RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep,
        raw_map_cast,RegistrationNativePlatformPublicAdapterBuildRaw.declined_raw,run,stored,cancelled,
        RegistrationNativePlatformPublicAdapterBuildDispatch.moved_objects,
        RegistrationNativePlatformPublicAdapterStore.erase,RegistrationNativePlatformPublicAdapterStore.move]

    · have valid :(RegistrationNativeRawAdapter.application payload).isSome=true :=by
        cases found :RegistrationNativeRawAdapter.application payload with
        | none=>exact False.elim (cancelled found)
        | some _=>rfl
      let app:=(RegistrationNativeRawAdapter.application payload).get valid
      have applicationEq :RegistrationNativeRawAdapter.application payload=some app :=(Option.some_get valid).symm
      have activeLaw:=complete_query coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential
        (AdapterPublicServerBuildOwnership.moved handle current.1,current.2)
        (RegistrationNativePlatformPublicAdapterBuildDispatch.move setup view views created credential current before handle)
        token (.Some app) edContract allocated reserveLeaf footprint containsLeaf installLeaves
      simpa [RegistrationNativePlatformPublicAdapterBuildRaw.step,RegistrationNativePlatformPublicAdapterBuildRaw.nativeStep,missing,cancelled,
        raw_map_cast,run,RegistrationNativePlatformPublicAdapterBuildDispatch.moved_objects,
        RegistrationNativePlatformPublicAdapterStore.erase,stored,applicationEq,
        RegistrationNativePlatformPublicAdapterStore.move] using activeLaw

omit primitive [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] originalCrypto in
private theorem finish_frame {R :Type} (view :MaterialView mlSource KemSK) (views :Views)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform)
    (result :RustM AdapterPublicServerBuildBody.Reply×(RegistrationNativePlatformSdkReification.Backend n KemSK×Platform)) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize (finish view views before result)=
      finish view views (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before)
        (result.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent result.2) :=by
  rcases result with ⟨outcome,after⟩
  cases outcome <;>rfl

omit originalCrypto in
private theorem active_frame {R :Type}
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :MaterialView mlSource KemSK) (views :Views) (original :ContainerOperations (RustT Base))
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8))
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      active coins setup codec keyView failure allocation helper erased writer view views original token data before=
      active coins setup codec keyView failure allocation helper erased writer view views original token data
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) :=by
  let program:=RegistrationNativePlatformPublicAdapterBuildSource.program (n:=n) coins setup codec keyView failure allocation helper erased
    (RegistrationNativeMldsa.owned mlSource (view.mldsa (platform.arcView before.server.identity).mldsa_identity))
    writer view original before.server token data
  have kept:=RegistrationNativePlatformPublicAdapterPhysicalFrame.map_frame Prod.snd program
    (RegistrationNativePlatformPublicAdapterBuildNormalization.program coins setup codec keyView failure allocation helper erased
      (RegistrationNativeMldsa.owned mlSource (view.mldsa (platform.arcView before.server.identity).mldsa_identity))
      writer view original before.server token data)
  have whole:=congrArg (fun computation=>computation.run before.backend.2) (kept before.backend.1)
  have result:=congrArg
    (fun computation=>(fun current=>finish view views (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before)
      (current.1.1,(current.1.2,current.2))) <$>computation) whole
  simpa only [active,program,StateT.run_map,Functor.map_map,Prod.map,id_eq,finish_frame,
    RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent] using result

omit originalCrypto in
theorem run_frame {R :Type}
    (coins :QueryImpl unifSpec Base) (setup :PqxdhServerAuthExperiment.Setup base KemSK)
    (codec :PqxdhServerAuthExperiment.Codec Reader Response) (keyView :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base) (erased :commitment.CommitmentTranscript)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base)
    (view :MaterialView mlSource KemSK) (views :Views) (original :ContainerOperations (RustT Base))
    (handle :Nat) (payload :Option Pqxdh.Bytes)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R Platform) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      run coins setup codec keyView failure allocation helper erased writer view views original handle payload before=
      run coins setup codec keyView failure allocation helper erased writer view views original handle payload
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) :=by
  cases selected :before.tokens handle with
  | none=>
    simp only [run,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,selected,map_pure]
    rfl
  | some token=>
    cases applicationEq :RegistrationNativeRawAdapter.application payload with
    | none=>
      simp only [run,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,selected,applicationEq,map_pure]
      rfl
    | some app=>
      simpa only [run,RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,selected,applicationEq,
        RegistrationNativePlatformPublicAdapterStore.move] using
        active_frame coins setup codec keyView failure allocation helper erased writer view views original token (.Some app)
          (RegistrationNativePlatformPublicAdapterStore.move before handle)

theorem normalized_query {R : Type}
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
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
      (fun current stored=>RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
        (RegistrationNativePlatformSdkOrdinaryBeaconSelected.strongPhysical setup view views created credential current stored))
      (RegistrationNativePlatformPublicAdapterBuildRaw.step coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before handle payload edContract allocated reserveLeaf footprint containsLeaf installLeaves)=
      run coins setup codec keyView failure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
        (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
        (RegistrationNativePlatformConcreteSource.writer reservePackets) view views originalContainers handle payload
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize
          (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)) :=by
  rw [RegistrationNativePlatformPublicAdapterNormalizedRaw.raw,query coins setup codec keyView converted failure allocate reserveFrame erased reservePackets originalLocal originalContainers previousChildren view views created credential current before handle payload edContract allocated reserveLeaf footprint containsLeaf installLeaves]
  exact run_frame coins setup codec keyView failure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation allocate)
    (RegistrationNativePlatformConcreteSource.helper reserveFrame) erased
    (RegistrationNativePlatformConcreteSource.writer reservePackets) view views originalContainers handle payload
    (RegistrationNativePlatformPublicAdapterStore.erase before.base.objects)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.complete_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.complete_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.run_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.run_frame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.normalized_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildPhysical.normalized_query
