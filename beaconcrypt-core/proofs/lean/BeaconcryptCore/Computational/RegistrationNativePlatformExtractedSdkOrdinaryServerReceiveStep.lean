-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun (Sample runner source native observed observe)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView)
variable (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
noncomputable def route (raw : Pqxdh.Bytes) : Option U64 := (RegistrationNativeConcreteCodec.wire.parseFrame raw).map CborProductionBoundary.NativeFrame.sender
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
variable (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : RegistrationNativeMldsa.Credential mlSource)

noncomputable def live (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (routed : route (TranscriptAuthParts.absSlice bytes)=some key)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (Carrier (R:=R) view views joint created credential)
      ((fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
          (.inl (.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run current.1).run current.2) := by
  let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
  let server:=Classical.choose fact
  have present:= (Classical.choose_spec fact).1
  have matched : AdapterPublicOrdinaryServerReifier.server view views before.objects.server server.records.rawAttempts=server := (Classical.choose_spec fact).2
  let peer : RawCtxServerRouting.Peer (Array U8 281#usize) :=
    ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩
  have found : server.records.server.peers key=some peer := by
    rw [←matched]
    change (views.peer before.objects.server.known_ids key).bind peerView=some peer
    rw [selected]
    exact AdapterPublicOrdinaryServerReifier.peer_kernel remote remote.peer.ratchet kernel stored
  refine {
    step  :=  {
      Packet := Sample Platform
      sample := runner setup erased.bytes server key peer bytes current.1 current.2
      sourceType := Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server
      sourceReply := (fun packet=>(source current.1 server.records.rawAttempts before.objects.server remote (back key) packet).outcome)
      sourceState := (fun packet=>(observed key view views (source current.1 server.records.rawAttempts before.objects.server remote (back key) packet)).2)
      sourceCall := observed key view views <$>RegistrationNativePlatformExtractedSdkOrdinary.run
        (RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased before.objects.server bytes)
        current.1 current.2 server.records.rawAttempts true
      source_exact := RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.observed_source setup reserve keyView failure erased view views
        before.objects.server remote back kernel bytes key routed selected stored get borrow current.1 current.2 server server.records.rawAttempts
      native := native current.1 server key peer
      native_exact := RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.native_exact setup reserve length erased.bytes route
        current.1 current.2 server key peer bytes present found routed
      store := ?_ }
    observe := observe
    normal := ?_
    reply := ?_ }
  · intro packet supported
    rcases packet with ⟨⟨raw,⟨primitive,frames⟩⟩,next⟩
    cases raw with
    | fail error=>exact PUnit.unit
    | div=>exact PUnit.unit
    | ok result=>
        rcases result with ⟨afterKernel,pubReply⟩
        have equal:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot.committed view views current.1 before.objects.server key remote (back key) (lens key)
          server matched kernel afterKernel pubReply primitive frames next
        change Carrier (R:=R) view views joint created credential _
        dsimp only [native,peer]
        dsimp only at equal
        rw [←equal]
        exact RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.put view views joint created credential current before key remote (back key) (lens key)
          afterKernel primitive frames next (PqxdhDeploymentNative.serverTag (.inr [])) server.records.rawAttempts true
  · intro packet supported
    exact RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.normal setup length erased.bytes
      before.objects.server remote (back key) bytes current.1 current.2 server key peer packet supported
  · intro packet supported returned actual
    exact RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.reply current.1 server key peer before.objects.server remote (back key) packet returned actual

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem transport_objects (current after : Native ×Platform) (same : current=after)
    (stored : Carrier (R:=R) view views joint created credential after) :
    ((congrArg (Carrier (R:=R) view views joint created credential) same).mpr stored).objects=stored.objects := by
  cases same
  rfl

theorem raw_objects (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (routed : route (TranscriptAuthParts.absSlice bytes)=some key)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target))
    (afterKernel : ratchet.concrete.ConcreteRatchetKernel) (pubReply : Option beaconcrypt.shared.Decrypted)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) (next : Platform)
    (supported : ((.ok (afterKernel,pubReply),(primitive,frames)),next)∈support
      (live setup reserve length keyView failure erased view views joint created credential current before bytes key remote routed selected kernel stored back lens get borrow).step.sample) :
    let call:=live setup reserve length keyView failure erased view views joint created credential current before bytes key remote routed selected kernel stored back lens get borrow
    (call.step.store ((.ok (afterKernel,pubReply),(primitive,frames)),next) supported).objects=
      {before.objects with server := AdapterPublicOrdinaryServerLookup.restore before.objects.server (some remote) (back key) (some (AdapterPublicOrdinaryEnvelope.manager afterKernel)), snapshot := .direct (call.step.sourceState ((.ok (afterKernel,pubReply),(primitive,frames)),next))} := by
  dsimp only [live]
  simp only [id_eq]
  rw [transport_objects]
  · rfl
  · let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
    exact (RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot.committed view views current.1 before.objects.server key remote (back key) (lens key)
      (Classical.choose fact) (Classical.choose_spec fact).2 kernel afterKernel pubReply primitive frames next).symm

theorem objects (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (routed : route (TranscriptAuthParts.absSlice bytes)=some key)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : U64 →Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀target changed query,views.peer (back target changed) query=if query=target then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids target=pure (views.peer before.objects.server.known_ids target,back target))
    (packet : {value //value∈support (live setup reserve length keyView failure erased view views joint created credential current before bytes key remote routed selected kernel stored back lens get borrow).step.sample}) :
    let call:=live setup reserve length keyView failure erased view views joint created credential current before bytes key remote routed selected kernel stored back lens get borrow
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      {before.objects with server := (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2, snapshot := .direct (call.step.sourceState packet.val)} := by
  let call:=live setup reserve length keyView failure erased view views joint created credential current before bytes key remote routed selected kernel stored back lens get borrow
  have normal:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
  rcases packet with ⟨⟨⟨raw,⟨primitive,frames⟩⟩,next⟩,supported⟩
  change RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned before.objects.server remote (back key) raw=.ok
    (RegistrationNativePlatformExtractedSdkPublic.returned call ⟨((raw,primitive,frames),next),supported⟩) at normal
  cases raw with
  | fail error | div=>cases normal
  | ok value=>
    rcases value with ⟨afterKernel,pubReply⟩
    have same : RegistrationNativePlatformExtractedSdkPublic.returned call ⟨((.ok (afterKernel,pubReply),primitive,frames),next),supported⟩=
        (pubReply,AdapterPublicOrdinaryServerLookup.restore before.objects.server (some remote) (back key) (some (AdapterPublicOrdinaryEnvelope.manager afterKernel))) :=
      (RustM.ok.inj normal).symm
    change (RegistrationNativePlatformExtractedSdkPublic.store call ⟨((.ok (afterKernel,pubReply),primitive,frames),next),supported⟩).objects=_
    rw [same]
    unfold RegistrationNativePlatformExtractedSdkPublic.store
    rw [same]
    exact raw_objects setup reserve length keyView failure erased view views joint created credential current before bytes key remote routed selected kernel stored back lens get borrow
      afterKernel pubReply primitive frames next supported

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.raw_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.raw_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveStep.objects
