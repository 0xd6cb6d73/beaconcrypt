-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier)
open RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun (Sample runner source native observed observe)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView)
variable (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
variable (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
variable (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : RegistrationNativeMldsa.Credential mlSource)

noncomputable def live (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key,back)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (Carrier (R:=R) view views joint created credential)
      ((fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route
          (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))) mlSource).run current.1).run current.2) := by
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
  have sender : server.sender=(platform.arcView before.objects.server.identity).identity_key_kid := by
    rw [←matched]
    rfl
  refine {
    step  :=  {
      Packet := Sample Platform
      sample := runner setup wire reserve keyView failure erased server key peer bytes current.1 current.2
      sourceType := Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server
      sourceReply := (fun packet=>(source current.1 server.records.rawAttempts before.objects.server remote back packet).outcome)
      sourceState := (fun packet=>(observed key view views (source current.1 server.records.rawAttempts before.objects.server remote back packet)).2)
      sourceCall := observed key view views <$>RegistrationNativePlatformExtractedSdkOrdinary.run
        (RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased before.objects.server bytes key)
        current.1 current.2 server.records.rawAttempts false
      source_exact := RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.observed_source setup wire reserve keyView failure erased view views
        before.objects.server remote back kernel bytes key selected stored get borrow current.1 current.2 server sender server.records.rawAttempts
      native := native current.1 server key peer
      native_exact := RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.native_exact setup wire reserve length keyView converted failure erased route
        current.1 current.2 server key peer bytes present found
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
        have equal:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.committed view views current.1 before.objects.server key remote back lens
          server matched kernel afterKernel pubReply primitive frames next
        change Carrier (R:=R) view views joint created credential _
        dsimp only [native,peer]
        dsimp only at equal
        rw [←equal]
        exact RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.put view views joint created credential current before key remote back lens
          afterKernel primitive frames next (PqxdhDeploymentNative.serverTag (.inl ([],key))) server.records.rawAttempts false
  · intro packet supported
    exact RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.normal setup wire reserve length keyView converted failure erased
      before.objects.server remote back bytes current.1 current.2 server key peer packet supported
  · intro packet supported returned actual
    exact RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.reply current.1 server key peer before.objects.server remote back packet returned actual

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
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key,back))
    (afterKernel : ratchet.concrete.ConcreteRatchetKernel) (pubReply : Option beaconcrypt_record_send.shared.Encrypted)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) (next : Platform)
    (supported : ((.ok (afterKernel,pubReply),(primitive,frames)),next)∈support
      (live setup wire reserve length keyView converted failure erased route view views joint created credential current before bytes key remote selected kernel stored back lens get borrow).step.sample) :
    let call:=live setup wire reserve length keyView converted failure erased route view views joint created credential current before bytes key remote selected kernel stored back lens get borrow
    (call.step.store ((.ok (afterKernel,pubReply),(primitive,frames)),next) supported).objects=
      {before.objects with server := AdapterPublicOrdinaryServerLookup.restore before.objects.server (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager afterKernel)), snapshot := .direct (call.step.sourceState ((.ok (afterKernel,pubReply),(primitive,frames)),next))} := by
  dsimp only [live]
  simp only [id_eq]
  rw [transport_objects]
  · rfl
  · let fact:=AdapterPublicOrdinaryServerReifier.related view views created credential before.objects.server current.1.server before.server
    exact (RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.committed view views current.1 before.objects.server key remote back lens
      (Classical.choose fact) (Classical.choose_spec fact).2 kernel afterKernel pubReply primitive frames next).symm

theorem objects (current : Native ×Platform) (before : Carrier (R:=R) view views joint created credential current)
    (bytes : Slice U8) (key : U64) (remote : Remote ed.PublicKey)
    (selected : views.peer before.objects.server.known_ids key=some remote)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer before.objects.server.known_ids query)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) before.objects.server.known_ids key=pure (views.peer before.objects.server.known_ids key,back))
    (packet : {value //value∈support (live setup wire reserve length keyView converted failure erased route view views joint created credential current before bytes key remote selected kernel stored back lens get borrow).step.sample}) :
    let call:=live setup wire reserve length keyView converted failure erased route view views joint created credential current before bytes key remote selected kernel stored back lens get borrow
    (RegistrationNativePlatformExtractedSdkPublic.store call packet).objects=
      {before.objects with server := (RegistrationNativePlatformExtractedSdkPublic.returned call packet).2, snapshot := .direct (call.step.sourceState packet.val)} := by
  let call:=live setup wire reserve length keyView converted failure erased route view views joint created credential current before bytes key remote selected kernel stored back lens get borrow
  have normal:=RegistrationNativePlatformExtractedSdkPublic.returned_exact call packet
  rcases packet with ⟨⟨⟨raw,⟨primitive,frames⟩⟩,next⟩,supported⟩
  change RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned before.objects.server remote back raw=.ok
    (RegistrationNativePlatformExtractedSdkPublic.returned call ⟨((raw,primitive,frames),next),supported⟩) at normal
  cases raw with
  | fail error | div=>cases normal
  | ok value=>
    rcases value with ⟨afterKernel,pubReply⟩
    have same : RegistrationNativePlatformExtractedSdkPublic.returned call ⟨((.ok (afterKernel,pubReply),primitive,frames),next),supported⟩=
        (pubReply,AdapterPublicOrdinaryServerLookup.restore before.objects.server (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager afterKernel))) :=
      (RustM.ok.inj normal).symm
    change (RegistrationNativePlatformExtractedSdkPublic.store call ⟨((.ok (afterKernel,pubReply),primitive,frames),next),supported⟩).objects=_
    rw [same]
    unfold RegistrationNativePlatformExtractedSdkPublic.store
    rw [same]
    exact raw_objects setup wire reserve length keyView converted failure erased route view views joint created credential current before bytes key remote selected kernel stored back lens get borrow
      afterKernel pubReply primitive frames next supported

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.raw_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.raw_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendStep.objects
