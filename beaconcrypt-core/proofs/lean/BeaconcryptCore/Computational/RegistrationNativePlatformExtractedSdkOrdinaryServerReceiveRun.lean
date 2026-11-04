-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (State)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
abbrev Sample (Platform : Type) := ((RustM AdapterRecordStatefulReceive.Result ×State) ×Platform)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

noncomputable def runner (setup : Setup base KemSK) (erased : Array U8 357#usize)
    (_server : PqxdhRecordLiftWorld.Server) (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (bytes : Slice U8) (before : Native) (previous : Platform) : ProbComp (Sample Platform) :=
  ((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire)
    erased peer.kernel key peer.metadata bytes).run (before.server.world.world.1.primitive,[])).run previous

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def source (before : Native) (rawBefore : Nat) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (reached : Sample Platform) :
    RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.server.Server
      (Option beaconcrypt.shared.Decrypted) Native Platform :=
  RegistrationNativePlatformExtractedSdkOrdinary.pack before rawBefore true
    ((RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned self remote back reached.1.1,reached.1.2),reached.2)

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def native (before : Native) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (reached : Sample Platform) :
    Option RawCtxWholeOwner.Decrypted ×(Native ×Platform) :=
  let result:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.project before.server.world.world.1 server key peer reached
  (result.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2))

theorem source_exact (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : U64 →Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (key : U64)
    (routed : (RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).map CborProductionBoundary.NativeFrame.sender=some key)
    (selected : views.peer self.known_ids key=some remote) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids target=pure (views.peer self.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids target=pure (views.peer self.known_ids target,back target))
    (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server) (rawBefore : Nat) :
    source before rawBefore self remote (back key) <$>
      runner setup erased.bytes server key ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩ bytes before previous =
    RegistrationNativePlatformExtractedSdkOrdinary.run
      (RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased self bytes)
      before previous rawBefore true := by
  have core:=congrArg (fun work=>(work.run (before.server.world.world.1.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.source setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased
      views self remote back kernel bytes key routed selected stored get borrow)
  have lifted:=congrArg (fun distribution=>RegistrationNativePlatformExtractedSdkOrdinary.pack before rawBefore true <$>distribution) core
  simp only [StateT.run_map,Functor.map_map] at lifted
  exact lifted

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem native_exact (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto) (erased : Array U8 357#usize)
    (route : RawCtxServerRouting.SenderDecoder)
    (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (bytes : Slice U8)
    (present : before.server.world.world.1.server=some server) (selected : server.records.server.peers key=some peer)
    (routed : route (TranscriptAuthParts.absSlice bytes)=some key) :
    native before server key peer <$>runner setup erased server key peer bytes before previous =
    (fun result : ((Option RawCtxWholeOwner.Decrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
      (((RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
        (.inl (.inr (TranscriptAuthParts.absSlice bytes)))) mlSource).run before).run previous := by
  have core:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.guarded setup reserve length erased route
    before.server.world.world.1 previous server key peer bytes present selected routed
  have lifted:=congrArg (fun distribution=>(fun result : ((Option RawCtxWholeOwner.Decrypted ×PqxdhRecordLiftWorld.State n) ×Platform)=>
    (result.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2))) <$>distribution) core
  have target : (RegistrationNativePlatformOrdinaryExperiment.record setup RegistrationNativeConcreteCodec.wire reserve route
      (.inl (.inr (TranscriptAuthParts.absSlice bytes))) mlSource).run before=
      (fun result : Option RawCtxWholeOwner.Decrypted ×PqxdhRecordLiftWorld.State n=>
        (result.1,RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.2)) <$>
        (RegistrationNativePlatformOrdinaryWorld.guarded setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve route
          (.inr (.inr (.inl (.inr (TranscriptAuthParts.absSlice bytes)))))).run before.server.world.world.1 := rfl
  have closed:=congrArg (fun work=>work.run previous) target
  simp only [StateT.run_map] at closed
  rw [closed,Functor.map_map]
  unfold native runner
  simpa only [Functor.map_map] using lifted

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observed (_key : U64)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (packet : RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.server.Server
      (Option beaconcrypt.shared.Decrypted) Native Platform) :
    RustM (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server) ×(Native ×Platform) :=
  (packet.outcome,match packet.outcome with
    | .ok returned=>(RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot
        (PqxdhDeploymentNative.serverTag (.inr [])) packet returned.2).committed view views
    | _=>packet.after)

theorem observed_source (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (viewMaterial : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : U64 →Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (key : U64)
    (routed : (RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).map CborProductionBoundary.NativeFrame.sender=some key)
    (selected : views.peer self.known_ids key=some remote) (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids target=pure (views.peer self.known_ids target))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased
      ∀target,AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids target=pure (views.peer self.known_ids target,back target))
    (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server) (rawBefore : Nat) :
    (observed key viewMaterial views ∘source before rawBefore self remote (back key)) <$>
      runner setup erased.bytes server key ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩ bytes before previous =
    observed key viewMaterial views <$>RegistrationNativePlatformExtractedSdkOrdinary.run
      (RegistrationNativePlatformExtractedSdkOrdinary.serverReceive setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve view failure erased self bytes)
      before previous rawBefore true := by
  rw [←source_exact setup reserve view failure erased views self remote back kernel bytes key routed selected stored get borrow before previous server rawBefore,Functor.map_map]
  rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem normal (setup : Setup base KemSK)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto) (erased : Array U8 357#usize)
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (bytes : Slice U8) (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (reached : Sample Platform)
    (supported : reached∈support (runner setup erased server key peer bytes before previous)) :
    ∃returned,(source before server.records.rawAttempts self remote back reached).outcome=.ok returned := by
  obtain ⟨value,normal⟩:=RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.normal setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) length erased
    peer.kernel key peer.metadata bytes (before.server.world.world.1.primitive,[]) reached.1.2 previous reached.2 reached.1.1 supported
  refine ⟨(value.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back
    (some (AdapterPublicOrdinaryEnvelope.manager value.1))),?_⟩
  change RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned self remote back reached.1.1=_
  rw [normal]
  rfl

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observe (returned : Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server) :
    Option RawCtxWholeOwner.Decrypted := RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply returned.1

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem reply (before : Native) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (reached : Sample Platform)
    (returned : Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server)
    (same : (source before server.records.rawAttempts self remote back reached).outcome=.ok returned) :
    observe returned=(native before server key peer reached).1 := by
  change RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned self remote back reached.1.1=.ok returned at same
  cases value:reached.1.1 with
  | fail error=>rw [value,RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned] at same;cases same
  | div=>rw [value,RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned] at same;cases same
  | ok result=>
      rcases result with ⟨afterKernel,pubReply⟩
      rw [value,RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned] at same
      cases same
      change RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply pubReply=
        (RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.project
          (RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.owner server key peer) reached.1.1).1
      rw [value]
      cases pubReply <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.source_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.native_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.observed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveRun.reply
