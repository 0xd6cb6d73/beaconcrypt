-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (State)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
abbrev Sample (Platform : Type) := ((RustM AdapterRecordStatefulSend.Result ×State) ×Platform)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

noncomputable def runner (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (bytes : Slice U8) (before : Native) (previous : Platform) : ProbComp (Sample Platform) :=
  ((RegistrationNativePlatformExtractedSdkOrdinarySendOperands.sample setup (ledgerCodec wire) reserve view failure erased
    key server.sender peer.metadata peer.kernel bytes).run (before.server.world.world.1.primitive,[])).run previous

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def source (before : Native) (rawBefore : Nat) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (reached : Sample Platform) :
    RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.server.Server
      (Option beaconcrypt_record_send.shared.Encrypted) Native Platform :=
  RegistrationNativePlatformExtractedSdkOrdinary.pack before rawBefore false
    ((RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned self remote back reached.1.1,reached.1.2),reached.2)

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def native (before : Native) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (reached : Sample Platform) :
    Option RawCtxSourceSend.Encrypted ×(Native ×Platform) :=
  let result:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.project before.server.world.world.1 server key peer reached
  (result.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2))

theorem source_exact (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (views : AdapterPublicWrapperStorage.Views)
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (key : U64)
    (selected : views.peer self.known_ids key=some remote)
    (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (ledgerCodec wire) reserve view failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (ledgerCodec wire) reserve view failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids key=pure (views.peer self.known_ids key,back))
    (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (sender : server.sender=(platform.arcView self.identity).identity_key_kid)
    (rawBefore : Nat) :
    source before rawBefore self remote back <$>
      runner setup wire reserve view failure erased server key
        ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩ bytes before previous =
    RegistrationNativePlatformExtractedSdkOrdinary.run
      (RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (ledgerCodec wire) reserve view failure erased self bytes key)
      before previous rawBefore false := by
  have core:=congrArg (fun work=>(work.run (before.server.world.world.1.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinarySendOperands.source setup (ledgerCodec wire) reserve view failure erased
      views self remote back kernel bytes key selected stored get borrow)
  have lifted:=congrArg (fun distribution=>RegistrationNativePlatformExtractedSdkOrdinary.pack before rawBefore false <$>distribution) core
  simp only [StateT.run_map,Functor.map_map] at lifted
  unfold runner
  rw [sender]
  exact lifted

omit material ed platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
theorem native_exact (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (bytes : Slice U8)
    (present : before.server.world.world.1.server=some server)
    (selected : server.records.server.peers key=some peer) :
    native before server key peer <$>
      runner setup wire reserve view failure erased server key peer bytes before previous =
    (fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform)=>(result.1.1,(result.1.2,result.2))) <$>
      (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route
        (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))) mlSource).run before).run previous := by
  have core:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.guarded setup wire reserve length view converted failure erased route
    before.server.world.world.1 previous server key peer bytes present selected
  have lifted:=congrArg (fun distribution=>(fun result : ((Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftWorld.State n) ×Platform)=>
    (result.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2))) <$>distribution) core
  have target : (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route
      (.inl (.inl (TranscriptAuthParts.absSlice bytes,key))) mlSource).run before=
      (fun result : Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftWorld.State n =>
        (result.1,RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.2)) <$>
        (RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserve route
          (.inr (.inr (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))))).run before.server.world.world.1 := rfl
  have closed:=congrArg (fun work=>work.run previous) target
  simp only [StateT.run_map] at closed
  rw [closed,Functor.map_map]
  unfold native runner
  simpa only [Functor.map_map] using lifted

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observed (key : U64)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (packet : RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.server.Server
      (Option beaconcrypt_record_send.shared.Encrypted) Native Platform) :
    RustM (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server) ×(Native ×Platform) :=
  (packet.outcome,match packet.outcome with
    | .ok returned=>(RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot
        (PqxdhDeploymentNative.serverTag (.inl ([],key))) packet returned.2).committed view views
    | _=>packet.after)

theorem observed_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (key : U64)
    (selected : views.peer self.known_ids key=some remote)
    (stored : remote.peer.ratchet.refined.kernel=some kernel)
    (get : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.read (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids key=pure (views.peer self.known_ids key))
    (borrow : letI:=RegistrationNativePlatformExtractedSdkOrdinary.operations setup (ledgerCodec wire) reserve keyView failure erased
      AdapterPublicOrdinaryServerLookup.borrow (m:=RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform) self.known_ids key=pure (views.peer self.known_ids key,back))
    (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (sender : server.sender=(platform.arcView self.identity).identity_key_kid) (rawBefore : Nat) :
    (observed key view views ∘source before rawBefore self remote back) <$>
      runner setup wire reserve keyView failure erased server key
        ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩ bytes before previous =
    observed key view views <$>RegistrationNativePlatformExtractedSdkOrdinary.run
      (RegistrationNativePlatformExtractedSdkOrdinary.serverSend setup (ledgerCodec wire) reserve keyView failure erased self bytes key)
      before previous rawBefore false := by
  rw [←source_exact setup wire reserve keyView failure erased views self remote back kernel bytes key selected stored get borrow before previous server sender rawBefore,Functor.map_map]
  rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
theorem normal (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (bytes : Slice U8) (before : Native) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (reached : Sample Platform)
    (supported : reached∈support (runner setup wire reserve view failure erased server key peer bytes before previous)) :
    ∃returned,(source before server.records.rawAttempts self remote back reached).outcome=.ok returned := by
  obtain ⟨value,normal⟩:=RegistrationNativePlatformExtractedSdkOrdinarySendOperands.normal setup (ledgerCodec wire) reserve length view converted failure erased
    key server.sender peer.metadata peer.kernel bytes (before.server.world.world.1.primitive,[]) reached.1.2 previous reached.2 reached.1.1 supported
  refine ⟨(value.2,AdapterPublicOrdinaryServerLookup.restore self (some remote) back
    (some (AdapterPublicOrdinaryEnvelope.manager value.1))),?_⟩
  change RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned self remote back reached.1.1=_
  rw [normal]
  rfl

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observe (returned : Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server) :
    Option RawCtxSourceSend.Encrypted := RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply returned.1

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem reply (before : Native) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (self : beaconcrypt_public_wrapper.server.Server) (remote : AdapterPublicWrapperStorage.Remote ed.PublicKey)
    (back : Option (AdapterPublicWrapperStorage.Remote ed.PublicKey) →AdapterPublicWrapperStorage.PeerMap)
    (reached : Sample Platform)
    (returned : Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server)
    (same : (source before server.records.rawAttempts self remote back reached).outcome=.ok returned) :
    observe returned=(native before server key peer reached).1 := by
  change RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned self remote back reached.1.1=.ok returned at same
  cases value:reached.1.1 with
  | fail error=>rw [value,RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned] at same;cases same
  | div=>rw [value,RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned] at same;cases same
  | ok result=>
      rcases result with ⟨afterKernel,pubReply⟩
      rw [value,RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned] at same
      cases same
      change RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply pubReply=
        (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.project
          (RegistrationNativePlatformExtractedSdkOrdinarySendOperands.owner key peer.metadata peer.kernel server.records.rawAttempts) reached.1.1).1
      rw [value]
      cases pubReply <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.source_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.native_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.observed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendRun.reply
