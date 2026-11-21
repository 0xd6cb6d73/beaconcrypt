-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSnapshot
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun
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
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) (before : Native) (previous : Platform) :
    ProbComp (Sample Platform) :=
  ((RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample setup (ledgerCodec wire) reserve view failure erased
    self control binding kernel bytes).run (before.server.world.world.1.primitive,[])).run previous

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def source (before : Native) (worldOwner : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (reached : Sample Platform) :
    RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.beacon.Beacon
      (Option beaconcrypt_record_send.shared.Encrypted) Native Platform :=
  RegistrationNativePlatformExtractedSdkOrdinary.pack before (before.server.world.world.1.ownerRaw worldOwner) false
    ((AdapterPublicOrdinaryKernel.returned self control binding reached.1.1,reached.1.2),reached.2)

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def native (before : Native) (worldOwner : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reached : Sample Platform) :
    Option RawCtxSourceSend.Encrypted ×(Native ×Platform) :=
  let result:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.project before.server.world.world.1
    worldOwner self control binding kernel reached
  (result.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2))

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem source_exact (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel))
    (bytes : Slice U8) (before : Native) (previous : Platform) (worldOwner : Nat) :
    source before worldOwner self control binding <$>
      runner setup wire reserve view failure erased self control binding kernel bytes before previous =
    RegistrationNativePlatformExtractedSdkOrdinary.run
      (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (ledgerCodec wire) reserve view failure erased self bytes)
      before previous (before.server.world.world.1.ownerRaw worldOwner) false := by
  have core:=congrArg (fun work=>(work.run (before.server.world.world.1.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.source setup (ledgerCodec wire) reserve view failure erased
      self control binding kernel stored bytes)
  have lifted:=congrArg (fun distribution=>RegistrationNativePlatformExtractedSdkOrdinary.pack before
    (before.server.world.world.1.ownerRaw worldOwner) false <$>distribution) core
  simp only [StateT.run_map,Functor.map_map] at lifted
  exact lifted

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem record_present (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (route : RawCtxServerRouting.SenderDecoder)
    (before : Native) (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (selected : before.beacons[logical]?=some owner) (bytes : Pqxdh.Bytes) :
    (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route (.inr (logical,.inl bytes)) mlSource).run before=
      (fun result : Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftWorld.State n =>(result.1,RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.2)) <$>
        ((RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserve route
          (.inr (.inr (.inr (owner.worldOwner,.inl bytes))))).run before.server.world.world.1) := by
  simp only [StateT.run,RegistrationNativePlatformOrdinaryExperiment.record,selected,RegistrationNativePlatformOrdinaryExperiment.world]
  rfl

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
theorem native_exact (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (before : Native) (previous : Platform) (logical : Nat) (owner : RegistrationNativeBeaconFrontend.Owner mlSource)
    (selected : before.beacons[logical]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (present : before.server.world.world.1.owners[owner.worldOwner]?=some
      (.established (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.shell self control binding) kernel)) :
    native before owner.worldOwner self control binding kernel <$>
      runner setup wire reserve view failure erased self control binding kernel bytes before previous =
    (fun result : ((Option RawCtxSourceSend.Encrypted ×Native) ×Platform) =>(result.1.1,(result.1.2,result.2))) <$>
      (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route
        (.inr (logical,.inl (TranscriptAuthParts.absSlice bytes)))) mlSource).run before).run previous := by
  have core:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.guarded setup wire reserve length view converted failure erased route
    before.server.world.world.1 previous owner.worldOwner self control binding kernel bytes present
  have lifted:=congrArg (fun distribution=>(fun result : ((Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftWorld.State n) ×Platform) =>
    (result.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2))) <$>distribution) core
  have target:=congrArg (fun work=>work.run previous)
    (record_present setup wire reserve route before logical owner selected (TranscriptAuthParts.absSlice bytes))
  simp only [StateT.run_map] at target
  rw [target,Functor.map_map]
  unfold native runner
  simpa only [Functor.map_map] using lifted

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observed (worldOwner : Nat) (fallback : beaconcrypt_public_wrapper.beacon.Beacon)
    (packet : RegistrationNativePlatformExtractedSdkOrdinaryReceipt.Packet beaconcrypt_public_wrapper.beacon.Beacon
      (Option beaconcrypt_record_send.shared.Encrypted) Native Platform) :
    RustM (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon) ×(Native ×Platform) :=
  let returned:=match packet.outcome with
    | .ok result=>result.2
    | _=>fallback
  (packet.outcome,(RegistrationNativePlatformSdkOrdinaryBeaconSnapshot.packet packet worldOwner returned).committed)

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem observed_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel))
    (bytes : Slice U8) (before : Native) (previous : Platform) (worldOwner : Nat) :
    (observed worldOwner self ∘source before worldOwner self control binding) <$>
      runner setup wire reserve view failure erased self control binding kernel bytes before previous =
    observed worldOwner self <$>RegistrationNativePlatformExtractedSdkOrdinary.run
      (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (ledgerCodec wire) reserve view failure erased self bytes)
      before previous (before.server.world.world.1.ownerRaw worldOwner) false := by
  rw [←source_exact setup wire reserve view failure erased self control binding kernel stored bytes before previous worldOwner,Functor.map_map]
  rfl

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] in
theorem normal (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (before : Native) (previous : Platform) (worldOwner : Nat) (reached : Sample Platform)
    (supported : reached∈support (runner setup wire reserve view failure erased self control binding kernel bytes before previous)) :
    ∃returned,(source before worldOwner self control binding reached).outcome=.ok returned := by
  obtain ⟨value,normal⟩:=RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_normal setup (ledgerCodec wire) reserve length view converted failure erased
    self control binding kernel bytes (before.server.world.world.1.primitive,[]) reached.1.2 previous reached.2 reached.1.1 supported
  refine ⟨(value.2,{self with state:=.Established control binding (AdapterPublicOrdinaryEnvelope.manager value.1)}),?_⟩
  change AdapterPublicOrdinaryKernel.returned self control binding reached.1.1=_
  rw [normal,AdapterPublicOrdinaryKernel.returned_exact]
  rfl

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def observe (returned : Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon) :
    Option RawCtxSourceSend.Encrypted := RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply returned.1

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem reply (before : Native) (worldOwner : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (reached : Sample Platform)
    (returned : Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon)
    (same : (source before worldOwner self control binding reached).outcome=.ok returned) :
    observe returned=(native before worldOwner self control binding kernel reached).1 := by
  change AdapterPublicOrdinaryKernel.returned self control binding reached.1.1=.ok returned at same
  cases value:reached.1.1 with
  | fail error=>
      rw [value,AdapterPublicOrdinaryKernel.returned_fail] at same
      cases same
  | div=>
      rw [value,AdapterPublicOrdinaryKernel.returned_div] at same
      cases same
  | ok result=>
      rcases result with ⟨afterKernel,pubReply⟩
      rw [value,AdapterPublicOrdinaryKernel.returned_exact] at same
      cases same
      change RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply pubReply=
        (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.project
          (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner control binding kernel (before.server.world.world.1.ownerRaw worldOwner)) reached.1.1).1
      rw [value]
      cases pubReply <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.source_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.native_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.reply
