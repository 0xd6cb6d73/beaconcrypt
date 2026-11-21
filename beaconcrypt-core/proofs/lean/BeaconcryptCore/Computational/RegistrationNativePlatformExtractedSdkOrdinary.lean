-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
/-! The four literal SDK methods use the actual dynamic stateful record drivers. Their common packet retains the returned source Self, actual primitive/platform poststate and actual attempted writer frames, before any owner finalizer. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryReceipt (Packet)
variable {n : Nat} {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
abbrev M (Platform : Type) := RegistrationNativePlatformExtractedSdkOrdinaryDriver.M Platform

@[instance_reducible] noncomputable def operations [primitives : AdapterSealPrimitive.Operations]
    [FrameDispatchFallback.Operations] [PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator]
    [AdapterPublicOrdinaryPlatform.LookupOperations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) : AdapterPublicOrdinaryRequestMonad.Operations (RustT (M Platform)) where
  send kernel context := ⟨RegistrationNativePlatformExtractedSdkOrdinaryDriver.send setup codec reserve view failure erased kernel context⟩
  receive pending := ⟨RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.effect setup codec erased.bytes pending⟩
  get eq hash build allocator queryHash equivalent table key :=
    liftRust (AdapterPublicOrdinaryPlatform.LookupOperations.get eq hash build allocator queryHash equivalent table key)
  getMut eq hash build allocator queryHash equivalent table key :=
    liftRust (AdapterPublicOrdinaryPlatform.LookupOperations.getMut eq hash build allocator queryHash equivalent table key)

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

noncomputable def beaconSend (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon) (bytes : Slice U8) :
    M Platform (RustM (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon)) :=
  letI := operations setup codec reserve view failure erased
  (beaconcrypt_public_ordinary_request.beacon.Beacon.encrypt_message (m:=RustT (M Platform)) self bytes).run

noncomputable def beaconReceive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon) (bytes : Slice U8) :
    M Platform (RustM (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.beacon.Beacon)) :=
  letI := operations setup codec reserve view failure erased
  (beaconcrypt_public_ordinary_request.beacon.Beacon.decrypt_message (m:=RustT (M Platform)) self bytes).run

noncomputable def serverSend (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) (key : U64) :
    M Platform (RustM (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.server.Server)) :=
  letI := operations setup codec reserve view failure erased
  (beaconcrypt_public_ordinary_request.server.Server.encrypt_message (m:=RustT (M Platform)) self bytes key).run

noncomputable def serverReceive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.server.Server) (bytes : Slice U8) :
    M Platform (RustM (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.server.Server)) :=
  letI := operations setup codec reserve view failure erased
  (beaconcrypt_public_ordinary_request.server.Server.decrypt_message (m:=RustT (M Platform)) self bytes).run

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def pack {Self Reply : Type} (before : RegistrationNativeExperiment.State n KemSK source)
    (rawBefore : Nat) (rawInvoked : Bool)
    (reached : ((RustM (Reply ×Self) ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :
    Packet Self Reply (RegistrationNativeExperiment.State n KemSK source) Platform :=
  ⟨reached.1.1,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before
    { before.server.world.world.1 with primitive:=reached.1.2.1 },reached.2),reached.1.2.2,rawBefore,rawInvoked⟩

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
noncomputable def run {Self Reply : Type}
    (work : M Platform (RustM (Reply ×Self))) (before : RegistrationNativeExperiment.State n KemSK source)
    (previous : Platform) (rawBefore : Nat) (rawInvoked : Bool) :
    ProbComp (Packet Self Reply (RegistrationNativeExperiment.State n KemSK source) Platform) :=
  pack before rawBefore rawInvoked <$> (work.run (before.server.world.world.1.primitive,[])).run previous

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def serverSnapshot {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (packet : Packet beaconcrypt_public_wrapper.server.Server Reply (RegistrationNativeExperiment.State n KemSK source) Platform)
    (returned : beaconcrypt_public_wrapper.server.Server) :
    RegistrationNativePlatformSdkOrdinarySnapshot.Server n KemSK Platform source :=
  ⟨returned,packet.after,tag,packet.frames,packet.rawBefore,packet.rawInvoked⟩

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem run_supported {Self Reply : Type}
    (work : M Platform (RustM (Reply ×Self))) (before : RegistrationNativeExperiment.State n KemSK source)
    (previous : Platform) (rawBefore : Nat) (rawInvoked : Bool)
    (packet : Packet Self Reply (RegistrationNativeExperiment.State n KemSK source) Platform)
    (supported : packet ∈ support (run work before previous rawBefore rawInvoked)) :
    ∃reached, reached ∈support ((work.run (before.server.world.world.1.primitive,[])).run previous) ∧
      pack before rawBefore rawInvoked reached=packet := by
  change packet ∈support (pack before rawBefore rawInvoked <$>
    (work.run (before.server.world.world.1.primitive,[])).run previous) at supported
  rw [support_map] at supported
  exact supported

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
def sourceProjection {Self Reply : Type}
    (packet : Packet Self Reply (RegistrationNativeExperiment.State n KemSK source) Platform) :
    ((RustM (Reply ×Self) ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform) :=
  ((packet.outcome,(packet.after.1.server.world.world.1.primitive,packet.frames)),packet.after.2)

omit material platform [PublicWrapperPlatform.Allocator] ed [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
theorem run_source {Self Reply : Type}
    (work : M Platform (RustM (Reply ×Self))) (before : RegistrationNativeExperiment.State n KemSK source)
    (previous : Platform) (rawBefore : Nat) (rawInvoked : Bool) :
    sourceProjection <$> run work before previous rawBefore rawInvoked =
      (work.run (before.server.world.world.1.primitive,[])).run previous := by
  change sourceProjection <$> (pack before rawBefore rawInvoked <$>
    (work.run (before.server.world.world.1.primitive,[])).run previous) = _
  rw [Functor.map_map]
  exact id_map' _

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary.run_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary.run_supported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary.run_source
