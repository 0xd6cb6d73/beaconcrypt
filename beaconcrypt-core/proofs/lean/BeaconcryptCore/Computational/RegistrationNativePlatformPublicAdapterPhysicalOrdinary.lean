-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical
/-! Ordinary source calls do not inspect the indexed KEM observation log. Its physical quotient commutes with the actual Server and Beacon send/receive runners, including terminal failure/divergence and exact returned object updates. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R Platform Reply PublicReply : Type} {mlSource : RegistrationNativeMldsa.Source}

abbrev Raw (Value : Type) :=RustM (Value×Store n KemSK R Platform)×(Backend n KemSK×Platform)

def normalize (result : Raw (n:=n) (KemSK:=KemSK) (R:=R) (Platform:=Platform) Reply) : Raw (n:=n) (KemSK:=KemSK) (R:=R) (Platform:=Platform) Reply :=
  (Prod.map id RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize <$>result.1,
    RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent result.2)

open RegistrationNativePlatformExtractedSdkOrdinaryDriver (State)

theorem server_finish (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (before : Store n KemSK R Platform) (observe : Reply → PublicReply) (tag : PqxdhDeploymentInterface.FrameTag) (invoked : Bool)
    (reached : ((RustM (Reply×beaconcrypt_public_wrapper.server.Server)×State)×Platform)) :
    normalize (RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.finish view views before observe tag invoked reached)=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.finish view views
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) observe tag invoked reached :=by
  rcases reached with ⟨⟨outcome,state⟩,next⟩
  cases outcome <;>rfl

theorem beacon_finish (before : Store n KemSK R Platform) (index : Nat) (observe : Reply → PublicReply) (invoked : Bool)
    (reached : ((RustM (Reply×beaconcrypt_public_wrapper.beacon.Beacon)×State)×Platform)) :
    normalize (RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.finish before index observe invoked reached)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.finish
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index observe invoked reached :=by
  rcases reached with ⟨⟨outcome,state⟩,next⟩
  cases outcome <;>rfl

variable {E I : Type} {base : OracleSpec I}
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (keyView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (erased : commitment.CommitmentTranscript)

theorem server_send (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (before : Store n KemSK R Platform) (bytes : Slice U8) (key : U64) :
    normalize <$> RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup reserve keyView failure erased view views before bytes key=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send setup reserve keyView failure erased view views
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) bytes key :=by
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.send,Functor.map_map]
  congr 1
  funext result
  exact server_finish view views before _ _ _ result

theorem server_receive (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (before : Store n KemSK R Platform) (bytes : Slice U8) :
    normalize <$> RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup reserve keyView failure erased view views before bytes=
      RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive setup reserve keyView failure erased view views
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) bytes :=by
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryServerPhysical.receive,Functor.map_map]
  congr 1
  funext result
  exact server_finish view views before _ _ _ result

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem beacon_send (before : Store n KemSK R Platform) (index : Nat) (bytes : Slice U8) :
    normalize <$> RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup reserve keyView failure erased before index bytes=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup reserve keyView failure erased
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index bytes :=by
  unfold RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send
  change normalize <$> (match before.beacons index with | none=>_ | some self=>_)=
    (match before.beacons index with | none=>_ | some self=>_)
  cases selected:before.beacons index with
  | none=>simp only [map_pure];rfl
  | some self=>
    rw [Functor.map_map]
    congr 1
    funext result
    exact beacon_finish before index _ _ result

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem beacon_receive (before : Store n KemSK R Platform) (index : Nat) (bytes : Slice U8) :
    normalize <$> RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup reserve keyView failure erased before index bytes=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup reserve keyView failure erased
        (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index bytes :=by
  unfold RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive
  change normalize <$> (match before.beacons index with | none=>_ | some self=>_)=
    (match before.beacons index with | none=>_ | some self=>_)
  cases selected:before.beacons index with
  | none=>simp only [map_pure];rfl
  | some self=>
    rw [Functor.map_map]
    congr 1
    funext result
    exact beacon_finish before index _ _ result

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_send
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.server_receive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_send
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary.beacon_receive
