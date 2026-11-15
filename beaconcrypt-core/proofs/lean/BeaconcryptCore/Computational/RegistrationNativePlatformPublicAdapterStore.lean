-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish
/-! The public adapter's actual source objects and persistent primitive/platform backend, with analysis owner representation erased. Source-only updates use returned source values and actual observed snapshots. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Objects Carrier SourceSnapshot)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R Platform : Type} {source : RegistrationNativeMldsa.Source}

structure Store (n : Nat) (KemSK R Platform : Type) where
  server : beaconcrypt_public_wrapper.server.Server
  beacons : Nat →Option beaconcrypt_public_wrapper.beacon.Beacon
  tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput
  rng : R
  nextSession : Nat
  nextOwner : Nat
  backend : RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform

def erase (objects : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R) : Store n KemSK R Platform :=
  ⟨objects.server,objects.beacons,objects.tokens,objects.rng,objects.nextSession,objects.nextOwner,
    RegistrationNativePlatformSdkReification.persistent objects.snapshot.committed⟩

def create (before : Store n KemSK R Platform) (outcome : AdapterBeaconConstructorBody.Outcome R)
    (backend : RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) : Store n KemSK R Platform :=
  { before with
    rng := outcome.2
    backend := backend
    beacons:=(match outcome.1 with | .Err _ =>before.beacons | .Ok self =>Function.update before.beacons before.nextOwner (some self))
    nextOwner:=(match outcome.1 with | .Err _ =>before.nextOwner | .Ok _ =>before.nextOwner+1) }

def accept (before : Store n KemSK R Platform) (word : AdapterPublicServerAgreementReceipt.Word R)
    (backend : RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) : Store n KemSK R Platform :=
  { before with
    server := word.2.1
    rng := word.2.2
    backend := backend
    tokens:=(match word.1 with | .None =>before.tokens | .Some token =>Function.update before.tokens before.nextSession (some token))
    nextSession:=(match word.1 with | .None =>before.nextSession | .Some _ =>before.nextSession+1) }

def server (before : Store n KemSK R Platform) (returned : beaconcrypt_public_wrapper.server.Server)
    (backend : RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) : Store n KemSK R Platform :=
  {before with server:=returned,backend:=backend}

def beacon (before : Store n KemSK R Platform) (index : Nat) (returned : beaconcrypt_public_wrapper.beacon.Beacon)
    (backend : RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) : Store n KemSK R Platform :=
  {before with beacons:=Function.update before.beacons index (some returned),backend:=backend}

def bundle (before : Store n KemSK R Platform) (index : Nat)
    (returned : core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)
    (backend : RegistrationNativePlatformSdkReification.Backend n KemSK ×Platform) : Store n KemSK R Platform :=
  {before with beacons:=Function.update before.beacons index (some returned.2.1),rng:=returned.2.2,backend:=backend}

def move (before : Store n KemSK R Platform) (handle : Nat) : Store n KemSK R Platform :=
  {before with tokens:=Function.update before.tokens handle none}

theorem create_update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (outcome : AdapterBeaconConstructorBody.Outcome R) (snapshot : SourceSnapshot n KemSK Platform source) :
    erase (RegistrationNativePlatformExtractedSdkCarrierCreate.update before outcome snapshot)=
      create (erase before) outcome (RegistrationNativePlatformSdkReification.persistent snapshot.committed) := by
  rcases outcome with ⟨chosen,rng⟩
  cases chosen <;> rfl

theorem accept_update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (word : AdapterPublicServerAgreementReceipt.Word R) (snapshot : SourceSnapshot n KemSK Platform source) :
    erase (RegistrationNativePlatformExtractedSdkCarrierServer.acceptUpdate before word snapshot)=
      accept (erase before) word (RegistrationNativePlatformSdkReification.persistent snapshot.committed) := rfl

theorem server_update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (returned : beaconcrypt_public_wrapper.server.Server) (snapshot : SourceSnapshot n KemSK Platform source) :
    erase (RegistrationNativePlatformExtractedSdkCarrierServer.buildUpdate before returned snapshot)=
      server (erase before) returned (RegistrationNativePlatformSdkReification.persistent snapshot.committed) := rfl

theorem retained (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (objects : Carrier (R:=R) view views joint created credential current) :
    (erase objects.objects).backend=RegistrationNativePlatformSdkReification.persistent current := objects.backend

theorem bundle_update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (index : Nat) (returned : core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R)
    (sourceAfter : RegistrationNativeExperiment.State n KemSK source ×Platform) :
    erase (RegistrationNativePlatformExtractedSdkCarrierBundle.update before index returned sourceAfter)=
      bundle (erase before) index returned (RegistrationNativePlatformSdkReification.persistent sourceAfter) := rfl

theorem finish_update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (index : Nat) (returned : AdapterPublicFinishBody.Result)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (sourceAfter : RegistrationNativeExperiment.State n KemSK source ×Platform) :
    erase (RegistrationNativePlatformExtractedSdkCarrierFinish.update before index returned environment sourceAfter)=
      beacon (erase before) index returned.2
        (RegistrationNativePlatformSdkReification.persistent (SourceSnapshot.committed (.environment environment sourceAfter))) := rfl

theorem move_update (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (objects : Carrier (R:=R) view views joint created credential current) (handle : Nat) :
    erase (RegistrationNativePlatformExtractedSdkCarrier.move view views joint created credential current objects handle).objects=
      move (erase objects.objects) handle := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.create_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.create_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.accept_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.accept_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.server_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.server_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.retained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.bundle_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.bundle_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.finish_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.finish_update
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.move_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore.move_update
