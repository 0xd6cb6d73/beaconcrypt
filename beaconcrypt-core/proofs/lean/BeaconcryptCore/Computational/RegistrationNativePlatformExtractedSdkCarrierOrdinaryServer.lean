-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier Objects)
variable {n : Nat} {KemSK Platform R : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

def snapshot (before : Native) (self : beaconcrypt_public_wrapper.server.Server)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (next : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (rawBefore : Nat) (invoked : Bool) :
    RegistrationNativePlatformSdkOrdinarySnapshot.Server n KemSK Platform mlSource :=
  ⟨AdapterPublicOrdinaryServerLookup.restore self (some remote) back (some (AdapterPublicOrdinaryEnvelope.manager kernel)),
    (RegistrationNativePlatformOrdinaryExperiment.replaceWorld before {before.server.world.world.1 with primitive:=primitive},next),
    tag,frames,rawBefore,invoked⟩

def update (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (objects : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=mlSource) R)
    (reached : RegistrationNativePlatformSdkOrdinarySnapshot.Server n KemSK Platform mlSource) :=
  {objects with server:=reached.returned,snapshot:=reached.registrationSnapshot view views}

noncomputable def put (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native ×Platform)
    (before : Carrier (R:=R) view views joint created credential current)
    (key : U64) (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer before.objects.server.known_ids query)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (next : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (rawBefore : Nat) (invoked : Bool) :
    Carrier (R:=R) view views joint created credential
      ((snapshot current.1 before.objects.server remote back kernel primitive frames next tag rawBefore invoked).committed view views) := by
  let reached:=snapshot current.1 before.objects.server remote back kernel primitive frames next tag rawBefore invoked
  have related:=AdapterPublicOrdinaryServerReifier.restored_material view views created credential
    before.objects.server current.1.server before.server key remote back lens
    (AdapterPublicOrdinaryEnvelope.manager kernel) kernel rfl reached.rawAfter
  refine {objects:=update view views before.objects reached
          server:=?_
          beacons:=before.beacons
          tokens:=before.tokens
          sessionCount:=before.sessionCount
          ownerCount:=before.ownerCount
          allocated:=before.allocated
          indexed:=before.indexed
          backend:=rfl}
  exact {identity:=related.identity
         control:=related.control
         pinIdentity:=related.pinIdentity
         pinIdentifier:=related.pinIdentifier
         pinMldsa:=related.pinMldsa
         replay:=related.replay
         peers:=related.peers}

theorem put_objects (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native ×Platform)
    (before : Carrier (R:=R) view views joint created credential current)
    (key : U64) (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer before.objects.server.known_ids query)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (next : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (rawBefore : Nat) (invoked : Bool) :
    (put view views joint created credential current before key remote back lens kernel primitive frames next tag rawBefore invoked).objects=
      update view views before.objects (snapshot current.1 before.objects.server remote back kernel primitive frames next tag rawBefore invoked) := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.put_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.put_objects
