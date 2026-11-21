-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
open RegistrationNativePlatformExtractedSdkCarrier (Carrier Objects)
variable {n : Nat} {KemSK Platform R : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

def snapshot (before : Native) (self : beaconcrypt_public_wrapper.server.Server)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (next : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (rawBefore : Nat) (invoked : Bool) :
    RegistrationNativePlatformSdkOrdinarySnapshot.Server n KemSK Platform mlSource :=
  ⟨self,(RegistrationNativePlatformOrdinaryExperiment.replaceWorld before {before.server.world.world.1 with primitive:=primitive},next),
    tag,frames,rawBefore,invoked⟩

noncomputable def put (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native ×Platform)
    (before : Carrier (R:=R) view views joint created credential current)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (next : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (rawBefore : Nat) (invoked : Bool) :
    Carrier (R:=R) view views joint created credential
      ((snapshot current.1 before.objects.server primitive frames next tag rawBefore invoked).committed view views) := by
  let reached:=snapshot current.1 before.objects.server primitive frames next tag rawBefore invoked
  refine {objects:=RegistrationNativePlatformExtractedSdkCarrierOrdinaryServer.update view views before.objects reached
          server:=?_
          beacons:=before.beacons
          tokens:=before.tokens
          sessionCount:=before.sessionCount
          ownerCount:=before.ownerCount
          allocated:=before.allocated
          indexed:=before.indexed
          backend:=rfl}
  refine {identity:=before.server.identity
          control:=before.server.control
          pinIdentity:=before.server.pinIdentity
          pinIdentifier:=before.server.pinIdentifier
          pinMldsa:=before.server.pinMldsa
          replay:=before.server.replay
          peers:=?_}
  obtain ⟨records,_present,_sender,_identity,matched⟩:=before.server.peers
  refine ⟨AdapterPublicOrdinaryServerReifier.server view views before.objects.server reached.rawAfter,rfl,
    before.server.identity.identifier,before.server.identity.publicKey,?_⟩
  intro key
  exact ⟨rfl,(matched key).2.trans (congrArg Option.isSome (matched key).1.symm)⟩

theorem objects (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (joint : PqxdhJointIdentity.Primitives) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native ×Platform)
    (before : Carrier (R:=R) view views joint created credential current)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames)
    (next : Platform) (tag : PqxdhDeploymentInterface.FrameTag) (rawBefore : Nat) (invoked : Bool) :
    (put view views joint created credential current before primitive frames next tag rawBefore invoked).objects=
      {before.objects with snapshot:=.direct ((snapshot current.1 before.objects.server primitive frames next tag rawBefore invoked).committed view views)} := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierOrdinaryServerRetain.objects
