-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

theorem restore_record (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (kernel afterKernel : ratchet.concrete.ConcreteRatchetKernel) (rawBefore : Nat) :
    AdapterPublicOrdinaryServerReifier.server view views
      (AdapterPublicOrdinaryServerLookup.restore self (some remote) back
        (some (AdapterPublicOrdinaryEnvelope.manager afterKernel))) rawBefore =
    let server:=AdapterPublicOrdinaryServerReifier.server view views self rawBefore
    {server with records:=⟨RawCtxServerRouting.putPeer server.records.server key
      ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩ afterKernel,rawBefore⟩} := by
  unfold AdapterPublicOrdinaryServerReifier.server
  rw [AdapterPublicOrdinaryServerReifier.restore_peers views self key remote back lens
    (AdapterPublicOrdinaryEnvelope.manager afterKernel) afterKernel rfl]
  rfl

theorem committed (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Native) (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (server : PqxdhRecordLiftWorld.Server)
    (matched : AdapterPublicOrdinaryServerReifier.server view views self server.records.rawAttempts=server)
    (kernel afterKernel : ratchet.concrete.ConcreteRatchetKernel)
    (reply : Option beaconcrypt_record_send.shared.Encrypted)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) (next : Platform) :
    let packet:=RegistrationNativePlatformExtractedSdkOrdinary.pack before server.records.rawAttempts false
      ((RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned self remote back (.ok (afterKernel,reply)),(primitive,frames)),next)
    (RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot (PqxdhDeploymentNative.serverTag (.inl ([],key))) packet
      (AdapterPublicOrdinaryServerLookup.restore self (some remote) back
        (some (AdapterPublicOrdinaryEnvelope.manager afterKernel)))).committed view views =
    let result:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.project before.server.world.world.1 server key
      ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩
      ((.ok (afterKernel,reply),(primitive,frames)),next)
    (RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2) := by
  have records:=restore_record view views self key remote back lens kernel afterKernel server.records.rawAttempts
  rw [matched] at records
  dsimp only [RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot,
    RegistrationNativePlatformExtractedSdkOrdinary.pack,RegistrationNativePlatformExtractedSdkOrdinarySendOperands.returned,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.committed,RegistrationNativePlatformSdkOrdinarySnapshot.Server.world,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.rawAfter]
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
  rw [records]
  cases reply <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.restore_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.restore_record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.committed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.committed
