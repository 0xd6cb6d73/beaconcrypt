-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinarySnapshot
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot
open BeaconcryptCore.Refinement
open AdapterPublicWrapperStorage
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

theorem committed (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : Views)
    (before : Native) (self : beaconcrypt_public_wrapper.server.Server) (key : U64)
    (remote : Remote ed.PublicKey) (back : Option (Remote ed.PublicKey) →PeerMap)
    (lens : ∀changed query,views.peer (back changed) query=if query=key then changed else views.peer self.known_ids query)
    (server : PqxdhRecordLiftWorld.Server)
    (matched : AdapterPublicOrdinaryServerReifier.server view views self server.records.rawAttempts=server)
    (kernel afterKernel : ratchet.concrete.ConcreteRatchetKernel)
    (reply : Option beaconcrypt.shared.Decrypted)
    (primitive : PqxdhRecordLiftWorld.Primitive) (frames : PqxdhRecordLiftLoggedAdapters.Frames) (next : Platform) :
    let packet:=RegistrationNativePlatformExtractedSdkOrdinary.pack before server.records.rawAttempts true
      ((RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned self remote back (.ok (afterKernel,reply)),(primitive,frames)),next)
    (RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot (PqxdhDeploymentNative.serverTag (.inr [])) packet
      (AdapterPublicOrdinaryServerLookup.restore self (some remote) back
        (some (AdapterPublicOrdinaryEnvelope.manager afterKernel)))).committed view views =
    let result:=RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.project before.server.world.world.1 server key
      ⟨remote.peer.binding.beacon_identity_public_key,kernel,remote.peer.binding.associated_data⟩
      ((.ok (afterKernel,reply),(primitive,frames)),next)
    (RegistrationNativePlatformOrdinaryExperiment.replaceWorld before result.1.2,result.2) := by
  have shifted : AdapterPublicOrdinaryServerReifier.server view views self (server.records.rawAttempts+1)=
      {server with records:={server.records with rawAttempts:=server.records.rawAttempts+1}} := by
    conv_rhs=>rw [←matched]
    rfl
  have records:=RegistrationNativePlatformExtractedSdkOrdinaryServerSendSnapshot.restore_record view views self key remote back lens kernel afterKernel (server.records.rawAttempts+1)
  rw [shifted] at records
  dsimp only [RegistrationNativePlatformExtractedSdkOrdinary.serverSnapshot,
    RegistrationNativePlatformExtractedSdkOrdinary.pack,RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSource.returned,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.committed,RegistrationNativePlatformSdkOrdinarySnapshot.Server.world,
    RegistrationNativePlatformSdkOrdinarySnapshot.Server.rawAfter]
  simp only [ite_true]
  rw [records]
  cases reply <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot.committed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveSnapshot.committed
