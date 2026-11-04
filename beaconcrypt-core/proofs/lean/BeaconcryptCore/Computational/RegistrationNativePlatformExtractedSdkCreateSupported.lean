-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit
import BeaconcryptCore.Computational.RegistrationNativeCreateHandle
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
/-! Source constructor receipts commit only literal owner registration after capture. The backend erasure retains the exact captured source state, environment and platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformExtractedSdkCreateReceipt (SourceM Packet Result)
variable {n : Nat} {I KemSK R Error Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)


theorem native (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (packet : Result n KemSK R source)
    (supported : (packet,next)∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous)) :
    (RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet,next)∈support
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId))).run before).run previous) := by
  have equation := congrArg (fun work =>work.run previous)
    (RegistrationNativePlatformExtractedSdkCreateCommon.native coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before)
  simp only [StateT.run_map] at equation
  rw [←equation,support_map]
  exact ⟨(packet,next),supported,rfl⟩

theorem backend (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (packet : Result n KemSK R source)
    (supported : (packet,next)∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous)) :
    RegistrationNativePlatformSdkReification.persistent ((RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2,next)=
      RegistrationNativePlatformSdkReification.persistent (packet.1.1.1.sourceAfter,next) := by
  obtain ⟨captured,owners,environment,current,_called,equal⟩ :=
    RegistrationNativePlatformExtractedSdkCreateCommit.decompose coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before previous next packet supported
  subst packet
  exact RegistrationNativePlatformExtractedSdkCreateCommit.backend coins setup checks representation created generator view kem leaves keyId serverId captured owners environment current next

theorem reply (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (packet : Result n KemSK R source)
    (supported : (packet,next)∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous)) :
    RegistrationNativePlatformExtractedSdkCreateCommit.observe before.beacons.length packet.1.1.1.outcome=packet.1.1.1.reply := by
  have called := native coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before previous next packet supported
  obtain ⟨captured,owners,environment,current,_joint,equal⟩ :=
    RegistrationNativePlatformExtractedSdkCreateCommit.decompose coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before previous next packet supported
  subst packet
  cases selected : captured.1 with
  | none =>
      simp only [RegistrationNativePlatformExtractedSdkCreateCommit.result,
        RegistrationNativePlatformExtractedSdkCreateCommit.observe,AdapterBeaconConstructorNative.sourceResult,
        AdapterBeaconConstructorJoint.sourceResult,selected]
  | some generated =>
      have indexReceipt : ((.ok (some owners.length),
          (RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection
            (RegistrationNativePlatformExtractedSdkCreateCommit.result coins setup checks representation created generator view kem leaves keyId serverId captured owners environment current)).2),next)∈support
        (((RegistrationNativePlatformExperiment.liftNative coins
          (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId))).run before).run previous) := by
        simpa only [RegistrationNativePlatformExtractedSdkCreateCommit.result,selected,
          RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection] using called
      have indexSame := RegistrationNativeCreateHandle.platform coins setup checks representation created
        (view.edPublic serverId) mlPin keyId before _ previous next owners.length indexReceipt
      rw [←indexSame]
      exact RegistrationNativePlatformExtractedSdkCreateCommit.reply coins setup checks representation created generator view kem leaves keyId serverId captured owners environment current

theorem entry_support (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (packet : Result n KemSK R source)
    (supported : (packet,next)∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous)) :
    (((((packet.1.1.1.reply,packet.1.1.1.outcome),packet.1.1.2),packet.1.2),packet.2),next)∈support
      (((((AdapterBeaconConstructorNative.entry coins setup checks representation created generator view kem leaves keyId serverId mlPin rng).run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)).run before).run previous) := by
  have equation := congrArg (fun work =>(((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)).run before).run previous)
    (RegistrationNativePlatformExtractedSdkCreateReceipt.erases coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)
  simp only [StateT.run_map] at equation
  rw [←equation,support_map]
  exact ⟨(packet,next),supported,rfl⟩

theorem created_material (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng afterRng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (packet : Result n KemSK R source)
    (supported : (packet,next)∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous))
    (index : Nat) (stored : beaconcrypt_public_wrapper.beacon.Beacon)
    (reply : packet.1.1.1.reply=.ok (some index)) (outcome : packet.1.1.1.outcome=(.Ok stored,afterRng)) :
    ∃owner,(RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2.beacons[index]?=some owner ∧
      AdapterPublicWrapperState.Beacon view setup.joint
        (RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2.pool stored owner
        (RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2.server.world.world.1.owners[owner.worldOwner]? := by
  have reached := entry_support coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before previous next packet supported
  rw [reply,outcome] at reached
  exact AdapterBeaconConstructorReached.entry_material coins setup checks representation created generator view kem leaves keyId serverId mlPin rng afterRng
    before.beacons packet.1.1.2 (RegistrationWorldAgreementCompiler.erase before.server.world) packet.1.2 before packet.2 previous next index stored reached

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.reply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.entry_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.entry_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.created_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported.created_material
