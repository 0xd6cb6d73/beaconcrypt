-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit
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

noncomputable def result (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (captured : Option (AdapterBeaconConstructorJoint.Capture source R) ×R)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) : Result n KemSK R source :=
  let outcome := AdapterBeaconConstructorNative.sourceResult coins setup checks representation created generator view kem leaves keyId serverId captured
  let snapshot := RegistrationNativeFinishTerminalTree.assemble owners environment before
  match captured.1 with
  | none => (((⟨outcome,snapshot,.ok none⟩,owners),environment),before)
  | some (ready,generated) =>
    let nextOwner := RegistrationNativeBeaconBirth.owner setup source ready.pin ready.credentials ready.identity ready.prekey generated.born before.server.world.world.1.owners.length
    (((⟨outcome,snapshot,.ok (some owners.length)⟩,owners ++[nextOwner]),environment),
      AdapterBeaconConstructorMaterial.appendNative keyId (view.edPublic serverId) before)

theorem exact_result (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (captured : Option (AdapterBeaconConstructorJoint.Capture source R) ×R)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (((RegistrationNativePlatformExtractedSdkCreateReceipt.commit coins setup checks representation created generator view kem leaves keyId serverId captured).run owners).run environment).run before=
      pure (result coins setup checks representation created generator view kem leaves keyId serverId captured owners environment before) := by
  unfold RegistrationNativePlatformExtractedSdkCreateReceipt.commit
  simp only [StateT.run_bind]
  have snapshot : (((RegistrationNativePlatformExtractedSdkCreateReceipt.snapshot (Platform := Platform)).run owners).run environment).run before=
      pure (((RegistrationNativeFinishTerminalTree.assemble owners environment before,owners),environment),before) := rfl
  rw [snapshot,pure_bind]
  cases selected : captured.1 with
  | none => simp only [StateT.run_pure,pure_bind,result,selected]
  | some generated =>
      rcases generated with ⟨ready,generated⟩
      simp only [StateT.run_bind]
      rw [AdapterBeaconConstructorNativeRegister.register_exact]
      simp only [pure_bind,StateT.run_pure,result,selected]

theorem backend (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (captured : Option (AdapterBeaconConstructorJoint.Capture source R) ×R)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    let packet := result coins setup checks representation created generator view kem leaves keyId serverId captured owners environment before
    RegistrationNativePlatformSdkReification.persistent ((RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2,previous)=
      RegistrationNativePlatformSdkReification.persistent (packet.1.1.1.sourceAfter,previous) := by
  cases selected : captured.1 with
  | none => simp only [result,selected,RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection]
  | some generated =>
      simp only [result,selected,RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection,
        RegistrationNativePlatformSdkReification.persistent,RegistrationNativePlatformSdkReification.backend,
        RegistrationNativeFinishTerminalTree.assemble,AdapterBeaconConstructorMaterial.appendNative,
        AdapterBeaconConstructorMaterial.appendWorld,RegistrationWorldAgreementCompiler.join,
        RegistrationNativePlatformSdkReification.worldBackend,PqxdhRecordLiftWorld.chargeEffect,
        PqxdhRecordLiftInterface.effectKind,Function.update_idem]

def observe (nextOwner : Nat) (outcome : AdapterBeaconConstructorBody.Outcome R) : RustM (Option Nat) :=
  .ok (match outcome.1 with | .Err _ =>none | .Ok _ =>some nextOwner)

theorem reply (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (captured : Option (AdapterBeaconConstructorJoint.Capture source R) ×R)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    let packet := result coins setup checks representation created generator view kem leaves keyId serverId captured owners environment before
    observe owners.length packet.1.1.1.outcome=packet.1.1.1.reply := by
  cases selected : captured.1 with
  | none => simp only [result,observe,AdapterBeaconConstructorNative.sourceResult,AdapterBeaconConstructorJoint.sourceResult,selected]
  | some generated => simp only [result,observe,AdapterBeaconConstructorNative.sourceResult,AdapterBeaconConstructorJoint.sourceResult,selected]

theorem decompose (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (packet : Result n KemSK R source)
    (supported : (packet,next)∈support
      ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before).run previous)) :
    ∃captured owners environment current,
      (((((captured,owners),environment),current),next)∈support
        (((((AdapterBeaconConstructorNative.joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng).run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)).run before).run previous)) ∧
      packet=result coins setup checks representation created generator view kem leaves keyId serverId captured owners environment current := by
  simp only [RegistrationNativePlatformExtractedSdkCreateCommon.runner,RegistrationNativePlatformExtractedSdkCreateReceipt.program,
    StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨⟨⟨⟨captured,owners⟩,environment⟩,current⟩,middle⟩,called,continued⟩ := supported
  rw [exact_result coins setup checks representation created generator view kem leaves] at continued
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff,Prod.mk.injEq] at continued
  obtain ⟨returned,platformSame⟩ := continued
  subst middle
  exact ⟨captured,owners,environment,current,called,returned⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.exact_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.exact_result
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.backend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.reply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.decompose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommit.decompose
