-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreate
/-! Capture the actual constructor source snapshot before the model's pure registration administration. Erasing this capture recovers the original common source/native constructor exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
variable {n : Nat} {I KemSK R Error Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
abbrev SourceM (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT Platform ProbComp)

def snapshot : SourceM n KemSK source Platform (RegistrationNativeExperiment.State n KemSK source) :=
  fun owners environment before => pure (((RegistrationNativeFinishTerminalTree.assemble owners environment before,owners),environment),before)

private theorem snapshot_run (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (((snapshot (Platform := Platform)).run owners).run environment).run before=
      pure (((RegistrationNativeFinishTerminalTree.assemble owners environment before,owners),environment),before) := rfl

private theorem snapshot_erase (work : SourceM n KemSK source Platform A) :
    (snapshot *>work)=work := by
  funext owners environment before
  change ((snapshot *>work).run owners |>.run environment |>.run before)=_
  simp only [seqRight_eq_bind,StateT.run_bind]
  rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
structure Packet (n : Nat) (KemSK R : Type) (source : RegistrationNativeMldsa.Source) where
  outcome : AdapterBeaconConstructorBody.Outcome R
  sourceAfter : RegistrationNativeExperiment.State n KemSK source
  reply : RustM (Option Nat)

def forget (packet : Packet n KemSK R source) : RustM (Option Nat) ×AdapterBeaconConstructorBody.Outcome R :=
  (packet.reply,packet.outcome)

variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (kem : AdapterBeaconConstructorKem.Representation view R)

noncomputable def commit
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (captured : Option (AdapterBeaconConstructorJoint.Capture source R) ×R) :
    SourceM n KemSK source Platform (Packet n KemSK R source) := do
  let sourceAfter ← snapshot
  let outcome := AdapterBeaconConstructorNative.sourceResult coins setup checks representation created generator view kem leaves keyId serverId captured
  let reply ← match captured.1 with
    | none => pure (.ok none)
    | some (ready,generated) =>
      AdapterBeaconConstructorNative.lift coins setup checks representation created
        (RegistrationNativeBeaconCreateEntry.register setup (view.edPublic serverId) keyId ready generated.born)
  pure ⟨outcome,sourceAfter,reply⟩


noncomputable def program
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R) :
    SourceM n KemSK source Platform (Packet n KemSK R source) := do
  let captured ← AdapterBeaconConstructorNative.joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng
  commit coins setup checks representation created generator view kem leaves keyId serverId captured

theorem erases
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R) :
    forget <$> program coins setup checks representation created generator view kem leaves keyId serverId mlPin rng=
      AdapterBeaconConstructorNative.entry coins setup checks representation created generator view kem leaves keyId serverId mlPin rng := by
  unfold program AdapterBeaconConstructorNative.entry
  rw [map_bind]
  apply bind_congr
  intro captured
  unfold commit
  cases selected : captured.1 with
  | none =>
      simp only [map_bind,map_pure,forget,pure_bind]
      exact snapshot_erase _
  | some generated =>
      rcases generated with ⟨ready,generated⟩
      simp only [map_bind,map_pure,forget]
      exact snapshot_erase _

abbrev Result (n : Nat) (KemSK R : Type) (source : RegistrationNativeMldsa.Source) :=
  ((Packet n KemSK R source ×RegistrationNativeBeaconFrontend.State source) ×
    RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×RegistrationNativeExperiment.State n KemSK source

def sourceWord (result : Result n KemSK R source) : AdapterBeaconConstructorBody.Outcome R ×RegistrationNativeExperiment.State n KemSK source :=
  (result.1.1.1.outcome,result.1.1.1.sourceAfter)

theorem commit_source
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (captured : Option (AdapterBeaconConstructorJoint.Capture source R) ×R)
    (owners : RegistrationNativeBeaconFrontend.State source)
    (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    sourceWord <$> (((commit coins setup checks representation created generator view kem leaves keyId serverId captured).run owners).run environment).run before=
      pure (AdapterBeaconConstructorNative.sourceResult coins setup checks representation created generator view kem leaves keyId serverId captured,
        RegistrationNativeFinishTerminalTree.assemble owners environment before) := by
  unfold commit
  simp only [StateT.run_bind]
  rw [snapshot_run,pure_bind]
  cases chosen : captured.1 with
  | none =>
      simp only [pure_bind,StateT.run_pure,map_pure,sourceWord]
  | some generated =>
      rcases generated with ⟨ready,generated⟩
      simp only [StateT.run_bind]
      rw [AdapterBeaconConstructorNativeRegister.register_exact]
      simp only [map_pure,pure_bind,StateT.run_pure,sourceWord]

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt.erases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt.erases
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt.commit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt.commit_source
