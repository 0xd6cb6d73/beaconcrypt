-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle
import BeaconcryptCore.Computational.RegistrationNativeBundleSafety
/-! Complete actual native Fresh and FreshWithCoins bundle executions are explicit projections of one same-run publication tree, including the real sample, failed writer effects, private pool, native histories and final pending World slot. The publication frame derives terminal readiness from source material; no successful-advance premise is supplied. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundleLifetime
open RegistrationNativeBeaconFrontend (Owner)
variable {n : Nat} {I KemSK E Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def tree (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformFrontend.interpret
    (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformBeaconPublication.begin
      (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
      (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey)

theorem tree_lower (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    tree (n := n) coins setup checks representation created writer index owner scalar =
      RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner)
        (RegistrationNativeBundleInterpretation.encoder coins setup checks representation created writer)
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey := by
  unfold tree
  exact RegistrationNativeBundleInterpretation.publication coins setup checks representation created writer index owner _ _ _ _ _

noncomputable def sample : RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) PqxdhJointGapDh.ScalarBytes :=
  RegistrationNativePlatformFrontend.interpret
    (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))

theorem publish_exact (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Native) (previous : Platform)
    (ready : RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner) :
    (((RegistrationNativePlatformFrontend.interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativeBundleLifecycle.publish setup index owner scalar)).run before).run previous) =
      (fun result => ((RegistrationNativeBundleLifecycle.value result.1.1,
        RegistrationNativeBundleLifecycle.after index owner scalar result.1.1 result.1.2), result.2)) <$>
        ((tree coins setup checks representation created writer index owner scalar).run before).run previous := by
  rw [RegistrationNativeBundleLifecycle.publish_interpret, ← tree_lower coins setup checks representation created writer index owner scalar]
  change ((do
    let published ← tree coins setup checks representation created writer index owner scalar
    RegistrationNativePlatformFrontend.interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativeBundleLifecycle.terminal index owner scalar published) :
      RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp) _).run before).run previous = _
  simp only [StateT.run_bind]
  rw [← bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result reached
  have kept := RegistrationNativeBundleSafety.interpreted_snapshot coins setup checks representation created writer _
    (RegistrationNativeBundleSafety.publication_safe setup index owner scalar) before previous result reached
  have owners : result.1.2.server.world.world.1.owners = before.server.world.world.1.owners := congrArg Prod.fst kept
  have terminalReady : RegistrationNativeBundleTerminal.Ready result.1.2.server.world.world.1 owner.worldOwner := by
    simpa only [RegistrationNativeBundleTerminal.Ready, owners] using ready
  rw [RegistrationNativeBundleLifecycle.terminal_exact coins setup checks representation created writer index owner scalar result.1.1 result.1.2 terminalReady]
  rfl

theorem with_coins (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Native) (previous : Platform) (selected : before.beacons[index]? = some owner)
    (phase : owner.phase = .freshWithCoins scalar)
    (ready : RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner) :
    (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous) =
      (fun result => ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1),
        RegistrationNativeBundleLifecycle.after index owner scalar result.1.1 result.1.2), result.2)) <$>
        ((tree coins setup checks representation created writer index owner scalar).run before).run previous := by
  rw [RegistrationNativePlatformFrontend.actual_bundle, StateT.run_map, StateT.run_map,
    RegistrationNativeBundleLifecycle.with_coins coins setup checks representation created writer index owner scalar before selected phase,
    publish_exact coins setup checks representation created writer index owner scalar before previous ready,
    Functor.map_map]


noncomputable def fresh_tree (index : Nat) (owner : Owner source) :
    RegistrationNativePlatformExperiment.M n KemSK source (StateT Platform ProbComp)
      (PqxdhJointGapDh.ScalarBytes × RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) := do
  let scalar ← sample coins setup checks representation created writer
  let published ← tree coins setup checks representation created writer index owner scalar
  pure (scalar, published)

theorem fresh (index : Nat) (owner : Owner source) (before : Native) (previous : Platform)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .fresh)
    (ready : RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner) :
    (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous) =
      (fun result => ((RegistrationNativePlatformFrontend.publicBytes (RegistrationNativeBundleLifecycle.value result.1.1.2),
        RegistrationNativeBundleLifecycle.after index owner result.1.1.1 result.1.1.2 result.1.2), result.2)) <$>
        ((fresh_tree coins setup checks representation created writer index owner).run before).run previous := by
  rw [RegistrationNativePlatformFrontend.actual_bundle, StateT.run_map, StateT.run_map,
    RegistrationNativeBundleLifecycle.fresh coins setup checks representation created writer index owner before selected phase]
  simp only [fresh_tree, StateT.run_bind, bind_pure_comp, StateT.run_map, map_bind, Functor.map_map]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro drawn reached
  have kept := RegistrationNativeBundleSafety.sample_snapshot coins setup checks representation created writer
    PqxdhJointGapDh.sampleScalar before previous drawn reached
  have owners : drawn.1.2.server.world.world.1.owners = before.server.world.world.1.owners := congrArg Prod.fst kept
  have terminalReady : RegistrationNativeBundleTerminal.Ready drawn.1.2.server.world.world.1 owner.worldOwner := by
    simpa only [RegistrationNativeBundleTerminal.Ready, owners] using ready
  have actual := congrArg (fun distribution => (fun result => ((RegistrationNativePlatformFrontend.publicBytes result.1.1, result.1.2), result.2)) <$> distribution)
    (publish_exact coins setup checks representation created writer index owner drawn.1.1 drawn.1.2 drawn.2 terminalReady)
  simpa only [Functor.map_map] using actual

variable [material : BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [ed : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
theorem fresh_ready (view : BeaconcryptCore.Refinement.AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (before : Native)
    (related : BeaconcryptCore.Refinement.AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh) :
    RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner := by
  have data := related.phase
  simp only [BeaconcryptCore.Refinement.AdapterPublicWrapperState.Phase, stored, phase] at data
  exact Or.inl data.2.2.2

theorem with_coins_ready (view : BeaconcryptCore.Refinement.AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (before : Native)
    (related : BeaconcryptCore.Refinement.AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (control : pqxdh.BeaconFresh) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .FreshWithCoins control prekey oneTime kem) (phase : owner.phase = .freshWithCoins scalar) :
    RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner := by
  have data := related.phase
  simp only [BeaconcryptCore.Refinement.AdapterPublicWrapperState.Phase, stored, phase] at data
  exact Or.inr data.2.2.2.2

end BeaconcryptCore.Computational.RegistrationNativeBundleLifetime

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.tree_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.tree_lower

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.publish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.publish_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.with_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.fresh_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.fresh_ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.with_coins_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifetime.with_coins_ready
