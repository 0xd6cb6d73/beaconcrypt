-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorNative
import BeaconcryptCore.Refinement.AdapterBeaconConstructorMaterial
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKemSupport
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Registration of the SAME returned SDK object appends the actual native owner and actual World slot. This administration is outside the physical SDK constructor. Newly generated material is derived from individual key views, the same reached private KEM row, and the actual pin binding. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open AdapterBeaconConstructorNative (M Leaves lift)
variable {n : Nat} {ι KemSK R Error Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (M n KemSK source Auxiliary m))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (M n KemSK source Auxiliary m))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (M n KemSK source Auxiliary m))]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : Leaves (n := n) (Auxiliary := Auxiliary) coins setup checks representation created generator view kem)

omit [LawfulMonad m] in
theorem object_related (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (ready : RegistrationNativeBeaconFrontend.Prepared source) (receipt : AdapterBeaconConstructorKem.Receipt R)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (worldOwner : Nat)
    (binding : ready.pin.binding = ⟨view.edPublic serverId, keyId⟩)
    (kemRow : AdapterPublicWrapperState.KemPair view pool receipt.pair receipt.born.1 receipt.born.2) :
    AdapterPublicWrapperState.Beacon view setup.joint pool
      (AdapterBeaconConstructorJoint.object generator view _ leaves.ml setup.joint _ leaves.ed _ _ leaves.kx keyId serverId (ready, receipt))
      (RegistrationNativeBeaconBirth.owner setup source ready.pin ready.credentials ready.identity ready.prekey receipt.born worldOwner)
      (some (.inactive .fresh)) := by
  constructor
  · exact leaves.ed.publicView _
  · exact leaves.ed.privateView _
  · exact leaves.ml.privateView _
  · rfl
  · exact congrArg pqxdh.ServerBinding.identity_public_key binding.symm
  · exact congrArg pqxdh.ServerBinding.identity_key_id binding.symm
  · exact ⟨rfl, ⟨leaves.kx.privateView _, leaves.kx.publicView _⟩, kemRow, rfl⟩

omit generators crypto children material primitive [LawfulMonad m] in
theorem append_interpret (keyId : U64) (edPin : Std.Array U8 32#usize)
    (before : AdapterBeaconConstructorKem.Native n KemSK source) :
    ((AdapterBeaconConstructorKemLift.implementation coins setup checks representation created)
      (.inl (.inr (.appendOwner keyId edPin .fresh)))).run before =
      pure (before.server.world.world.1.owners.length, AdapterBeaconConstructorMaterial.appendNative keyId edPin before) := by
  change simulateQ coins ((RegistrationNativeExperiment.trusted setup checks representation created source
    (.inl (.inr (.appendOwner keyId edPin .fresh)))).run before) = _
  rw [AdapterBeaconConstructorMaterial.append_source, simulateQ_pure]

omit generators crypto children material primitive in
theorem register_exact (keyId : U64) (edPin : Std.Array U8 32#usize)
    (ready : RegistrationNativeBeaconFrontend.Prepared source) (born : Nat × PqxdhKemIndCca.MlKem768PublicKey)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : AdapterBeaconConstructorKem.Native n KemSK source) :
    (((lift coins setup checks representation created (RegistrationNativeBeaconCreateEntry.register setup edPin keyId ready born)).run owners).run env).run before =
      pure (((.ok (some owners.length), owners ++ [RegistrationNativeBeaconBirth.owner setup source ready.pin ready.credentials ready.identity ready.prekey born before.server.world.world.1.owners.length]), env),
        AdapterBeaconConstructorMaterial.appendNative keyId edPin before) := by
  change ((RegistrationNativePlatformGenericBundle.liftLegacy (AdapterBeaconConstructorKemLift.implementation coins setup checks representation created)
    (RegistrationNativeBeaconCreateEntry.register setup edPin keyId ready born)).run owners |>.run env |>.run before) = _
  rw [RegistrationNativeBeaconCreateEntry.register_run]
  simp only [bind_pure_comp, StateT.run_map]
  rw [append_interpret coins setup checks representation created]
  simp only [map_pure]

end BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister.object_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister.object_related

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister.append_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister.append_interpret

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister.register_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister.register_exact
