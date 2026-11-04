-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceWorld
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! A source KEM object and caller RNG are represented from the SAME private generated pair before its public handle is returned. The actual native key-generation sampler, pool/history and complete World are preserved. The object/RNG realizer is a selected per-key functional representation; no private key is recovered from a public reply. This joint native receipt does not yet identify the realizer with the SDK generation method; that later per-key operation contract must include its exact returned RNG and availability. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorKem
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca (MlKem768PublicKey)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {ι KemSK R : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

structure Representation (view : AdapterPublicWrapperState.MaterialView source KemSK) (R : Type) where
  realize : MlKem768PublicKey → KemSK → R → beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair × R
  publicView : ∀ pk sk rng, view.kemPublic (realize pk sk rng).1.public_key = pk
  privateView : ∀ pk sk rng, view.kemSecret (realize pk sk rng).1.secret_key = sk

structure Receipt (R : Type) where
  born : Nat × MlKem768PublicKey
  pair : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair
  rng : R

abbrev Native (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) := RegistrationNativeExperiment.State n KemSK source

def after (before : Native n KemSK source) (pair : MlKem768PublicKey × KemSK) (world : PqxdhRecordLiftWorld.State n) : Native n KemSK source :=
  { before with
    pool := (PqxdhLiveKemBirth.created before.pool pair).2
    server := { before.server with world := { before.server.world with world := (world, before.server.world.world.2) } } }

def receipt (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : Representation view R)
    (before : Native n KemSK source) (pair : MlKem768PublicKey × KemSK) (rng : R) : Receipt R :=
  ⟨(before.pool.keys.length, pair.1), (model.realize pair.1 pair.2 rng).1, (model.realize pair.1 pair.2 rng).2⟩

noncomputable def jointSource (setup : Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : Representation view R) (rng : R) : StateT (Native n KemSK source) ProbComp (Receipt R) := fun before =>
  (fun result => (receipt view model before result.1 rng, after before result.1 result.2)) <$>
    (PqxdhRecordLiftWorld.sampled (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)).run before.server.world.world.1

theorem native_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : Representation view R) (rng : R) (before : Native n KemSK source) :
    Prod.map Receipt.born id <$> (jointSource setup view model rng).run before =
    (RegistrationNativeExperiment.trusted setup checks representation created source (.inr (.inr (.inl .create)))).run before := by
  have generated := RegistrationNativeKemInterface.create_source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
    (RegistrationNativeKemBackend.serverOther setup checks representation created.seed)
    (before.server.world.auxiliary, before.pool)
  change Prod.map Receipt.born id <$> (jointSource setup view model rng).run before =
    (do
      let result ← (PqxdhRecordLiftWorld.sampled
        ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) (.inr (.inl .create))).run
            (before.server.world.auxiliary, before.pool))).run before.server.world.world.1
      pure (result.1.1, { before with pool := result.1.2.2, server := { before.server with world :=
        { before.server.world with auxiliary := result.1.2.1, world := (result.2, before.server.world.world.2) } } }))
  rw [generated, RegistrationNativeKemReferenceWorld.sampled_map]
  simp only [jointSource, StateT.run, Functor.map_map, bind_pure_comp, receipt, after, Prod.map_def, id_eq]

variable {m : Type → Type} [Monad m] [LawfulMonad m]
noncomputable def joint (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : Representation view R) (rng : R) :
    StateT (Native n KemSK source) m (Receipt R) := RegistrationNativePlatformInterpret.state coins (jointSource setup view model rng)

theorem native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : Representation view R) (rng : R) (before : Native n KemSK source) :
    Prod.map Receipt.born id <$> (joint coins setup view model rng).run before =
    (RegistrationNativePlatformInterpret.state coins
      (RegistrationNativeExperiment.trusted setup checks representation created source (.inr (.inr (.inl .create))))).run before := by
  change Prod.map Receipt.born id <$> simulateQ coins ((jointSource setup view model rng).run before) = _
  rw [← simulateQ_map, native_source setup checks representation created view model rng before]
  rfl

omit [Monad m] [LawfulMonad m] in
theorem key_material (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : Representation view R)
    (before : Native n KemSK source) (pair : MlKem768PublicKey × KemSK) (world : PqxdhRecordLiftWorld.State n) (rng : R) :
    AdapterPublicWrapperState.KemPair view (after before pair world).pool (receipt view model before pair rng).pair
      (receipt view model before pair rng).born.1 (receipt view model before pair rng).born.2 := by
  constructor
  · exact model.publicView _ _ _
  · simp only [after, receipt, PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, model.privateView]
    simp

end BeaconcryptCore.Refinement.AdapterBeaconConstructorKem

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKem.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKem.native_source

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKem.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKem.native

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKem.key_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKem.key_material
