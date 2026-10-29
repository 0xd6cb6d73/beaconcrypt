-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! A successful concrete source constructor retains a key pair from the actual KEM generator. Its opaque generated-key index is taken from the reached private pool, independently of public-key byte aliases. Both callback supports come from the actual constructor control flow. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend
open RegistrationNativeBeaconBirth
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}

theorem trusted_env_pool (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (mlSource : RegistrationNativeMldsa.Source)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (result : (PqxdhRecordLiftInterface.EnvEffects n).Range query × RegistrationNativeExperiment.State n KemSK mlSource)
    (supported : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created mlSource
      (.inl query)).run before)) : result.2.pool = before.pool := by
  simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
    RegistrationNativeExperiment.server, StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

/-- This endpoint starts with the complete constructor, rather than a caller-supplied generated-key receipt. -/
theorem create_generated (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (mlSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State mlSource) (env : EnvState Auxiliary)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource)
    (index : Nat) (ownersAfter : State mlSource) (envAfter : EnvState Auxiliary)
    (supported : (((.ok (some index), ownersAfter), envAfter), after) ∈ support
      ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((create setup mlSource edPin mlPin keyId).run owners).run env)).run before)) :
    ∃ (prepared : Prepared mlSource) (leadingOwners : State mlSource) (leadingEnv : EnvState Auxiliary)
      (middle : RegistrationNativeExperiment.State n KemSK mlSource)
      (born : Nat × PqxdhKemIndCca.MlKem768PublicKey)
      (afterBirth : RegistrationNativeExperiment.State n KemSK mlSource) (worldOwner : Nat)
      (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK),
      (((.ok (some prepared), leadingOwners), leadingEnv), middle) ∈ support
        ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((prepare mlSource edPin mlPin keyId).run owners).run env)).run before) ∧
      pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) ∧
      born = (middle.pool.keys.length, pair.1) ∧
      afterBirth.pool.keys = middle.pool.keys ++ [pair] ∧
      after.pool = afterBirth.pool ∧
      index = leadingOwners.length ∧
      ownersAfter = leadingOwners ++
        [owner setup mlSource prepared.pin prepared.credentials prepared.identity prepared.prekey born worldOwner] ∧
      envAfter = leadingEnv := by
  obtain ⟨prepared, leadingOwners, leadingEnv, middle, earlier, appended⟩ :=
    RegistrationNativeBeaconBirth.create_supported setup mlSource
      (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
      edPin mlPin keyId owners env before index ownersAfter envAfter after supported
  obtain ⟨born, afterBirth, worldOwner, final, generated, allocated, returned⟩ :=
    append_supported setup mlSource (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
      edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey leadingOwners leadingEnv middle _ appended
  obtain ⟨pair, genuine, bornEq, poolEq⟩ := RegistrationNativeExperiment.trusted_create_generated
    setup checks representation created mlSource middle (born, afterBirth) generated
  have retained := trusted_env_pool setup checks representation created mlSource
    (.inr (.appendOwner keyId edPin .fresh)) afterBirth (worldOwner, final) allocated
  have finalEq : after = final := congrArg Prod.snd returned
  have envEq : envAfter = leadingEnv := congrArg (fun result => result.1.2) returned
  have ownersEq := congrArg (fun result => result.1.1.2) returned
  have indexEq : index = leadingOwners.length := Option.some.inj (RustM.ok.inj
    (congrArg (fun result => result.1.1.1) returned))
  exact ⟨prepared, leadingOwners, leadingEnv, middle, born, afterBirth, worldOwner, pair,
    earlier, genuine, bornEq, poolEq, (congrArg (fun state => state.pool) finalEq).trans retained,
    indexEq, ownersEq, envEq⟩

/-- The actual deployment wrapper returns a local owner whose opaque handle selects the genuine generated pair in its reached private pool. -/
theorem owner_generated (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (mlSource : RegistrationNativeMldsa.Source)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : RegistrationNativeExperiment.State n KemSK mlSource) (index : Nat)
    (supported : (.ok (some index), after) ∈ support
      ((RegistrationNativeExperiment.beacon setup checks representation created
        (create setup mlSource edPin mlPin keyId)).run before)) :
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen),
      ∃ selected, after.beacons[index]? = some selected ∧ selected.kemPublic = pair.1 ∧
        after.pool.keys[selected.kemHandle]? = some pair := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨⟨⟨⟨value, ownersAfter⟩, envAfter⟩, sourceAfter⟩, reached, returned⟩ := supported
  have valueEq : value = .ok (some index) := congrArg Prod.fst returned.symm
  subst value
  obtain ⟨prepared, leadingOwners, leadingEnv, middle, born, afterBirth, worldOwner, pair,
    _earlier, genuine, bornEq, poolEq, retained, indexEq, ownersEq, _envEq⟩ :=
      create_generated setup checks representation created mlSource edPin mlPin keyId before.beacons
        (RegistrationWorldAgreementCompiler.erase before.server.world) before sourceAfter index ownersAfter envAfter reached
  have beaconsEq : after.beacons = ownersAfter := congrArg (fun result => result.2.beacons) returned
  have poolAfter : after.pool = sourceAfter.pool := congrArg (fun result => result.2.pool) returned
  refine ⟨pair, genuine, owner setup mlSource prepared.pin prepared.credentials prepared.identity prepared.prekey born worldOwner, ?_, ?_, ?_⟩
  · rw [beaconsEq]
    simp only [ownersEq, indexEq, List.getElem?_concat_length]
  · exact congrArg Prod.snd bornEq
  · rw [poolAfter]
    simp only [owner, retained, poolEq, bornEq, List.getElem?_concat_length]

end BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource.trusted_env_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource.trusted_env_pool

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource.create_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource.create_generated

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource.owner_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconBirthSource.owner_generated
