-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRealization
import BeaconcryptCore.Computational.RegistrationNativeEnvSampling

/-! The concrete indexed identity birth draws the actual private seed at the constructor position, retains both original counter increments, and gives the returned public credential precisely that stored seed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context State implementation)
open RegistrationNativeIdentityInterface (Credential)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def advance (before : Context n KemSK) : Context n KemSK :=
  { before with server := { before.server with world := { before.server.world with
    world := (RegistrationNativeEnvSampling.advance 32 before.server.world.world.1, before.server.world.world.2) } } }

def born (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK) (seed : PqxdhJointIdentity.IdentitySeed) : State n KemSK :=
  ⟨advance before.context, (PqxdhDynamicIdentityPool.createdReply joint before.identities seed).2⟩

def credential (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK) (seed : PqxdhJointIdentity.IdentitySeed) : Credential :=
  ⟨before.identities.seeds.length, joint.publicKeys seed⟩

private theorem seed (before : PqxdhRecordLiftWorld.State n) :
    (simulateQ RegistrationWorldCoinCompiler.coin PqxdhJointIdentity.sampleSeed).run before =
      (fun value => (value, RegistrationNativeEnvSampling.advance 32 before)) <$> PqxdhJointIdentity.sampleSeed :=
  RegistrationNativeEnvSampling.bytes 32 before

/-- The actual source query counts and stores its one seed before publishing the exact generated index and correlated public keys. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : State n KemSK) :
    (implementation (mlSource := source) setup checks representation created (.inr .create)).run before =
      (fun value => (some (before.identities.seeds.length, setup.joint.publicKeys value), born setup.joint before value)) <$>
        PqxdhJointIdentity.sampleSeed := by
  change (do
    let result ← (simulateQ RegistrationWorldCoinCompiler.coin
      ((PqxdhDynamicIdentityPool.lazyImpl setup.joint (.inr .create)).run before.identities)).run before.context.server.world.world.1
    pure (result.1.1, { before with identities := result.1.2, context := { before.context with server := { before.context.server with
      world := { before.context.server.world with world := (result.2, before.context.server.world.world.2) } } } })) = _
  rw [PqxdhDynamicIdentityPool.lazyImpl_create]
  simp only [simulateQ_map, StateT.run_map, seed, bind_pure_comp, Functor.map_map,
    born, advance, PqxdhDynamicIdentityPool.createdReply]

/-- The actual public identity-create wrapper returns only a generated public credential, retaining the complete original World and actual private pool. -/
theorem create_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : State n KemSK) :
    (simulateQ (implementation (mlSource := source) setup checks representation created)
      (RegistrationNativeIdentityInterface.create (RegistrationNativeIdentityFrontend.Ambient n KemSK))).run before =
      (fun value => (some (credential setup.joint before value), born setup.joint before value)) <$>
        PqxdhJointIdentity.sampleSeed := by
  simp only [RegistrationNativeIdentityInterface.create, simulateQ_map, simulateQ_spec_query,
    StateT.run_map]
  rw [query_source (source := source) setup checks representation created before]
  simp only [Functor.map_map, Option.map_some, credential]

/-- The generated public credential realizes to exactly its privately stored source seed, without any injectivity assumption. -/
theorem seed_found (joint : PqxdhJointIdentity.Primitives) (before : State n KemSK) (value : PqxdhJointIdentity.IdentitySeed) :
    RegistrationNativeIdentityRealization.seedFor (born joint before value).identities (credential joint before value) = value := by
  simp only [RegistrationNativeIdentityRealization.seedFor, born, credential,
    PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record,
    List.getElem?_append, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth.create_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth.seed_found' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth.seed_found
