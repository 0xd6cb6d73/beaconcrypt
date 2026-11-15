-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySourceBirth

/-! Ordinary identity-frontend World effects execute against the same complete native context. Identity sampling and ordinary sampling therefore share actual Env counters, without a guessed source-state equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityWorld (Context ambient)
open PqxdhRecordLiftInterface (EnvEffects)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def withWorld (before : Context n KemSK) (world : PqxdhRecordLiftWorld.State n) : Context n KemSK :=
  { before with server := { before.server with world := { before.server.world with
    world := (world, before.server.world.world.2) } } }

/-- Every adaptive ordinary World-effect program preserves the complete context envelope and actual underlying World execution. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : OracleComp (EnvEffects n) Value)
    (before : Context n KemSK) :
    (simulateQ (ambient (mlSource := source) setup checks representation created)
      (simulateQ RegistrationBeaconReferenceNativeRecord.environment work)).run before =
      Prod.map id (withWorld before) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.server.world.world.1 := by
  rw [← QueryImpl.simulateQ_compose]
  have step (query : (EnvEffects n).Domain) (world : PqxdhRecordLiftWorld.State n) :
      Prod.map id (withWorld before) <$> (PqxdhRecordLiftWorld.effects query).run world =
        ((ambient (mlSource := source) setup checks representation created ∘ₛ
          RegistrationBeaconReferenceNativeRecord.environment) query).run (withWorld before world) := by
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, ambient, RegistrationNativeExperiment.trusted,
      RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
      RegistrationNativeIdentityWorld.project, RegistrationNativeIdentityWorld.embed,
      withWorld, StateT.run, Prod.map_def, id_eq, Functor.map_map]
    rfl
  simpa only [withWorld, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (withWorld before) step work before.server.world.world.1).symm

/-- Ordinary constructor coins keep their original Env and uniform charges on the same context. -/
theorem coins (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (work : ProbComp Value)
    (before : Context n KemSK) :
    (simulateQ (ambient (mlSource := source) setup checks representation created)
      (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (simulateQ RegistrationWorldCoinCompiler.envCoin work))).run before =
      Prod.map id (withWorld before) <$>
        (simulateQ RegistrationWorldCoinCompiler.coin work).run before.server.world.world.1 := by
  rw [program, RegistrationWorldCoinCompiler.env_program]

/-- An ordinary source seed draw reaches the exact same context as indexed generated identity birth. -/
theorem seed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (before : Context n KemSK) :
    (simulateQ (ambient (mlSource := source) setup checks representation created)
      (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (simulateQ RegistrationWorldCoinCompiler.envCoin PqxdhJointIdentity.sampleSeed))).run before =
      (fun value => (value, RegistrationNativeIdentitySourceBirth.advance before)) <$> PqxdhJointIdentity.sampleSeed := by
  rw [coins]
  have counted := RegistrationNativeEnvSampling.bytes 32 before.server.world.world.1
  change (simulateQ RegistrationWorldCoinCompiler.coin PqxdhJointIdentity.sampleSeed).run before.server.world.world.1 = _ at counted
  rw [counted, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects.coins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects.seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceEffects.seed
