-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarEagerLaws
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects

/-! The literal Beacon sampler closes on the same complete source World and Env coin counters. Selected-scalar interchange can therefore retain the entire native poststate, including pool, roster, receipts and both draw counters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceNativeEffects (embed)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem sample_effects (draw : ProbComp Value) :
    RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) draw =
      StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (simulateQ RegistrationWorldCoinCompiler.envCoin draw))) := by
  have composed : RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) ∘ₛ RegistrationWorldCoinCompiler.envCoin =
      (fun query => RegistrationNativeBeaconFrontend.effect (.inl query)) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationWorldCoinCompiler.envCoin, simulateQ_spec_query]
  rw [RegistrationNativeBeaconFrontend.sample, ← composed, QueryImpl.simulateQ_compose]
  change simulateQ ((RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK)).liftTarget
    (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
      (simulateQ RegistrationWorldCoinCompiler.envCoin draw) = _
  rw [simulateQ_liftTarget]
  rfl

/-- Literal constructor sampling closes to the original Env coin program in the current native World, preserving every outer field. -/
theorem sample (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (draw : ProbComp Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.sample draw)).run before =
      Prod.map id (embed before) <$>
        (simulateQ RegistrationWorldCoinCompiler.coin draw).run before.server.world.world.1 := by
  rw [sample_effects, RegistrationBeaconReferenceNativeEffects.beacon_program,
    RegistrationBeaconReferenceNativeEffects.program, RegistrationWorldCoinCompiler.env_program]

/-- Actual source scalar sampling keeps the native pool, roster, receipts and exact 32-query uniform/coin charges. -/
theorem scalar (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before =
      (fun value => (value, embed before (RegistrationNativeEnvSampling.advance 32 before.server.world.world.1))) <$>
        PqxdhJointGapDh.sampleScalar := by
  rw [sample, RegistrationNativeEnvSampling.scalar, Functor.map_map]
  rfl

/-- The independent private challenge replaces only the scalar used by the native continuation; its dummy draw stays in the actual source state. -/
theorem scalar_eager (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (next : PqxdhJointGapDh.ScalarBytes → RegistrationNativeExperiment.State n KemSK source → ProbComp Value) :
    (do let drawn ← (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before
        next drawn.1 drawn.2) =ᵈ
      (do let selected ← PqxdhJointGapDh.sampleScalar
          let dummy ← (RegistrationNativeExperiment.beacon setup checks representation created
            (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before
          next selected dummy.2) := by
  simp only [scalar, bind_map_left]
  apply _root_.EvalDistEq.bind_right
  intro selected
  exact (OracleComp.EvalDistEq.bind_const PqxdhJointGapDh.sampleScalar
    (next selected (embed before (RegistrationNativeEnvSampling.advance 32 before.server.world.world.1)))).symm

end BeaconcryptCore.Computational.RegistrationNativeScalarSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarSource.sample_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarSource.sample_effects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarSource.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarSource.sample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarSource.scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarSource.scalar
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarSource.scalar_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarSource.scalar_eager
