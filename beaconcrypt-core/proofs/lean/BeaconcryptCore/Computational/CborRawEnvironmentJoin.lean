-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawEnvironment
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv

/-! The public raw registration transformer preserves the concrete environment/native split. The fixed-parameter ideal instance uses the existing proved ideal split, including its shared random-oracle effects and private state. This is a registration step join; the complete record-world join additionally uses the native cursor/refusal coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawEnvironmentJoin
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment EnvQuery EnvSpec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good Splits)
open PqxdhDeploymentBackend (RegImpl XState)
open CborRawPublicState (Public)
open LazyOracleDiscard (LawEq)
variable {n : Nat} {KemSK Bk E : Type}

/-- Public adaptation is outside the real shared-world effect interpreter. -/
theorem step_effects (env : Environment n E) (query : EnvQuery) (state : Public × E)
    (world : PqxdhRecordLiftWorld.State n) :
    (simulateQ PqxdhRecordLiftWorld.effects ((CborRawEnvironment.step env query).run state)).run world =
      (fun value => ((CborRawEnvironment.reply state.1 query value.1.1,
        (CborRawEnvironment.next state.1 query value.1.1, value.1.2)), value.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          ((env.step (CborRawEnvironment.request state.1 query)).run state.2)).run world := by
  simp only [CborRawEnvironment.step_run, simulateQ_map, StateT.run_map]

/-- The same public state is retained beside the complete existing reassembly. -/
def merge (state : Public × EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n) :
    Public × XState KemSK Bk n :=
  (state.1, PqxdhDeploymentEnvironmentJoin.merge state.2 world)

/-- Any proved concrete environment split transports through the public raw registration adapter without changing its effects, private outcomes or failure replies. -/
theorem step_law (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop)
    (splits : Splits created reg env.step inv)
    (query : EnvQuery) (state : Public × EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : Good created state.2 world) (holds : inv state.2 world) :
    LawEq ((fun value => (value.1.1, merge value.1.2 value.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((CborRawEnvironment.step env query).run state)).run world)
      ((fun value => (CborRawEnvironment.reply state.1 query value.1,
          (CborRawEnvironment.next state.1 query value.1, value.2))) <$>
        (reg (CborRawEnvironment.request state.1 query)).run
          (PqxdhDeploymentEnvironmentJoin.merge state.2 world)) := by
  have delegated := (splits (CborRawEnvironment.request state.1 query) state.2 world good holds).1
  have mapped := delegated.map (fun value => (CborRawEnvironment.reply state.1 query value.1,
    (CborRawEnvironment.next state.1 query value.1, value.2)))
  rw [step_effects, Functor.map_map]
  simpa only [Functor.map_map, merge] using mapped

/-- The adapter keeps the existing admissibility and private environment invariant on every full supported outcome. -/
theorem step_keeps (env : Environment n (EnvState KemSK Bk)) (reg : RegImpl KemSK Bk n)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop)
    (splits : Splits created reg env.step inv)
    (query : EnvQuery) (state : Public × EnvState KemSK Bk) (world : PqxdhRecordLiftWorld.State n)
    (good : Good created state.2 world) (holds : inv state.2 world)
    (value : (EnvSpec.Range query × (Public × EnvState KemSK Bk)) × PqxdhRecordLiftWorld.State n)
    (supported : value ∈ support
      ((simulateQ PqxdhRecordLiftWorld.effects ((CborRawEnvironment.step env query).run state)).run world)) :
    Good created value.1.2.2 value.2 ∧ inv value.1.2.2 value.2 := by
  rw [step_effects, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact (splits (CborRawEnvironment.request state.1 query) state.2 world good holds).2 inner reached

section Ideal
open PqxdhDeploymentIdealParams (Target Params)
variable {ι Reader Response A : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count)

/-- Concrete ideal registration instance: the split is proved by the existing actual ideal environment, rather than assumed by a raw-game theorem. -/
theorem ideal_step_law (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : EnvQuery)
    (state : Public × EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (world : PqxdhRecordLiftWorld.State 2)
    (good : Good created state.2 world) (holds : PqxdhDeploymentIdealEnv.IdealInv target state.2 world) :
    LawEq ((fun value => (value.1.1, merge value.1.2 value.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects ((CborRawEnvironment.step
          (PqxdhDeploymentIdealEnv.envG setup (CborRawCompile.sourceCodec wire parse) checks target parameters
            ensureInit identityIndex runtime) query).run state)).run world)
      ((fun value => (CborRawEnvironment.reply state.1 query value.1,
          (CborRawEnvironment.next state.1 query value.1, value.2))) <$>
        (PqxdhDeploymentIdealDefer.idealSplit setup (CborRawCompile.sourceCodec wire parse)
          (CborRawCompile.route parse) checks target parameters created
          (CborRawEnvironment.request state.1 query)).run
          (PqxdhDeploymentEnvironmentJoin.merge state.2 world)) :=
  step_law _ _ created _
    (PqxdhDeploymentIdealEnv.ideal_splits setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      checks target parameters created) query state world good holds

end Ideal
end BeaconcryptCore.Computational.CborRawEnvironmentJoin

/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentJoin.step_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentJoin.step_effects
/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentJoin.step_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentJoin.step_law
/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentJoin.step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentJoin.step_keeps
/-- info: 'BeaconcryptCore.Computational.CborRawEnvironmentJoin.ideal_step_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawEnvironmentJoin.ideal_step_law
