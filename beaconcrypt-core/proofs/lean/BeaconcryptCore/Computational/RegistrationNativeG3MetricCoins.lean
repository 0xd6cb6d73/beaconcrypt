-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant

/-! The selective material service has a proved zero-capability footprint. Its remaining actual Env coin AST therefore evaluates as a local probability computation on an unchanged semantic World after the named accounting projection. The constant-initial-World fallback is outside this verified footprint and never sees the actual hidden World. This supplies the independent key-service sampler required by the concrete material frontend source equations. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3MetricWorld (mask handler)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def program (work : ProbComp Value) : OracleComp (WorldSpec n) Value :=
  simulateQ effectLift (simulateQ RegistrationNativeHiddenService.coins work)

private theorem actual_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : ProbComp Value) :
    simulateQ (CborRecordWorldSimulation.guarded setup codec route) (program (n := n) work) =
      simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin work) := by
  simp only [program, ← QueryImpl.simulateQ_compose]
  have same : CborRecordWorldSimulation.guarded setup codec route ∘ₛ (effectLift ∘ₛ
      RegistrationNativeHiddenService.coins) =
      (PqxdhRecordLiftWorld.effects ∘ₛ RegistrationWorldCoinCompiler.envCoin :
        QueryImpl unifSpec (StateT (State n) ProbComp)) := by
    funext coin
    simp only [QueryImpl.compose, RegistrationNativeHiddenService.coins, effectLift,
      RegistrationWorldCoinCompiler.envCoin, simulateQ_spec_query]
    rfl
  rw [same]

/-- The actual compiled Env coin program becomes its independent literal sampler while every semantic World field remains unchanged. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : ProbComp Value) (before : State n) :
    (simulateQ (handler setup codec route) (program (n := n) work)).run (mask before) =
      (fun value => (value, mask before)) <$> work := by
  rw [← RegistrationNativeG3MetricWorld.program_source, actual_program]
  exact RegistrationNativeG3MetricWorld.sampled_source work before

noncomputable def localCoins : QueryImpl (EnvEffects n) ProbComp
  | .inl coin => unifSpec.query coin
  | .inr capability => Prod.fst <$> (PqxdhRecordLiftWorld.effects (.inr capability)).run PqxdhRecordLiftWorld.initial

/-- Every capability-free actual Env program factors through a local sampler, retaining the complete semantic World and all client output. -/
theorem environment_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (EnvEffects n) Value)
    (free : work.IsQueryBoundP RegistrationNativeHiddenServiceBounds.IsCapability 0) (before : State n) :
    (simulateQ (handler setup codec route) (simulateQ effectLift work)).run (mask before) =
      (fun value => (value, mask before)) <$> simulateQ localCoins work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      cases query with
      | inl coin =>
          simp only [simulateQ_bind, simulateQ_spec_query, effectLift, StateT.run_bind, localCoins, map_bind]
          have step := program_source setup codec route (unifSpec.query coin : ProbComp (unifSpec.Range coin)) before
          simp only [program, RegistrationNativeHiddenService.coins, simulateQ_spec_query, effectLift] at step
          rw [step, bind_map_left]
          apply bind_congr
          intro reply
          have tail := ih reply (by simpa only [RegistrationNativeHiddenServiceBounds.IsCapability, ite_false] using free.2 reply) before
          exact tail
      | inr capability =>
          have impossible := free.1
          simp only [RegistrationNativeHiddenServiceBounds.IsCapability, not_true_eq_false, Nat.not_lt_zero, or_self] at impossible

/-- The same independent sampler law applies from an arbitrary counted input World after the named output projection. -/
theorem environment_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (EnvEffects n) Value)
    (free : work.IsQueryBoundP RegistrationNativeHiddenServiceBounds.IsCapability 0) (before : State n) :
    Prod.map id mask <$> (simulateQ (handler setup codec route) (simulateQ effectLift work)).run before =
      (fun value => (value, mask before)) <$> simulateQ localCoins work := by
  rw [RegistrationNativeG3MetricWorld.handler_program_mask]
  exact environment_source setup codec route work free before

end BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins.environment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins.environment_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins.environment_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins.environment_project
