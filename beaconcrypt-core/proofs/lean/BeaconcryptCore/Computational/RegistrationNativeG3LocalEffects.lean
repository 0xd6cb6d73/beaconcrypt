-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld

/-! Actual materialized common stages use Env coins and administration, whose literal World queries have no record-size refusal. Their exact source equations therefore lift through the actual guarded handler without a reached cursor-validity premise. RecordSpec remains outside this equation and keeps its actual early guard. The only normalization below is the already proved accounting projection on both input and output. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects
open PqxdhRecordLiftInterface (EnvEffects effectLift)
open PqxdhRecordLiftWorld (State)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3MetricWorld (mask handler)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

/-- Every concrete Env callback is the literal actual World effect under cursor admission; no record guard is bypassed. -/
theorem guarded_effect (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (EnvEffects n).Domain) :
    simulateQ (CborRecordWorldSimulation.guarded setup codec route) (effectLift query) =
      PqxdhRecordLiftWorld.effects query := by
  simp only [effectLift, simulateQ_spec_query]
  funext before
  rfl

/-- The actual normalized guarded Env callback is exactly the same actual administration effect with its explicit accounting view. -/
theorem normalized_effect (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (EnvEffects n).Domain) (before : State n) :
    (simulateQ (handler setup codec route) (effectLift query)).run before =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.effects query).run (mask before) := by
  simp only [effectLift, simulateQ_spec_query]
  rfl

/-- Exact finite material/common Env source equations may be normalized at both ends through the actual guarded World, including every failure and installed kernel. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (EnvEffects n) Value) (before : State n) :
    Prod.map id mask <$> (simulateQ PqxdhRecordLiftWorld.effects work).run before =
      (simulateQ (handler setup codec route) (simulateQ effectLift work)).run (mask before) := by
  have program : simulateQ (CborRecordWorldSimulation.guarded setup codec route) (simulateQ effectLift work) =
      simulateQ PqxdhRecordLiftWorld.effects work := by
    rw [← QueryImpl.simulateQ_compose]
    have queries : CborRecordWorldSimulation.guarded setup codec route ∘ₛ effectLift =
        (PqxdhRecordLiftWorld.effects : QueryImpl (EnvEffects n) (StateT (State n) ProbComp)) := by
      funext query
      exact guarded_effect setup codec route query
    rw [queries]
  rw [← program]
  exact RegistrationNativeG3MetricWorld.program_source setup codec route (simulateQ effectLift work) before

end BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects.guarded_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects.guarded_effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects.normalized_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects.normalized_effect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalEffects.program_source
