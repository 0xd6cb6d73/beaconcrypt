-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldViewRecords
import BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform
import BeaconcryptCore.Computational.RegistrationNativeHiddenService

/-! The selective G3 source comparison erases only the separately billed native-call map, Env coin counter and primitive uniform counter. The actual seed cache and use markers, shared CTX cache, all other counters, complete record kernels and produced frames remain literal. Every actual guarded World callback has this bilateral non-read law, so normalizing between callbacks is derived from the actual World semantics. Pure key-service sampling can then be moved to independent private service state without a free same-World premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def mask (before : State n) : State n :=
  RegistrationNativeWorldView.project (RegistrationNativeKemWorldUniform.mask before)

/-- The two existing analysis projections commute and retain every seed, use, record and shared-cache coordinate. -/
theorem mask_commute (before : State n) :
    RegistrationNativeKemWorldUniform.mask (RegistrationNativeWorldView.project before) = mask before := rfl

/-- Repeated normalization erases exactly the same three separately billed analysis fields. -/
theorem mask_idempotent (before : State n) : mask (mask before) = mask before := by
  simp only [mask, RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, RegistrationNativeKemWorldUniform.mask, Function.update_idem]

/-- Actual cursor admission and every optional World reply are independent of the stated accounting fields on both input and output. -/
theorem guarded_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run (mask before) := by
  have uniform := congrArg (fun distribution => Prod.map id RegistrationNativeWorldView.project <$> distribution)
    (RegistrationNativeKemWorldRecordUniform.guarded_input setup codec route query before)
  have counters := congrArg (fun distribution => Prod.map id RegistrationNativeKemWorldUniform.mask <$> distribution)
    (RegistrationNativeWorldViewRecords.guarded_input setup codec route query (RegistrationNativeKemWorldUniform.mask before))
  simp only [Functor.map_map, Prod.map_def, id_eq, mask_commute] at uniform counters
  exact uniform.trans counters

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) := fun query before =>
  Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run (mask before)

/-- The normalized concrete callback itself commutes with accounting erasure, including a pure refusal. -/
theorem handler_mask (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id mask <$> (handler setup codec route query).run before =
      (handler setup codec route query).run (mask before) := by
  simp only [handler, StateT.run, Functor.map_map, Prod.map_def, id_eq, mask_idempotent]

/-- Arbitrary actual World code can be normalized at both ends without changing any semantic field or adaptive reply. -/
theorem handler_program_mask (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.map id mask <$> (simulateQ (handler setup codec route) work).run before =
      (simulateQ (handler setup codec route) work).run (mask before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ mask (handler_mask setup codec route) work before

/-- Normalizing the complete actual World run equals normalizing its concrete callbacks one at a time. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.map id mask <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before =
      (simulateQ (handler setup codec route) work).run (mask before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ mask _ work before
  intro query state
  simpa only [handler, StateT.run, mask_idempotent] using guarded_input setup codec route query state

/-- The actual full private sampler, after only accounting erasure, is the same independent draw on the unchanged semantic World. -/
theorem sampled_source (work : ProbComp Value) (before : State n) :
    Prod.map id mask <$>
      (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin work)).run before =
      (fun value => (value, mask before)) <$> work := by
  have counters := congrArg (fun distribution => Prod.map id RegistrationNativeKemWorldUniform.mask <$> distribution)
    (RegistrationNativeWorldView.coins work before)
  rw [RegistrationNativeKemWorldUniform.sampled_mask] at counters
  simpa only [Functor.map_map, Function.comp_def, Prod.map_def, id_eq, mask_commute] using counters

end BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.mask_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.mask_commute
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.mask_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.mask_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.guarded_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.guarded_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.handler_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.handler_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.handler_program_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.handler_program_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.sampled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MetricWorld.sampled_source
