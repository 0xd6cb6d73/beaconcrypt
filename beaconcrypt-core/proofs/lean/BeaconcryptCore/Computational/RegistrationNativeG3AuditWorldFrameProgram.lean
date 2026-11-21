-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrame

/-! Adaptive common World execution preserves a preassigned private table and every used-role marker. Its bilateral input projection omits only the seed table, retaining the entire chronological role history required by the later up-to-repetition coupling. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3KnownWorldFrameCore (Allowed)
open RegistrationNativeG3AuditWorldFrame (view handler_input keeps)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

/-- Every actual adaptive common continuation preserves all preassigned seeds and every earlier role use. -/
theorem program_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) (result : Value × State n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before)) :
    result.2.seeds = before.seeds ∧ result.2.used = before.used := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, continued⟩ := supported
      have first := keeps setup codec route query allowed before middle stepped
      have rest := ih middle.1 (later middle.1) middle.2 continued
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

private noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) :=
  fun query state => Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run state

private theorem program_normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) :
    Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before =
      (simulateQ (normalized setup codec route) work).run (view before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change _ = (Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (view before)) >>= _
      rw [← handler_input setup codec route query allowed before, bind_map_left]
      exact bind_congr fun result => ih result.1 (later result.1) result.2

/-- Every actual adaptive common World program retains the same complete semantic outcome under the G3 input view. -/
theorem program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) :
    Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before =
      Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run (view before) := by
  have first := program_normalized setup codec route work quiet before
  have second := program_normalized setup codec route work quiet (view before)
  have twice : view (view before) = view before := rfl
  rw [twice] at second
  exact first.trans second.symm


/-- Every previously assigned private table entry survives an arbitrary actual common continuation. -/
theorem program_cached (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) (result : Value × State n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before))
    (slot : PqxdhRecordLiftInterface.Slot n) (seed : PqxdhRecordLiftSeed.Seed)
    (cached : before.seeds.1 slot = some seed) : result.2.seeds.1 slot = some seed := by
  rw [(program_keeps setup codec route work quiet before result supported).1]
  exact cached

end BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram.program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram.program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram.program_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditWorldFrameProgram.program_cached
