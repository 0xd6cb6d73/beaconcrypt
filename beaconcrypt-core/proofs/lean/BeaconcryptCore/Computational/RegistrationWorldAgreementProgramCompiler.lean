-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler

/-! Arbitrary adaptive native agreement programs factor through a World-free environment. The only projected coordinate is the additional EnvEffects coin ledger; its accumulated increment is exactly the actual uniform increment. Every reply and all auxiliary, cache, receipt, request and private record state remain in the equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler
open RegistrationWorldAgreementCompiler (EnvState join mask compiler)
open PqxdhRecordLiftInterface (EffectKind effectKind)
variable {n : Nat} {Auxiliary Value : Type}

abbrev State (n : Nat) (Auxiliary : Type) := EnvState Auxiliary × PqxdhRecordLiftWorld.State n

def project (state : State n Auxiliary) : RegistrationWorldAgreement.State n Auxiliary :=
  mask (join state.1 state.2)

/-- Actual environment execution alongside the separate private record World. -/
noncomputable def handler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (State n Auxiliary) ProbComp) :=
  fun query state => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    RegistrationWorldAgreementCompiler.run source primitive query state.1 state.2

private theorem handler_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : State n Auxiliary) :
    (handler source primitive query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        RegistrationWorldAgreementCompiler.run source primitive query state.1 state.2 := rfl

private theorem native_run (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : RegistrationWorldAgreement.State n Auxiliary) :
    (RegistrationWorldAgreement.agreement source primitive query).run state =
      (fun result => (result.1.1, RegistrationWorldAgreement.State.mk result.1.2
        (state.requests ++ RegistrationWorldAgreement.recorded query) state.recordRequests (result.2, state.world.2))) <$>
        (PqxdhRecordLiftWorld.sampled
          ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary)).run state.world.1 := rfl

/-- Native callbacks never inspect the additional environment coin ledger. -/
theorem native_mask (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id mask <$> (RegistrationWorldAgreement.agreement source primitive query).run state =
      (RegistrationWorldAgreement.agreement source primitive query).run (mask state) := by
  rw [native_run, native_run]
  have same := congrArg (fun work =>
    (fun result => (result.1.1, RegistrationWorldAgreement.State.mk result.1.2
      (state.requests ++ RegistrationWorldAgreement.recorded query) state.recordRequests (result.2, state.world.2))) <$> work)
    (RegistrationWorldCoinCompiler.sampled_erase
      ((RegistrationAgreementShared.auxiliary source primitive query).run state.auxiliary) state.world.1)
  simpa only [mask, Functor.map_map, Prod.map, id_eq] using same

/-- Each environment callback has the actual native reply and full projected state. -/
theorem query_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (state : State n Auxiliary) :
    Prod.map id project <$> (handler source primitive query).run state =
      (RegistrationWorldAgreement.agreement source primitive query).run (project state) := by
  have same := RegistrationWorldAgreementCompiler.query_native source primitive query state.1 state.2
  rw [native_mask] at same
  simpa only [handler, StateT.run, Functor.map_map, Prod.map, id_eq, project] using same

/-- The complete native adaptive program also commutes with the derived counter projection. -/
theorem native_program_mask (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (state : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id mask <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run state =
      (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run (mask state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ mask (native_mask source primitive) work state

/-- Adaptive continuations receive their original native replies; no whole-program simulation premise is required. -/
theorem program_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (state : State n Auxiliary) :
    Prod.map id project <$> (simulateQ (handler source primitive) work).run state =
      Prod.map id mask <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run
        (join state.1 state.2) := by
  rw [native_program_mask]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query_project source primitive) work state

/-- All actual callback coins accumulate the exact native uniform bill, including failed callbacks and adaptive suffixes. -/
theorem program_accounting (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (state : State n Auxiliary)
    (result : Value × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (handler source primitive) work).run state)) :
    result.2.2.primitive.1.effects .coin + state.2.primitive.1.uniform =
      state.2.primitive.1.effects .coin + result.2.2.primitive.1.uniform := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, handler_run,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      have first := RegistrationWorldAgreementCompiler.query_accounting source primitive query state.1 state.2 step reached
      have rest := ih step.1.1 (step.1.2, step.2) result tail
      simp only [] at rest
      omega

/-- A concrete uniform cap for each native primitive callback gives the full adaptive environment coin bill and zero hash or administrative bill. -/
theorem program_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (stepCap : Nat)
    (stepBound : ∀ query auxiliary,
      ((RegistrationAgreementShared.auxiliary source primitive query).run auxiliary).IsTotalQueryBound stepCap)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (calls : Nat)
    (bounded : work.IsTotalQueryBound calls) (state : EnvState Auxiliary) (kind : EffectKind) :
    ((simulateQ (compiler (n := n) source primitive) work).run state).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .coin then calls * stepCap else 0) := by
  induction work using OracleComp.inductionOn generalizing calls state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
      have first := RegistrationWorldAgreementCompiler.query_bound (n := n) source primitive query state stepCap
        (stepBound query state.auxiliary) kind
      have rest := fun (result : RegistrationAgreementExecutor.Spec.Range query × EnvState Auxiliary)
        (_ : result ∈ support ((compiler (n := n) source primitive query).run state)) =>
        ih result.1 (calls - 1) (bounded.2 result.1) result.2
      have combined := isQueryBoundP_bind first rest
      apply combined.mono
      split_ifs with selected
      · have positive := bounded.1
        have count : stepCap + (calls - 1) * stepCap = calls * stepCap := by
          rw [Nat.sub_one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left stepCap positive)]
        omega
      · simp

end BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.native_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.native_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.native_program_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.native_program_mask
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.program_project
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.program_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.program_accounting
/-- info: 'BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler.program_bound
