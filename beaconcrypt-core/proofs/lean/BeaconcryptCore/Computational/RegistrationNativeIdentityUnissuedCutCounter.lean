-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
/-! The fixed public acceptance cut reaches its literal original counter, under every stateful private source interpreter and every optional reply. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityUnissuedAcceptCut (Cut stop)
variable {A S : Type}

def cost : TypedSpec.Domain → Nat
  | .inr (.accept _) => 1
  | _ => 0

noncomputable def counted (implementation : QueryImpl TypedSpec (StateT S ProbComp)) :
    QueryImpl TypedSpec (StateT (S × Nat) ProbComp) := fun query before =>
  (fun result => (result.1,(result.2,before.2+cost query))) <$> (implementation query).run before.1

def Status (accept : Nat) : Cut A → Nat → Prop
  | .returned _, cursor => cursor ≤ accept
  | .accept _ _, cursor => cursor = accept

private theorem stop_pure (accept cursor : Nat) (value : A) : stop accept (pure value) cursor = pure (.returned value) := rfl
private theorem stop_step (accept cursor : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) :
    stop accept (TypedSpec.query query >>= next) cursor =
      (match query with
      | .inr (.accept value) =>
          if cursor = accept then pure (.accept value next)
          else do let reply ← TypedSpec.query (.inr (.accept value)); stop accept (next reply) (cursor+1)
      | query => do let reply ← TypedSpec.query query; stop accept (next reply) cursor) := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

/-- A returned accept cut has exactly the original counted ordinal; a fully returned client has not passed it. -/
theorem progress (accept cursor : Nat) (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (work : OracleComp TypedSpec A) (before : S) (within : cursor ≤ accept)
    (result : Cut A × (S × Nat))
    (supported : result ∈ support ((simulateQ (counted implementation) (stop accept work cursor)).run (before,cursor))) :
    Status accept result.1 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before cursor result with
  | pure value =>
      simp only [stop_pure,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact within
  | query_bind query next ih =>
      have forward (bump : Nat) (charged : cost query = bump) (room : cursor+bump ≤ accept)
          (reached : result ∈ support ((simulateQ (counted implementation)
            (TypedSpec.query query >>= fun reply => stop accept (next reply) (cursor+bump))).run (before,cursor))) :
          Status accept result.1 result.2.2 := by
        rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
        obtain ⟨middle,called,continued⟩ := reached
        simp only [counted,StateT.run,support_map] at called
        obtain ⟨actual,_called,rfl⟩ := called
        exact ih actual.1 (cursor+bump) actual.2 room result (by simpa only [charged] using continued)
      rw [stop_step] at supported
      cases query with
      | inl coin => exact forward 0 rfl (by omega) supported
      | inr command =>
          cases command
          case accept value =>
            by_cases chosen : cursor = accept
            · simp only [chosen,ite_true,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
              cases supported
              rfl
            · simp only [chosen,ite_false] at supported
              exact forward 1 rfl (by omega) supported
          all_goals exact forward 0 rfl (by omega) supported

/-- Forgetting the counter preserves the complete original private source execution and its exact poststate. -/
theorem erase (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S × Nat) :
    Prod.map id Prod.fst <$> (simulateQ (counted implementation) work).run before =
      (simulateQ implementation work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [counted,StateT.run,Functor.map_map,Prod.map,id_eq]
  exact id_map _

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter.progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter.progress

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedCutCounter.erase
