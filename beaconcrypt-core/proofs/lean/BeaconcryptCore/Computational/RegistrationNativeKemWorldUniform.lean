-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-! Opening an external KEM callback hides its internal uniform-draw ledger from the CCA client. This projection removes only that analysis counter: native/effect counters, cache, kernels, owners, seeds, raw counters, produced frames and all other coordinates remain. Actual sampler caps are proved separately on the original counted execution. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform
open PqxdhRecordLiftWorld (State sampled countCoin)
variable {n : Nat} {Value : Type}

def mask (state : State n) : State n :=
  { state with primitive := ({ state.primitive.1 with uniform := 0 }, state.primitive.2) }

/-- Only the private uniform accounting coordinate is forgotten. -/
theorem mask_idempotent (state : State n) : mask (mask state) = mask state := rfl

/-- The actual counted sampler, after the stated projection, has its original draw and retains every operational World coordinate. -/
theorem sampled_mask (draw : ProbComp Value) (state : State n) :
    Prod.map id mask <$> (sampled draw).run state =
      (fun value => (value, mask state)) <$> draw := by
  have forgot := congrArg (fun work => (fun value => (value, mask state)) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget draw state.primitive.1.uniform)
  simpa only [sampled, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq,
    mask, Function.comp_def] using forgot

/-- Sampling from states differing only in the hidden uniform ledger has identical complete projected outcomes. -/
theorem sampled_input (draw : ProbComp Value) (state : State n) :
    Prod.map id mask <$> (sampled draw).run state =
      Prod.map id mask <$> (sampled draw).run (mask state) := by
  rw [sampled_mask, sampled_mask, mask_idempotent]

/-- An actual primitive program's total query cap bounds its retained uniform counter, before any projection. -/
private theorem counted_query_bound (draw : ProbComp Value) (cap : Nat)
    (bounded : draw.IsQueryBoundP (fun _ => True) cap)
    (count : Nat) (result : Value × Nat)
    (supported : result ∈ support ((simulateQ countCoin draw).run count)) : result.2 ≤ count + cap := by
  induction draw using OracleComp.inductionOn generalizing cap count result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      omega
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff] at bounded
      have positive : 0 < cap := by simpa using bounded.1
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind] at supported
      simp only [countCoin, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _, tail⟩ := supported
      have bound := ih reply (cap - 1) (by simpa only [ite_true] using bounded.2 reply) (count + 1) result tail
      omega

/-- An actual primitive program's total query cap bounds its retained uniform counter, before any projection. -/
theorem counted_bound (draw : ProbComp Value) (cap : Nat) (bounded : draw.IsTotalQueryBound cap)
    (count : Nat) (result : Value × Nat)
    (supported : result ∈ support ((simulateQ countCoin draw).run count)) : result.2 ≤ count + cap :=
  counted_query_bound draw cap ((isQueryBoundP_true_iff draw cap).mpr bounded) count result supported

/-- The original full sampler retains the same actual primitive bill even though its operational projection omits the uniform count. -/
theorem sampled_bound (draw : ProbComp Value) (cap : Nat) (bounded : draw.IsTotalQueryBound cap)
    (state : State n) (result : Value × State n)
    (supported : result ∈ support ((sampled draw).run state)) :
    result.2.primitive.1.uniform ≤ state.primitive.1.uniform + cap := by
  simp only [sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  cases returned
  exact counted_bound draw cap bounded state.primitive.1.uniform inner reached

end BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.mask_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.mask_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.sampled_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.sampled_mask

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.sampled_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.sampled_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.counted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.counted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.sampled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemWorldUniform.sampled_bound
