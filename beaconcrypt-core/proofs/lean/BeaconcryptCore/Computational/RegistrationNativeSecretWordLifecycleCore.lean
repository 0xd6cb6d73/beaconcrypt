-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend

/-! A ghost query counter records actual native callbacks without changing their replies or program effects. Finite callback costs and the frontend's actual decreasing lifecycle credit lift to every adaptive typed program. Concrete lifecycle modules discharge those local obligations from the native controllers. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore
variable {ι κ Value Front : Type} {spec : OracleSpec ι} {target : OracleSpec κ}

def monitor (counted : target.Domain → Prop) [DecidablePred counted] :
    QueryImpl target (StateT Nat (OracleComp target)) := fun query before =>
  (fun reply => (reply, before + if counted query then 1 else 0)) <$>
    (target.query query : OracleComp target _)

private theorem monitor_run (counted : target.Domain → Prop) [DecidablePred counted]
    (query : target.Domain) (before : Nat) :
    (monitor counted query).run before =
      (fun reply => (reply, before + if counted query then 1 else 0)) <$>
        (target.query query : OracleComp target _) := rfl

/-- Counter instrumentation preserves the literal complete original computation after dropping only its count. -/
theorem erased (counted : target.Domain → Prop) [DecidablePred counted]
    (work : OracleComp target Value) (before : Nat) :
    Prod.fst <$> (simulateQ (monitor counted) work).run before = work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, monitor_run,
        bind_map_left, map_bind, ih]

/-- An actual structural callback cap bounds its observed counter increment, including every failed reply branch. -/
theorem count_bound (counted : target.Domain → Prop) [DecidablePred counted]
    (work : OracleComp target Value) (cap : Nat) (bounded : work.IsQueryBoundP counted cap)
    (before : Nat) (result : Value × Nat)
    (supported : result ∈ support ((simulateQ (monitor counted) work).run before)) : result.2 ≤ before + cap := by
  induction work using OracleComp.inductionOn generalizing cap before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      omega
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, monitor_run,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      have later := ih reply _ (bounded.2 reply) _ continued
      by_cases charged : counted query
      · have positive : 0 < cap := bounded.1.resolve_left (not_not.mpr charged)
        simp only [ite_eq_left charged] at later
        omega
      · simpa only [ite_eq_right charged, Nat.add_zero] using later

/-- Every instrumented supported result also occurs in the literal original callback program. -/
theorem source_support (counted : target.Domain → Prop) [DecidablePred counted]
    (work : OracleComp target Value) (before : Nat) (result : Value × Nat)
    (supported : result ∈ support ((simulateQ (monitor counted) work).run before)) : result.1 ∈ support work := by
  rw [← erased counted work before, support_map]
  exact ⟨result, supported, rfl⟩

/-- Actual per-query lifecycle spending and returned-state credit compose through every adaptive typed client. -/
theorem program_credit (counted : target.Domain → Prop) [DecidablePred counted]
    (implementation : QueryImpl spec (StateT Front (OracleComp target)))
    (credit : Front → Nat) (cost : spec.Domain → Front → Nat)
    (localBound : ∀ query before, ((implementation query).run before).IsQueryBoundP counted (cost query before))
    (localCredit : ∀ query before result, result ∈ support ((implementation query).run before) →
      credit result.2 + cost query before ≤ credit before)
    (work : OracleComp spec Value) (before : Front) (initialCount : Nat)
    (result : (Value × Front) × Nat)
    (supported : result ∈ support ((simulateQ (monitor counted)
      ((simulateQ implementation work).run before)).run initialCount)) :
    result.2 + credit result.1.2 ≤ initialCount + credit before := by
  induction work using OracleComp.inductionOn generalizing before initialCount with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact Nat.le_refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, stepped, continued⟩ := supported
      have original := source_support counted ((implementation query).run before) initialCount middle stepped
      have spent := count_bound counted ((implementation query).run before) (cost query before)
        (localBound query before) initialCount middle stepped
      have remaining := localCredit query before middle.1 original
      have tail := ih middle.1.1 middle.1.2 middle.2 continued
      omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.erased' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.erased
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.count_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.count_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.source_support' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.source_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.program_credit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleCore.program_credit
