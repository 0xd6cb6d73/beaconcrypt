import BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix
import VCVio.EvalDist.Monad.Basic

/-!
An adaptive stateful source scan accumulates callback failure risks in their actual counted order. Selected callbacks are retained before execution and consume neither risk nor query budget. Every unselected callback keeps its original reply and complete state. The bound uses an all-reply source query cap and an explicit supported-state invariant; it does not assume a final collision probability or that a cut is reached. A protocol consumer must discharge the local invariant and one-callback risk bounds for its actual interpreter.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxStatefulScanRisk
open RawCtxStatefulPendingPrefix
variable {ι Result State : Type} {spec : OracleSpec ι}

/-- The failure probability of the actual stopped scan is at most the sum of the risks of its bounded counted callbacks. Zero-cost callbacks and a selected unexecuted callback add no risk. -/
theorem scan_risk
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (counted : ι → Prop) [DecidablePred counted]
    (Clean : State → Prop) (Valid : Nat → State → Prop) (risk : Nat → ℝ≥0∞)
    (preserve : ∀ k query state, selected query state = false → Valid k state → Clean state →
      ∀ result ∈ support ((impl query).run state),
        Valid (k + if counted query then 1 else 0) result.2)
    (step : ∀ k query state, selected query state = false → Valid k state → Clean state →
      Pr{let result ← (impl query).run state}[¬Clean result.2] ≤
        if counted query then risk k else 0)
    (client : OracleComp spec Result) (m k : Nat)
    (bound : client.IsQueryBoundP counted m) (state : State)
    (valid : Valid k state) (clean : Clean state) :
    Pr{let result ← scan selected impl client state}[¬Clean result.2] ≤
      ∑ j ∈ Finset.range m, risk (k + j) := by
  classical
  induction client using OracleComp.inductionOn generalizing m k state with
  | pure result =>
      rw [scan_pure, prEvent_pure]
      simp only [clean, not_true_eq_false, ite_false, zero_le]
  | query_bind query next ih =>
      cases chosen : selected query state with
      | true =>
          rw [scan_cut selected impl query next state chosen, prEvent_pure]
          simp only [clean, not_true_eq_false, ite_false, zero_le]
      | false =>
          rw [scan_other selected impl query next state chosen]
          rw [isQueryBoundP_query_bind_iff] at bound
          by_cases charged : counted query
          · have positive : 0 < m := bound.1.resolve_left (not_not.mpr charged)
            have continuation : ∀ result ∈ support ((impl query).run state), Clean result.2 →
                Pr{let final ← scan selected impl (next result.1) result.2}[¬Clean final.2] ≤
                  ∑ j ∈ Finset.range (m - 1), risk (k + 1 + j) := by
              intro result supported stillClean
              apply ih result.1 (m - 1) (k + 1)
              · simpa only [charged, ite_true] using bound.2 result.1
              · simpa only [charged, ite_true] using preserve k query state chosen valid clean result supported
              · exact stillClean
            have combined := (prEvent_bind_le_prEvent_add_of_support ((impl query).run state)
              (fun result => scan selected impl (next result.1) result.2)
              (fun result => ¬Clean result.2) (fun final => ¬Clean final.2)
              (ε := ∑ j ∈ Finset.range (m - 1), risk (k + 1 + j))
              fun result supported stillClean => continuation result supported (not_not.mp stillClean)).trans
              (add_le_add (by simpa only [charged, ite_true] using step k query state chosen valid clean) le_rfl)
            refine combined.trans_eq ?_
            conv_rhs => rw [show m = (m - 1) + 1 by omega]
            rw [Finset.sum_range_succ']
            simp only [Nat.add_zero]
            rw [add_comm]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            omega
          · have continuation : ∀ result ∈ support ((impl query).run state), Clean result.2 →
                Pr{let final ← scan selected impl (next result.1) result.2}[¬Clean final.2] ≤
                  ∑ j ∈ Finset.range m, risk (k + j) := by
              intro result supported stillClean
              apply ih result.1 m k
              · simpa only [charged, ite_false, Nat.sub_zero] using bound.2 result.1
              · simpa only [charged, ite_false, Nat.add_zero] using preserve k query state chosen valid clean result supported
              · exact stillClean
            have combined := (prEvent_bind_le_prEvent_add_of_support ((impl query).run state)
              (fun result => scan selected impl (next result.1) result.2)
              (fun result => ¬Clean result.2) (fun final => ¬Clean final.2)
              (ε := ∑ j ∈ Finset.range m, risk (k + j))
              fun result supported stillClean => continuation result supported (not_not.mp stillClean)).trans
              (add_le_add (by simpa only [charged, ite_false] using step k query state chosen valid clean) le_rfl)
            simpa only [zero_add] using combined

end BeaconcryptCore.Computational.RawCtxStatefulScanRisk

/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulScanRisk.scan_risk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulScanRisk.scan_risk
