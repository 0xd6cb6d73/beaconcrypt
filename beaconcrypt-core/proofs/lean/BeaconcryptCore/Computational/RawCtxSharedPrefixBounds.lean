import BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix
import BeaconcryptCore.Computational.PqxdhInitialNativeBudgets

/-!
Query accounting for the actual shared-ROM prefix charges all attempted source callbacks, including cached hashes, failed openings and callbacks before the selected miss. The scanner adds no oracle operation at its selected cut. Local probabilistic work and private full-output sampling remain explicit.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSharedPrefixBounds
open CtxRomAuth AdaptiveCtxSharedHash RawCtxForwardAnnotation RawCtxForwardCoverage RawCtxForwardScan
variable {ι Local Tag Result : Type} {base : OracleSpec ι}

/-- Each attempted callback retains its full cost; stopping at the selected request adds no query. The bound quantifies over every typed reply and reached local state. -/
theorem scan_bound
    (privateQuery : base.Domain → Bool) (selected : base.Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec)))
    (predicate : HashSpec.Domain → Prop) [DecidablePred predicate] (perCall : Nat)
    (bills : ∀ query state, ((impl query).run state).IsQueryBoundP predicate perCall)
    (client : OracleComp (Spec Tag base) Result) (covered : Covered privateQuery client)
    (q : Nat) (bounded : client.IsTotalQueryBound q) (state : Local) :
    (RawCtxSharedPrefixScan.scan privateQuery selected selection impl client covered state).IsQueryBoundP predicate (q * perCall) := by
  induction client using OracleComp.inductionOn generalizing q state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    change (if chosen : selected query.2 state = true then _ else _ : OracleComp HashSpec (Cut Tag Result Local)).IsQueryBoundP predicate _
    split
    · trivial
    · change (((impl query.2).run state) >>= fun result =>
        RawCtxSharedPrefixScan.scan privateQuery selected selection impl (next result.1) (covered.2 result.1) result.2).IsQueryBoundP predicate _
      have rest := fun result : base.Range query.2 × Local => ih result.1 (covered.2 result.1) (q - 1) (bounded.2 result.1) result.2
      have cost : perCall + (q - 1) * perCall = q * perCall := by
        calc
          _ = (1 + (q - 1)) * perCall := by simp [Nat.add_mul]
          _ = q * perCall := by rw [show 1 + (q - 1) = q by omega]
      exact cost ▸ isQueryBoundP_bind (bills query.2 state) (fun result _ => rest result)

/-- Erasing the carried descriptor retains exactly the original callback count under every typed reply. -/
theorem annotation_total (client : OracleComp (Spec Tag base) Result) (q : Nat) :
    (simulateQ erase client).IsTotalQueryBound q ↔ client.IsTotalQueryBound q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => simp only [simulateQ_pure]; rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, erase, isTotalQueryBound_query_bind_iff, ih]

end BeaconcryptCore.Computational.RawCtxSharedPrefixBounds


/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPrefixBounds.scan_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrefixBounds.scan_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSharedPrefixBounds.annotation_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSharedPrefixBounds.annotation_total
