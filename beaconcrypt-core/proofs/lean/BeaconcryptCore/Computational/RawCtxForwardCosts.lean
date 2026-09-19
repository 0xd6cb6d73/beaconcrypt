import BeaconcryptCore.Computational.RawCtxForwardCoverage

/-!
Erasing forward source descriptors preserves every exact primitive-query class. Static coverage additionally identifies the number of descriptor-carrying callbacks with the original private-query count. The source KDF ledger can therefore bound how many descriptors are constructed. Copying or retaining each finite saved structure remains explicit local work; these statements bound callback counts rather than asserting constant-time state copying.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardCosts
open RawCtxForwardAnnotation RawCtxForwardCoverage
variable {Tag ι Result : Type} {base : OracleSpec ι}

/-- Descriptor erasure preserves each actual query class for the complete syntax and every possible adaptive reply. -/
theorem erase_class
    (predicate : base.Domain → Prop) [DecidablePred predicate]
    (client : OracleComp (Spec Tag base) Result) (budget : Nat) :
    (simulateQ erase client).IsQueryBoundP predicate budget ↔
      client.IsQueryBoundP (fun query => predicate query.2) budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, erase, isQueryBoundP_query_bind_iff, ih]

/-- Every carried descriptor is charged to an original private callback, with no hidden allowance for annotation construction. -/
theorem descriptor_class
    (privateQuery : base.Domain → Bool) (client : OracleComp (Spec Tag base) Result)
    (covered : Covered privateQuery client) (budget : Nat) :
    client.IsQueryBoundP (fun query => query.1.isSome = true) budget ↔
      (simulateQ erase client).IsQueryBoundP (fun query => privateQuery query = true) budget := by
  rw [erase_class]
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff, isQueryBoundP_query_bind_iff]
    have tagged : query.1.isSome = privateQuery query.2 := covered.1
    simp only [tagged]
    exact and_congr Iff.rfl (forall_congr' fun reply => ih reply (covered.2 reply) _)

end BeaconcryptCore.Computational.RawCtxForwardCosts

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardCosts.erase_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardCosts.erase_class
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardCosts.descriptor_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardCosts.descriptor_class
