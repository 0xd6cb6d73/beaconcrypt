import BeaconcryptCore.Computational.RawCtxForwardAnnotation

/-!
Forward coverage requires a carried descriptor at every selected private query and nowhere else. This is checked over the actual annotated syntax under every possible reply, so erasure and descriptor soundness cannot be satisfied vacuously by omitting all annotations. Concrete source compilers supply the coverage proof used by the state-dependent sampler.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardCoverage
open RawCtxForwardAnnotation

noncomputable def Covered {Tag ι Result : Type} {base : OracleSpec ι}
    (selected : base.Domain → Bool) (client : OracleComp (Spec Tag base) Result) : Prop :=
  OracleComp.recOn client (fun _ => True)
    (fun query _next recurse => query.1.isSome = selected query.2 ∧ ∀ reply, recurse reply)

/-- A completed program has no selected request requiring annotation. -/
theorem covered_pure {Tag ι Result : Type} {base : OracleSpec ι}
    (selected : base.Domain → Bool) (result : Result) : Covered selected (pure result : OracleComp (Spec Tag base) Result) := trivial

/-- Every selected request carries a descriptor before its primitive call, and every reply continuation remains covered. -/
theorem covered_query {Tag ι Result : Type} {base : OracleSpec ι}
    (selected : base.Domain → Bool) (tag : Option Tag) (query : base.Domain)
    (next : base.Range query → OracleComp (Spec Tag base) Result) :
    Covered selected (((Spec Tag base).query (tag, query) : OracleComp (Spec Tag base) _) >>= next) ↔
      tag.isSome = selected query ∧ ∀ reply, Covered selected (next reply) := Iff.rfl

end BeaconcryptCore.Computational.RawCtxForwardCoverage

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardCoverage.covered_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardCoverage.covered_pure
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardCoverage.covered_query' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardCoverage.covered_query
