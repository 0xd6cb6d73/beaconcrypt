import BeaconcryptCore.Computational.RawCtxPendingMixedPrefix

/-!
Syntactic provenance of complete dependent query continuations in the original finite oracle program. Occurrence permits every typed reply branch and thus needs no primitive success or probability premise. Supported mixed scanning derives occurrence in this same original program. The relation keeps the entire original continuation rather than only the query value.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxQueryOccurrence

noncomputable def Occurs {ι Result : Type} {spec : OracleSpec ι}
    (query : ι) (next : spec.Range query → OracleComp spec Result) (client : OracleComp spec Result) : Prop :=
  OracleComp.recOn client (fun _ => False) (fun head tail recurse =>
    (⟨query, next⟩ : Σ q, spec.Range q → OracleComp spec Result) = ⟨head, tail⟩ ∨ ∃ reply, recurse reply)

/-- A completed original program contains no later query. -/
theorem pure_impossible {ι Result : Type} {spec : OracleSpec ι}
    (query : ι) (next : spec.Range query → OracleComp spec Result) (value : Result) :
    ¬ Occurs query next (pure value) := by
  exact fun occurs => occurs

/-- An occurrence is either the exact current dependent query and continuation or one original typed reply branch. -/
theorem query_cases {ι Result : Type} {spec : OracleSpec ι}
    (query head : ι) (next : spec.Range query → OracleComp spec Result)
    (tail : spec.Range head → OracleComp spec Result)
    (occurs : Occurs query next (spec.query head >>= tail)) :
    (⟨query, next⟩ : Σ q, spec.Range q → OracleComp spec Result) = ⟨head, tail⟩ ∨
      ∃ reply, Occurs query next (tail reply) := by
  exact occurs

/-- The exact current query and its original continuation occur at this node. -/
theorem here {ι Result : Type} {spec : OracleSpec ι}
    (query : ι) (next : spec.Range query → OracleComp spec Result) :
    Occurs query next (spec.query query >>= next) := Or.inl rfl

/-- An occurrence after any original typed reply remains an occurrence of the original whole program. -/
theorem later {ι Result : Type} {spec : OracleSpec ι}
    (query head : ι) (next : spec.Range query → OracleComp spec Result)
    (tail : spec.Range head → OracleComp spec Result) (reply : spec.Range head)
    (occurs : Occurs query next (tail reply)) : Occurs query next (spec.query head >>= tail) :=
  Or.inr ⟨reply, occurs⟩

open RawCtxPendingMixedPrefix

/-- A supported stop of the actual mixed scanner contains a query and full continuation from the same original program. -/
theorem scan_occurs {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (client : OracleComp spec Result) (index : Nat) (state reached : State)
    (target : ι) (continuation : spec.Range target → OracleComp spec Result)
    (supported : (Stopped.pending target continuation, reached) ∈ support (scan selected impl client index state)) :
    Occurs target continuation client := by
  induction client using OracleComp.inductionOn generalizing index state with
  | pure value =>
      simp only [scan_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
      cases supported.1
  | query_bind query next ih =>
      cases chosen : selected query with
      | false =>
          simp only [scan_other selected impl query next chosen, support_bind, Set.mem_iUnion] at supported
          rcases supported with ⟨reply, _, supported⟩
          exact later target query continuation next reply.1 (ih reply.1 index reply.2 supported)
      | true =>
          cases index with
          | zero =>
              simp only [scan_selected_zero selected impl query next chosen, support_pure,
                Set.mem_singleton_iff, Prod.mk.injEq] at supported
              cases supported.1
              exact here _ _
          | succ index =>
              simp only [scan_selected_succ selected impl query next chosen, support_bind, Set.mem_iUnion] at supported
              rcases supported with ⟨reply, _, supported⟩
              exact later target query continuation next reply.1 (ih reply.1 index reply.2 supported)

end BeaconcryptCore.Computational.RawCtxQueryOccurrence

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrence.pure_impossible' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrence.pure_impossible

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrence.query_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrence.query_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrence.here' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrence.here

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrence.later' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrence.later

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrence.scan_occurs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrence.scan_occurs
