import BeaconcryptCore.Computational.RawCtxQueryOccurrence

/-!
The complete original query continuation is preserved by sequential composition and literal query forwarding. These syntactic decomposition laws classify original program branches without assuming their runtime reachability or any primitive success.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition
open RawCtxQueryOccurrence

/-- An original bound program occurrence comes from the left program with its same outer continuation, or from an original outer-client branch. -/
theorem bind_cases {ι Value Result : Type} {spec : OracleSpec.{0, 0} ι}
    (query : ι) (next : spec.Range query → OracleComp spec Result)
    (left : OracleComp spec Value) (outer : Value → OracleComp spec Result)
    (occurs : Occurs query next (left >>= outer)) :
    (∃ inner : spec.Range query → OracleComp spec Value,
      Occurs query inner left ∧ next = fun reply => inner reply >>= outer) ∨
      ∃ value, Occurs query next (outer value) := by
  induction left using OracleComp.inductionOn with
  | pure value => exact Or.inr ⟨value, occurs⟩
  | query_bind head tail ih =>
    rw [bind_assoc] at occurs
    rcases query_cases query head next (fun reply => tail reply >>= outer) occurs with current | following
    · rcases Sigma.mk.inj_iff.mp current with ⟨same, continuation⟩
      subst head
      exact Or.inl ⟨tail, here query tail, eq_of_heq continuation⟩
    · rcases following with ⟨reply, following⟩
      rcases ih reply following with ⟨inner, inside, continuation⟩ | outside
      · exact Or.inl ⟨inner, later query head inner tail reply inside, continuation⟩
      · exact Or.inr outside

def inlForward {ι κ : Type} {spec : OracleSpec.{0, 0} ι} {extra : OracleSpec.{0, 0} κ} :
    QueryImpl spec (OracleComp (spec + extra)) := fun query => (spec + extra).query (.inl query)

/-- Literal left forwarding retains the original query and entire forwarded continuation; no query can originate in the added capability. -/
theorem inl_cases {ι κ Result : Type} {spec : OracleSpec.{0, 0} ι} {extra : OracleSpec.{0, 0} κ}
    (query : ι ⊕ κ) (next : (spec + extra).Range query → OracleComp (spec + extra) Result)
    (client : OracleComp spec Result)
    (occurs : Occurs query next (simulateQ inlForward client)) :
    ∃ (originalQuery : ι) (originalNext : spec.Range originalQuery → OracleComp spec Result),
      Occurs originalQuery originalNext client ∧
        (⟨query, next⟩ : Σ q, (spec + extra).Range q → OracleComp (spec + extra) Result) =
          ⟨.inl originalQuery, fun reply => simulateQ inlForward (originalNext reply)⟩ := by
  induction client using OracleComp.inductionOn with
  | pure value =>
    simp only [simulateQ_pure] at occurs
    exact False.elim (pure_impossible query next value occurs)
  | query_bind head tail ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, inlForward] at occurs
    rcases query_cases query (.inl head) next (fun reply => simulateQ inlForward (tail reply)) occurs with current | following
    · exact ⟨head, tail, here head tail, current⟩
    · rcases following with ⟨reply, following⟩
      rcases ih reply following with ⟨originalQuery, originalNext, inside, same⟩
      exact ⟨originalQuery, originalNext, later originalQuery head originalNext tail reply inside, same⟩

end BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition.bind_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition.bind_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition.inl_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition.inl_cases
