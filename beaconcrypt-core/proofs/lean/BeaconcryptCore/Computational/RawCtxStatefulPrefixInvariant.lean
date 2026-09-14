import BeaconcryptCore.Computational.RawCtxStatefulPendingPrefix

/-!
A state-dependent pending prefix may use a source invariant to establish the same complete prefix under two handlers. The invariant is checked on every supported unselected callback, and the common computation is an exact OracleComp equality. Completed and pending outputs retain their actual final state. These generic operational premises must be derived by the source consumer; they neither assume selection occurs nor condition on a selected branch.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant
open RawCtxPendingMixedPrefix RawCtxStatefulPendingPrefix

/-- Agreement only at invariant states suffices when actual unselected callbacks preserve that invariant. -/
theorem scan_same {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (left right : QueryImpl spec (StateT State ProbComp))
    (valid : State → Prop)
    (agree : ∀ query state, valid state → selected query state = false →
      (left query).run state = (right query).run state)
    (preserve : ∀ query state, valid state → selected query state = false →
      ∀ reply ∈ support ((left query).run state), valid reply.2)
    (client : OracleComp spec Result) (state : State) (initial : valid state) :
    scan selected left client state = scan selected right client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true => rw [scan_cut selected left query next state chosen, scan_cut selected right query next state chosen]
    | false =>
      rw [scan_other selected left query next state chosen, scan_other selected right query next state chosen,
        ← agree query state initial chosen]
      apply bind_congr_of_forall_mem_support
      intro reply supported
      exact ih reply.1 reply.2 (preserve query state initial chosen reply supported)

/-- Every completed or pending supported prefix retains the invariant at its actual reached state. -/
theorem scan_valid {ι Result State : Type} {spec : OracleSpec ι}
    (selected : ι → State → Bool) (impl : QueryImpl spec (StateT State ProbComp))
    (valid : State → Prop)
    (preserve : ∀ query state, valid state → selected query state = false →
      ∀ reply ∈ support ((impl query).run state), valid reply.2)
    (client : OracleComp spec Result) (state : State) (initial : valid state)
    (result : Prefix spec Result State) (supported : result ∈ support (scan selected impl client state)) :
    valid result.2 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [RawCtxStatefulPendingPrefix.scan_pure, mem_support_pure_iff] at supported
    subst result
    exact initial
  | query_bind query next ih =>
    cases chosen : selected query state with
    | true =>
      rw [scan_cut selected impl query next state chosen, mem_support_pure_iff] at supported
      subst result
      exact initial
    | false =>
      rw [scan_other selected impl query next state chosen, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1 reply.2 (preserve query state initial chosen reply head) tail

end BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant

/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant.scan_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant.scan_same

/-- info: 'BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant.scan_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStatefulPrefixInvariant.scan_valid
