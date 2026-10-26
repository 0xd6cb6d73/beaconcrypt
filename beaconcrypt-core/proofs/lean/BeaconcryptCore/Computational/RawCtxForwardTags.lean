import BeaconcryptCore.Computational.RawCtxForwardScan
import BeaconcryptCore.Computational.RawCtxForwardAnnotationLift

/-!
Properties of the descriptor constructed at an actual annotated query are checked throughout the complete source syntax and every reply. The executable scanner returns that very descriptor, so these certificates require neither inversion of its continuation nor a replacement existential witness.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardTags
open RawCtxForwardAnnotation
variable {Tag Other ι Result Value State : Type} {base : OracleSpec.{0,0} ι}

noncomputable def All (predicate : Tag → Prop) (client : OracleComp (Spec Tag base) Result) : Prop :=
  OracleComp.recOn client (fun _ => True) (fun query _ recurse =>
    (∀ tag, query.1 = some tag → predicate tag) ∧ ∀ reply, recurse reply)

/-- A pure return carries no descriptor obligations. -/
theorem pure_all (predicate : Tag → Prop) (result : Result) :
    All predicate (pure result : OracleComp (Spec Tag base) Result) := trivial

/-- A node certificate covers its actual tag and every complete reply continuation. -/
theorem query_all (predicate : Tag → Prop) (query : (Spec Tag base).Domain)
    (next : (Spec Tag base).Range query → OracleComp (Spec Tag base) Result) :
    All predicate (((Spec Tag base).query query : OracleComp (Spec Tag base) _) >>= next) ↔
      (∀ tag, query.1 = some tag → predicate tag) ∧ ∀ reply, All predicate (next reply) := Iff.rfl

/-- Appending a complete annotated continuation preserves all certificates from both programs. -/
theorem bind_all (predicate : Tag → Prop) (client : OracleComp (Spec Tag base) Value)
    (next : Value → OracleComp (Spec Tag base) Result) (first : All predicate client)
    (later : ∀ value, All predicate (next value)) : All predicate (client >>= next) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact later value
  | query_bind query outside ih =>
      rw [bind_assoc, query_all]
      exact ⟨first.1, fun reply => ih reply (first.2 reply)⟩

/-- Any implication between descriptor certificates applies to every literal carried tag. -/
theorem mono (left right : Tag → Prop) (implies : ∀ tag, left tag → right tag)
    (client : OracleComp (Spec Tag base) Result) (valid : All left client) : All right client := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      exact ⟨fun tag same => implies tag (valid.1 tag same), fun reply => ih reply (valid.2 reply)⟩

/-- Explicit descriptor mapping preserves any certificate proved for its original carried value. -/
theorem map_all (left : Tag → Prop) (right : Other → Prop) (changeTag : Tag → Other)
    (implies : ∀ tag, left tag → right (changeTag tag))
    (client : OracleComp (Spec Tag base) Result) (valid : All left client) :
    All right (mapTags changeTag client) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [mapTags, simulateQ_bind, simulateQ_spec_query]
    constructor
    · intro actual same
      obtain ⟨tag, present, rfl⟩ := Option.map_eq_some_iff.mp same
      exact implies tag (valid.1 tag present)
    · intro reply
      exact ih reply (valid.2 reply)

/-- Forwarding all existing queries into the LIVE sum preserves their mapped descriptor certificates. -/
theorem lift_all {κ : Type} {extra : OracleSpec.{0,0} κ}
    (left : Tag → Prop) (right : Other → Prop) (changeTag : Tag → Other)
    (implies : ∀ tag, left tag → right (changeTag tag))
    (client : OracleComp (Spec Tag base) Result) (valid : All left client) :
    All right (RawCtxForwardAnnotationLift.lift (extra := extra) changeTag client) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [RawCtxForwardAnnotationLift.lift, RawCtxForwardAnnotationLift.adapter,
      simulateQ_bind, simulateQ_spec_query]
    constructor
    · intro actual same
      obtain ⟨tag, present, rfl⟩ := Option.map_eq_some_iff.mp same
      exact implies tag (valid.1 tag present)
    · intro reply
      exact ih reply (valid.2 reply)

/-- A supported executable scan returns the actual carried descriptor with its syntactically established certificate. -/
theorem scan_all
    (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (predicate : Tag → Prop)
    (client : OracleComp (Spec Tag base) Result)
    (covered : RawCtxForwardCoverage.Covered privateQuery client) (valid : All predicate client)
    (state reached : State) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag reached ∈ support
      (RawCtxForwardScan.scan privateQuery selected selection impl client covered state)) : predicate tag := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [RawCtxForwardScan.scan_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
  | query_bind query next ih =>
      cases chosen : selected query.2 state with
      | true =>
          rw [RawCtxForwardScan.scan_cut privateQuery selected selection impl query next covered state chosen] at supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact valid.1 _ (Option.some_get _).symm
      | false =>
          rw [RawCtxForwardScan.scan_other privateQuery selected selection impl query next covered state chosen] at supported
          simp only [support_bind, Set.mem_iUnion] at supported
          obtain ⟨answer, _answered, later⟩ := supported
          exact ih answer.1 (covered.2 answer.1) (valid.2 answer.1) answer.2 later

end BeaconcryptCore.Computational.RawCtxForwardTags
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.pure_all' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.pure_all
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.query_all' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.query_all
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.bind_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.bind_all
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.mono

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.map_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.map_all
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.lift_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.lift_all

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardTags.scan_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardTags.scan_all
