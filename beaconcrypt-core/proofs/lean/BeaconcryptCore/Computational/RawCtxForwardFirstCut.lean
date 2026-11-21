import BeaconcryptCore.Computational.RawCtxForwardTags

/-! An annotated callback with no tags after its first query can only stop before that first query, retaining the whole incoming interpreter state and literal continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardFirstCut
open RawCtxForwardAnnotation RawCtxForwardTags
variable {Tag Other ι Result Value State : Type} {base : OracleSpec.{0,0} ι}

/-- A callback may return immediately, or issue a first query after which none of its reply paths carries a cut descriptor. -/
noncomputable def First (client : OracleComp (Spec Tag base) Result) : Prop :=
  OracleComp.recOn client (fun _ => True) (fun _ next _ => ∀ reply, All (fun _ => False) (next reply))

/-- Pure returns have no later cut descriptor. -/
theorem pure_first (value : Result) : First (pure value : OracleComp (Spec Tag base) Result) := trivial

/-- At a query, the condition covers every typed reply continuation. -/
theorem query_first (query : (Spec Tag base).Domain)
    (next : (Spec Tag base).Range query → OracleComp (Spec Tag base) Result) :
    First (((Spec Tag base).query query : OracleComp (Spec Tag base) _) >>= next) ↔
      ∀ reply, All (fun _ => False) (next reply) := Iff.rfl

/-- Mapping a complete result does not create a later cut descriptor. -/
theorem map_first (change : Value → Result) (client : OracleComp (Spec Tag base) Value)
    (first : First client) : First (change <$> client) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      rw [map_bind, query_first]
      simpa only [bind_pure_comp] using (fun reply => bind_all (fun _ => False) (next reply) (fun value => pure (change value)) (first reply) (fun _ => trivial))

/-- Mapping literal descriptor data preserves the location of the only possible cut. -/
theorem mapTags_first (change : Tag → Other) (client : OracleComp (Spec Tag base) Result)
    (first : First client) : First (mapTags change client) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [mapTags, simulateQ_bind, simulateQ_spec_query, query_first]
      exact fun reply => map_all (fun _ => False) (fun _ => False) change (fun _ impossible => impossible) (next reply) (first reply)

/-- Forwarding into the sum interface keeps the first-query location, for every actual reply. -/
theorem lift_first {κ : Type} {extra : OracleSpec.{0,0} κ} (change : Tag → Other)
    (client : OracleComp (Spec Tag base) Result) (first : First client) :
    First (RawCtxForwardAnnotationLift.lift (extra := extra) change client) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [RawCtxForwardAnnotationLift.lift, RawCtxForwardAnnotationLift.adapter, simulateQ_bind, simulateQ_spec_query, query_first]
      exact fun reply => lift_all (fun _ => False) (fun _ => False) change (fun _ impossible => impossible) (next reply) (first reply)

/-- An actual pending cut occurs before the callback's first query. Its complete state is unchanged, and its saved frame is exactly the whole erased callback. -/
theorem cut_start (privateQuery : base.Domain → Bool) (selected : base.Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT State ProbComp)) (frame : Tag → Frame base Result)
    (client : OracleComp (Spec Tag base) Result) (covered : RawCtxForwardCoverage.Covered privateQuery client)
    (sound : Sound frame client) (first : First client) (state reached : State) (tag : Tag)
    (supported : RawCtxForwardScan.Cut.pending tag reached ∈ support
      (RawCtxForwardScan.scan privateQuery selected selection impl client covered state)) :
    reached = state ∧ simulateQ erase client = ((base.query (frame tag).1 : OracleComp base _) >>= (frame tag).2) := by
  induction client using OracleComp.inductionOn with
  | pure value =>
      simp only [RawCtxForwardScan.scan_pure, mem_support_pure_iff, reduceCtorEq] at supported
  | query_bind query next ih =>
      cases chosen : selected query.2 state with
      | true =>
          rw [RawCtxForwardScan.scan_cut privateQuery selected selection impl query next covered state chosen, mem_support_pure_iff] at supported
          cases supported
          exact ⟨rfl, (erase_query query.1 query.2 next).trans
            (congrArg (fun saved : Frame base Result => (base.query saved.1 : OracleComp base _) >>= saved.2)
              (sound.1 _ (Option.some_get _).symm))⟩
      | false =>
          rw [RawCtxForwardScan.scan_other privateQuery selected selection impl query next covered state chosen,
            mem_support_bind_iff] at supported
          obtain ⟨reply, _, later⟩ := supported
          exact False.elim (scan_all privateQuery selected selection impl (fun _ => False) (next reply.1)
            (covered.2 reply.1) (first reply.1) reply.2 reached tag later)

end BeaconcryptCore.Computational.RawCtxForwardFirstCut

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFirstCut.pure_first' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFirstCut.pure_first
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFirstCut.query_first' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFirstCut.query_first
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFirstCut.map_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFirstCut.map_first
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFirstCut.mapTags_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFirstCut.mapTags_first
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFirstCut.lift_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFirstCut.lift_first
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardFirstCut.cut_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardFirstCut.cut_start
