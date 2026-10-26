import BeaconcryptCore.Computational.RawCtxSelectedFamilyContext

/-!
Forward annotation attaches an explicit source descriptor while constructing each oracle request. Erasure forwards exactly that request with its original dependent reply. Soundness checks the carried descriptor against the full erased continuation at every annotated node and every reply; it never recovers a descriptor by deciding function equality or choosing an occurrence witness. Concrete source compilers construct these annotations before the corresponding primitive draw.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardAnnotation

abbrev Spec (Tag : Type) {ι : Type} (base : OracleSpec ι) : OracleSpec (Option Tag × base.Domain) :=
  fun query => base.Range query.2

def erase {Tag ι : Type} {base : OracleSpec ι} : QueryImpl (Spec Tag base) (OracleComp base) :=
  fun query => base.query query.2

noncomputable def mapTags {Tag Other ι Result : Type} {base : OracleSpec ι}
    (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Result) : OracleComp (Spec Other base) Result :=
  simulateQ (fun query => (Spec Other base).query (query.1.map changeTag, query.2)) client

abbrev Frame {ι : Type} (base : OracleSpec ι) (Result : Type) :=
  Σ query, base.Range query → OracleComp base Result

noncomputable def Sound {Tag ι Result : Type} {base : OracleSpec ι}
    (frame : Tag → Frame base Result) (client : OracleComp (Spec Tag base) Result) : Prop :=
  OracleComp.recOn client (fun _ => True) (fun query next recurse =>
    (∀ tag, query.1 = some tag → (⟨query.2, fun reply => simulateQ erase (next reply)⟩ : Frame base Result) = frame tag) ∧
      ∀ reply, recurse reply)

/-- Erasing an annotated node forwards the same actual request and complete original reply continuation. -/
theorem erase_query {Tag ι Result : Type} {base : OracleSpec ι}
    (tag : Option Tag) (query : base.Domain)
    (next : base.Range query → OracleComp (Spec Tag base) Result) :
    simulateQ erase (((Spec Tag base).query (tag, query) : OracleComp (Spec Tag base) _) >>= next) =
      ((base.query query : OracleComp base _) >>= fun reply => simulateQ erase (next reply)) := by
  simp only [simulateQ_bind, simulateQ_spec_query, erase]

/-- A completed annotated program carries no pending source descriptor. -/
theorem sound_pure {Tag ι Result : Type} {base : OracleSpec ι}
    (frame : Tag → Frame base Result) (result : Result) : Sound frame (pure result) := trivial

/-- Soundness is checked directly at the carried descriptor and every following typed reply. -/
theorem sound_query {Tag ι Result : Type} {base : OracleSpec ι}
    (frame : Tag → Frame base Result) (tag : Option Tag) (query : base.Domain)
    (next : base.Range query → OracleComp (Spec Tag base) Result) :
    Sound frame (((Spec Tag base).query (tag, query) : OracleComp (Spec Tag base) _) >>= next) ↔
      (∀ actual, tag = some actual → (⟨query, fun reply => simulateQ erase (next reply)⟩ : Frame base Result) = frame actual) ∧
        ∀ reply, Sound frame (next reply) := Iff.rfl

/-- Mapping explicit descriptor data changes no request, reply, state or complete source distribution. -/
theorem erase_mapTags {Tag Other ι Result : Type} {base : OracleSpec ι}
    (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Result) :
    simulateQ erase (mapTags changeTag client) = simulateQ erase client := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [mapTags, simulateQ_bind, simulateQ_spec_query, erase]
    exact bind_congr ih

end BeaconcryptCore.Computational.RawCtxForwardAnnotation

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotation.erase_query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotation.erase_query

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotation.sound_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotation.sound_pure

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotation.sound_query' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotation.sound_query

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotation.erase_mapTags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotation.erase_mapTags
