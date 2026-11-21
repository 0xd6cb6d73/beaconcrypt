import BeaconcryptCore.Computational.RawCtxForwardCoverage

/-!
Forward source descriptors compose with their complete original outside programs. Mapping a carried descriptor and appending an annotated continuation preserves the literal erased pending frame when the concrete frame constructors satisfy the corresponding splice equation. Source frontends discharge that operational equation using their actual peer and role installation; no descriptor is recovered from an existential occurrence or function-equality test.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition
open RawCtxForwardAnnotation

def appendFrame {ι Value Result : Type} {base : OracleSpec ι}
    (outside : Value → OracleComp base Result) (saved : Frame base Value) : Frame base Result :=
  ⟨saved.1, fun reply => saved.2 reply >>= outside⟩

/-- Explicitly carried source frames remain exact through descriptor mapping and the entire original outside continuation. -/
theorem sound_map_bind {Tag Other ι Value Result : Type} {base : OracleSpec ι}
    (innerFrame : Tag → Frame base Value) (outerFrame : Other → Frame base Result)
    (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Value)
    (outside : Value → OracleComp (Spec Other base) Result)
    (innerSound : Sound innerFrame client)
    (outsideSound : ∀ value, Sound outerFrame (outside value))
    (frames : ∀ tag, outerFrame (changeTag tag) =
      appendFrame (fun value => simulateQ erase (outside value)) (innerFrame tag)) :
    Sound outerFrame (mapTags changeTag client >>= outside) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact outsideSound value
  | query_bind query next ih =>
    change (∀ tag, query.1.map changeTag = some tag →
      (⟨query.2, fun reply => simulateQ erase (mapTags changeTag (next reply) >>= outside)⟩ : Frame base Result) = outerFrame tag) ∧
        ∀ reply, Sound outerFrame (mapTags changeTag (next reply) >>= outside)
    refine ⟨?_, fun reply => ih reply (innerSound.2 reply)⟩
    intro tag tagged
    obtain ⟨original, present, rfl⟩ := Option.map_eq_some_iff.mp tagged
    rw [frames, ← innerSound.1 original present]
    simp only [appendFrame, simulateQ_bind, erase_mapTags]
    rfl

/-- Descriptor mapping and complete outside continuations retain exact annotation coverage of every selected source query. -/
theorem covered_map_bind {Tag Other ι Value Result : Type} {base : OracleSpec ι}
    (selected : base.Domain → Bool) (changeTag : Tag → Other)
    (client : OracleComp (Spec Tag base) Value)
    (outside : Value → OracleComp (Spec Other base) Result)
    (innerCovered : RawCtxForwardCoverage.Covered selected client)
    (outsideCovered : ∀ value, RawCtxForwardCoverage.Covered selected (outside value)) :
    RawCtxForwardCoverage.Covered selected (mapTags changeTag client >>= outside) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact outsideCovered value
  | query_bind query next ih =>
    change (query.1.map changeTag).isSome = selected query.2 ∧
      ∀ reply, RawCtxForwardCoverage.Covered selected (mapTags changeTag (next reply) >>= outside)
    exact ⟨by simpa only [Option.isSome_map] using
      (show query.1.isSome = selected query.2 from innerCovered.1), fun reply => ih reply (innerCovered.2 reply)⟩

end BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition.sound_map_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition.sound_map_bind
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition.covered_map_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition.covered_map_bind
