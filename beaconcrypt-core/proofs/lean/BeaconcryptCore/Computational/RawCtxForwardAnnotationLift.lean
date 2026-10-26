import BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition

/-!
Adding the original LIVE read interface forwards every existing family request through the left branch of the same oracle sum. The carried source descriptor is mapped explicitly, and its full continuation is forwarded before the original outside LIVE client. These source-construction laws preserve exact descriptor soundness and selected-query coverage without an inverse map on functions.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardAnnotationLift
open RawCtxForwardAnnotation RawCtxForwardAnnotationComposition
variable {Tag Other ι κ Value Result : Type} {base : OracleSpec ι} {extra : OracleSpec κ}

def forward : QueryImpl base (OracleComp (base + extra)) := fun query => (base + extra).query (.inl query)

def adapter (changeTag : Tag → Other) : QueryImpl (Spec Tag base) (OracleComp (Spec Other (base + extra))) :=
  fun query => (Spec Other (base + extra)).query (query.1.map changeTag, .inl query.2)

noncomputable def lift (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Value) :
    OracleComp (Spec Other (base + extra)) Value := simulateQ (adapter changeTag) client

noncomputable def liftFrame (saved : Frame base Value) : Frame (base + extra) Value :=
  ⟨.inl saved.1, fun reply => simulateQ forward (saved.2 reply)⟩

/-- Adding the read interface preserves every actual family query and full original continuation after descriptor erasure. -/
theorem erase_lift (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Value) :
    simulateQ erase (lift (extra := extra) changeTag client) =
      simulateQ forward (simulateQ erase client) := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [lift, adapter, simulateQ_bind, simulateQ_spec_query, erase, forward]
    exact bind_congr ih

/-- A carried family descriptor remains exact after forwarding its entire pending continuation into the LIVE interface and appending the original outside client. -/
theorem sound_lift_bind
    (innerFrame : Tag → Frame base Value) (outerFrame : Other → Frame (base + extra) Result)
    (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Value)
    (outside : Value → OracleComp (Spec Other (base + extra)) Result)
    (innerSound : Sound innerFrame client) (outsideSound : ∀ value, Sound outerFrame (outside value))
    (frames : ∀ tag, outerFrame (changeTag tag) =
      appendFrame (fun value => simulateQ erase (outside value)) (liftFrame (innerFrame tag))) :
    Sound outerFrame (lift changeTag client >>= outside) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact outsideSound value
  | query_bind query next ih =>
    change (∀ tag, query.1.map changeTag = some tag →
      (⟨.inl query.2, fun reply => simulateQ erase (lift changeTag (next reply) >>= outside)⟩ : Frame (base + extra) Result) = outerFrame tag) ∧
        ∀ reply, Sound outerFrame (lift changeTag (next reply) >>= outside)
    refine ⟨?_, fun reply => ih reply (innerSound.2 reply)⟩
    intro tag tagged
    obtain ⟨original, present, rfl⟩ := Option.map_eq_some_iff.mp tagged
    rw [frames, ← innerSound.1 original present]
    simp only [appendFrame, liftFrame, simulateQ_bind, erase_lift]
    rfl

/-- Forwarding family queries and appending the original LIVE continuation retains a descriptor at every selected private call. -/
theorem covered_lift_bind
    (selected : base.Domain → Bool) (extended : (base + extra).Domain → Bool)
    (sameSelection : ∀ query, extended (.inl query) = selected query)
    (changeTag : Tag → Other) (client : OracleComp (Spec Tag base) Value)
    (outside : Value → OracleComp (Spec Other (base + extra)) Result)
    (innerCovered : RawCtxForwardCoverage.Covered selected client)
    (outsideCovered : ∀ value, RawCtxForwardCoverage.Covered extended (outside value)) :
    RawCtxForwardCoverage.Covered extended (lift changeTag client >>= outside) := by
  induction client using OracleComp.inductionOn with
  | pure value => exact outsideCovered value
  | query_bind query next ih =>
    change (query.1.map changeTag).isSome = extended (.inl query.2) ∧
      ∀ reply, RawCtxForwardCoverage.Covered extended (lift changeTag (next reply) >>= outside)
    exact ⟨by simpa only [Option.isSome_map, sameSelection] using
      (show query.1.isSome = selected query.2 from innerCovered.1), fun reply => ih reply (innerCovered.2 reply)⟩

end BeaconcryptCore.Computational.RawCtxForwardAnnotationLift

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotationLift.erase_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotationLift.erase_lift
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotationLift.sound_lift_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotationLift.sound_lift_bind
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardAnnotationLift.covered_lift_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardAnnotationLift.covered_lift_bind
