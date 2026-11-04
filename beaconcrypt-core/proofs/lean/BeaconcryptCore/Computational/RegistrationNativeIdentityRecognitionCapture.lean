-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityQueryGuard
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition

/-! The executable recognition guard returns its first actual witness before submitting the forbidden request. Erasing that witness is exactly the existing stop guard. Thus a stopped public query yields usable signature bytes for the ordinary EUF adversary; a bare stop flag is never assumed to be a forgery. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture
variable {I Value Witness State : Type} {spec : OracleSpec I}

def erase : Witness ⊕ Value → Option Value
  | .inl _ => none
  | .inr value => some value

def capture (recognize : spec.Domain → Option Witness) (work : OracleComp spec Value) :
    OracleComp spec (Witness ⊕ Value) :=
  OracleComp.construct (C := fun _ => OracleComp spec (Witness ⊕ Value))
    (fun value => pure (.inr value))
    (fun query _next continued => match recognize query with
      | some witness => pure (.inl witness)
      | none => do let reply ← spec.query query; continued reply) work

private theorem pure_capture (recognize : spec.Domain → Option Witness) (value : Value) :
    capture recognize (pure value) = pure (.inr value) := rfl
private theorem query_capture (recognize : spec.Domain → Option Witness) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec Value) :
    capture recognize (spec.query query >>= next) = (match recognize query with
      | some witness => pure (.inl witness)
      | none => do let reply ← spec.query query; capture recognize (next reply)) := rfl

/-- The first-witness guard has exactly the same stopping paths as the Boolean guard. -/
theorem erased (recognize : spec.Domain → Option Witness) (work : OracleComp spec Value) :
    erase <$> capture recognize work =
      RegistrationNativeIdentityQueryGuard.cut (fun query => (recognize query).isNone) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    rw [query_capture]
    change _ = (if (recognize query).isNone then (do let reply ← (spec.query query : OracleComp spec _); RegistrationNativeIdentityQueryGuard.cut (fun query => (recognize query).isNone) (next reply)) else pure none)
    cases found : recognize query with
    | none =>
      simp only [Option.isNone_none, ite_true, map_bind]
      simp only [ih]
    | some witness => simp only [Option.isNone_some, Bool.false_eq_true, ite_false, map_pure, erase]

/-- Only unrecognized requests are actually submitted, even when the returned first witness is retained. -/
theorem submitted (recognize : spec.Domain → Option Witness) (work : OracleComp spec Value) :
    AllQueriesSatisfy (capture recognize work) (fun query => recognize query = none) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [pure_capture]; trivial
  | query_bind query next ih =>
    rw [query_capture]
    cases found : recognize query with
    | some witness => trivial
    | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨found, ih⟩

/-- Every returned witness is justified by an actual recognized request on this reached prefix. -/
theorem valid (handler : QueryImpl spec (StateT State ProbComp))
    (recognize : spec.Domain → Option Witness) (property : Witness → Prop)
    (recognizes : ∀ query witness, recognize query = some witness → property witness)
    (work : OracleComp spec Value) (before : State) (result : (Witness ⊕ Value) × State)
    (reached : result ∈ support ((simulateQ handler (capture recognize work)).run before)) :
    ∀ witness, result.1 = .inl witness → property witness := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [pure_capture, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    intro witness same
    cases same
  | query_bind query next ih =>
    rw [query_capture] at reached
    cases found : recognize query with
    | some witness =>
      simp only [found, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      cases reached
      intro chosen same
      cases same
      exact recognizes query witness found
    | none =>
      simp only [found, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, _called, continued⟩ := reached
      exact ih middle.1 middle.2 result continued

/-- Returning a candidate exposes the recognition loss as the actual witness event, retaining all allowed draws and complete interpreter state. -/
theorem cover (handler : QueryImpl spec (StateT State ProbComp)) (recognize : spec.Domain → Option Witness)
    (work : OracleComp spec Value) (event : Value × State → Prop) (before : State) :
    Pr{let result ← (simulateQ handler work).run before}[event result] ≤
      Pr{let result ← (simulateQ handler (capture recognize work)).run before}[
        ∃ witness, result.1 = .inl witness] +
      Pr{let result ← (simulateQ handler (capture recognize work)).run before}[
        ∃ value, result.1 = .inr value ∧ event (value, result.2)] := by
  have upper := RegistrationNativeIdentityQueryGuard.cover handler (fun query => (recognize query).isNone) work event before
  rw [← erased recognize work] at upper
  simp only [simulateQ_map, StateT.run_map, prEvent_map] at upper
  apply upper.trans
  apply (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le _ _ _)
  rintro ⟨value, current⟩ _ held
  cases value with
  | inl witness => exact Or.inl ⟨witness, rfl⟩
  | inr value => exact Or.inr ⟨value, rfl, held⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.erased' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.erased

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.submitted' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionCapture.submitted
