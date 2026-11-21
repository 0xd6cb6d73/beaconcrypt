-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace

/-! The original chronological native repeated-role event lifts through actual pointwise Word-event evaluation without changing its ordered witnesses. The repeated selected192-byte input then exposes a candidate-equal literal at one of those same two protocol events. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhKemIndCca (MlKemSharedSecret)
open RegistrationNativeSecretWordMessage (Message eval)
open RegistrationNativeSecretWordFrontendTrace (Event)
open PqxdhRecordLiftInterface (Role)

private theorem map_split {A B : Type} (map : A → B) (values : List A) (before : List B) (value : B) (after : List B)
    (formed : values.map map = before ++ value :: after) :
    ∃ first selected last, values = first ++ selected :: last ∧ first.map map = before ∧ map selected = value ∧ last.map map = after := by
  induction before generalizing values with
  | nil =>
      cases values with
      | nil => simp only [List.map_nil, List.nil_append, reduceCtorEq] at formed
      | cons head tail =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at formed
          exact ⟨[], head, tail, rfl, rfl, formed.1, formed.2⟩
  | cons head tail ih =>
      cases values with
      | nil => simp only [List.map_nil, List.cons_append, reduceCtorEq] at formed
      | cons first rest =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at formed
          obtain ⟨left, selected, right, same, leftMap, selectedMap, rightMap⟩ := ih rest formed.2
          refine ⟨first :: left, selected, right, ?_, ?_, selectedMap, rightMap⟩
          · simp only [List.cons_append, same]
          · simp only [List.map_cons, formed.1, leftMap]

/-- Native event evaluation retains both exact ordered installation witnesses and their roles. -/
theorem lift_repeat (candidate : MlKemSharedSecret) (events : List Event)
    (earlier middle later : List RegistrationNativeG2Trace.Event) (role : Role)
    (first second : RegistrationNativeRelatedFamily.Message)
    (shape : events.map (RegistrationNativeSecretWordCheckedTrace.event candidate) =
      earlier ++ [.install role first] ++ middle ++ [.installAttempt role second] ++ later) :
    ∃ earlierWord middleWord laterWord firstWord secondWord,
      events = earlierWord ++ [.install role firstWord] ++ middleWord ++ [.installAttempt role secondWord] ++ laterWord ∧
      eval candidate firstWord = first ∧ eval candidate secondWord = second := by
  have firstSplit : events.map (RegistrationNativeSecretWordCheckedTrace.event candidate) =
      earlier ++ RegistrationNativeG2Trace.Event.install role first :: (middle ++ .installAttempt role second :: later) := by
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using shape
  obtain ⟨left, selected, rest, divided, _leftMap, firstEvent, restMap⟩ :=
    map_split (RegistrationNativeSecretWordCheckedTrace.event candidate) events earlier (.install role first) _ firstSplit
  cases selected with
  | prepare message | demand message | encapsulate tag key ciphertext secret | installAttempt actual message =>
      simp only [RegistrationNativeSecretWordCheckedTrace.event, reduceCtorEq] at firstEvent
  | install actual firstWord =>
      simp only [RegistrationNativeSecretWordCheckedTrace.event, RegistrationNativeG2Trace.Event.install.injEq] at firstEvent
      obtain ⟨rfl, firstMessage⟩ := firstEvent
      obtain ⟨center, selected, right, remaining, _centerMap, secondEvent, _rightMap⟩ :=
        map_split (RegistrationNativeSecretWordCheckedTrace.event candidate) rest middle (.installAttempt actual second) later restMap
      cases selected with
      | prepare message | demand message | encapsulate tag key ciphertext secret | install actual message =>
          simp only [RegistrationNativeSecretWordCheckedTrace.event, reduceCtorEq] at secondEvent
      | installAttempt nextRole secondWord =>
          simp only [RegistrationNativeSecretWordCheckedTrace.event, RegistrationNativeG2Trace.Event.installAttempt.injEq] at secondEvent
          obtain ⟨rfl, secondMessage⟩ := secondEvent
          refine ⟨left, center, right, firstWord, secondWord, ?_, firstMessage, secondMessage⟩
          rw [divided, remaining]
          simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The original native repeated-role event at a selectively hidden input has an actual candidate-equal literal witness in its same evaluated Word trace. -/
theorem repeated_literal (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : MlKemSharedSecret) (target : Option DhOutput) (events : List Event)
    (valid : ∀ role, RegistrationNativeSecretWordAtomTraceOrder.Good role events)
    (bounded : ∀ role, events.countP (RegistrationNativeSecretWordAtomInstallTrace.attempt role) ≤ 1)
    (repeated : RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input joint dh seed scalar)
      (RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate)
      (events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))) :
    RegistrationNativeSecretWordAtomRepeatLiteral.LiteralHit candidate joint dh seed scalar target events := by
  obtain ⟨earlier, middle, later, role, first, second, bytes, shape, firstInput, secondInput, selected⟩ := repeated
  obtain ⟨left, center, right, firstWord, secondWord, same, firstEval, secondEval⟩ :=
    lift_repeat candidate events earlier middle later role first second shape
  apply RegistrationNativeSecretWordAtomRepeatLiteral.repeat_literal joint dh seed scalar candidate target events valid bounded
    left center right role firstWord secondWord bytes same
  · rw [firstEval]
    exact firstInput
  · rw [secondEval]
    exact secondInput
  · exact selected

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap.lift_repeat' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap.lift_repeat
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap.repeated_literal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap.repeated_literal
