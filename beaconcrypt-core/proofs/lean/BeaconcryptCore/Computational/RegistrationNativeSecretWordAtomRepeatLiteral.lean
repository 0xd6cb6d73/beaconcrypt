-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedInput
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenService

/-! A repeated same-role installation at the selected literal192-byte input cannot be atom-only once the actual per-role attempt bound is known. It must expose the candidate as a literal descriptor at one of those same ordered installation events. The source link from that event to the actual successful protected material demand is separate and is not assumed by this list/algebra lemma. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhKemIndCca (MlKemSharedSecret)
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message input eval)
open RegistrationNativeSecretWordFrontendTrace (Event)
open PqxdhRecordLiftInterface (Role)

def Exposure (events : List Event) (role : Role) (message : Message) : Prop :=
  Event.install role message ∈ events ∨ Event.installAttempt role message ∈ events

def LiteralHit (candidate : MlKemSharedSecret) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (target : Option DhOutput) (events : List Event) : Prop :=
  ∃ role message key, Exposure events role message ∧ input joint dh seed scalar message = some key ∧
    RegistrationNativeSecretWordProtection.inside target key.head = true ∧
    message.kem = .literal candidate ∧ key.word = .literal candidate

private theorem input_keeps_word (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (key : Key) (formed : input joint dh seed scalar message = some key) : key.word = message.kem := by
  have same := RegistrationNativeSecretWordCheckedInput.input_word joint dh seed scalar message message.kem
  have unchanged : { message with kem := message.kem } = message := by cases message; rfl
  rw [unchanged, formed, Option.map_some, Option.some.injEq] at same
  exact congrArg Key.word same

/-- Actual successful optional input construction retains the exact KEM word and concrete head classifier. -/
theorem selected_input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : MlKemSharedSecret) (target : Option DhOutput) (message : Message) (bytes : Pqxdh.Bytes)
    (native : RegistrationNativeRelatedFamily.input joint dh seed scalar (eval candidate message) = some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate bytes = true) :
    ∃ key, input joint dh seed scalar message = some key ∧ key.word = message.kem ∧
      key.word.eval candidate = candidate ∧ RegistrationNativeSecretWordProtection.inside target key.head = true := by
  have mapped := RegistrationNativeSecretWordMessage.input_eval joint dh seed scalar candidate message
  rw [native] at mapped
  cases formed : input joint dh seed scalar message with
  | none => simp only [formed, Option.map_none, reduceCtorEq] at mapped
  | some key =>
      simp only [formed, Option.map_some, Option.some.injEq] at mapped
      have parsed : RegistrationNativeKeyFamilyPreparation.inside target bytes = true ∧
          PqxdhJointGapDh.readDh 160 bytes = some candidate := by
        simpa only [RegistrationNativeSelectiveHiddenService.selected, Bool.and_eq_true, decide_eq_true_eq] using selected
      have chosen := parsed.2
      have suffix : PqxdhJointGapDh.readDh 160 (RegistrationNativeSecretWord.eval candidate key) = some (key.word.eval candidate) := by
        simp [PqxdhJointGapDh.readDh, RegistrationNativeSecretWord.eval]
        apply List.Vector.toList_injective
        exact List.take_of_length_le (by simp)
      rw [← mapped, suffix, Option.some.injEq] at chosen
      refine ⟨key, rfl, input_keeps_word joint dh seed scalar message key formed, chosen, ?_⟩
      rw [RegistrationNativeSecretWordProtection.inside_eval, mapped]
      exact parsed.1

/-- At the selected native input, an ordered repeated role attempt necessarily exposes a candidate-equal literal descriptor. -/
theorem repeat_literal (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : MlKemSharedSecret) (target : Option DhOutput) (events : List Event)
    (valid : ∀ role, RegistrationNativeSecretWordAtomTraceOrder.Good role events)
    (bounded : ∀ role, events.countP (RegistrationNativeSecretWordAtomInstallTrace.attempt role) ≤ 1)
    (earlier middle later : List Event) (role : Role) (first second : Message) (bytes : Pqxdh.Bytes)
    (shape : events = earlier ++ [.install role first] ++ middle ++ [.installAttempt role second] ++ later)
    (firstInput : RegistrationNativeRelatedFamily.input joint dh seed scalar (eval candidate first) = some bytes)
    (secondInput : RegistrationNativeRelatedFamily.input joint dh seed scalar (eval candidate second) = some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate bytes = true) :
    LiteralHit candidate joint dh seed scalar target events := by
  obtain ⟨firstKey, firstFormed, firstWord, firstValue, firstInside⟩ := selected_input joint dh seed scalar candidate target first bytes firstInput selected
  obtain ⟨secondKey, secondFormed, secondWord, secondValue, secondInside⟩ := selected_input joint dh seed scalar candidate target second bytes secondInput selected
  cases firstShape : first.kem with
  | literal value =>
      have same : value = candidate := by simpa only [firstWord, firstShape, Word.eval] using firstValue
      subst value
      exact ⟨role, first, firstKey, Or.inl (by rw [shape]; simp), firstFormed, firstInside, firstShape, firstWord.trans firstShape⟩
  | atom =>
      cases secondShape : second.kem with
      | literal value =>
          have same : value = candidate := by simpa only [secondWord, secondShape, Word.eval] using secondValue
          subst value
          exact ⟨role, second, secondKey, Or.inr (by rw [shape]; simp), secondFormed, secondInside, secondShape, secondWord.trans secondShape⟩
      | atom => exact False.elim (RegistrationNativeSecretWordAtomTraceOrder.no_second role events (valid role) (bounded role)
          earlier middle later first second shape firstShape secondShape)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral.selected_input' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral.selected_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral.repeat_literal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral.repeat_literal
