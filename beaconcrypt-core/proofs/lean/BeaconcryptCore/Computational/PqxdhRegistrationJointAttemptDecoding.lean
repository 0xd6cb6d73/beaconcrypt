-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointIssuedAttempts

/-! The complete source-ordered signing transcript determines its entire tuple-attempt history. This is tagged byte encoding injectivity, not a cryptographic public-key injectivity assumption. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding
open PqxdhEd25519EufCma PqxdhRegistrationJointIssuedAttempts

/-- Three canonical source messages uniquely encode each chronological attempt, including repetitions. -/
theorem history_injective : Function.Injective history := by
  intro first
  induction first with
  | nil =>
      intro second same
      cases second <;> simp_all [history, messages]
  | cons keys rest ih =>
      intro second same
      cases second with
      | nil => simp [history, messages] at same
      | cons other tail =>
          simp only [history, List.flatMap_cons, messages, List.cons_append, List.nil_append,
            List.cons.injEq] at same
          exact congrArg₂ List.cons
            (Phase1KeyTuple.ext' (prekeyMessage_injective same.1)
              (oneTimeMessage_injective same.2.1) (pqMessage_injective same.2.2.1))
            (ih same.2.2.2)

/-- Membership in the uniquely determined complete chronological attempt list, expressed using only the literal source signing transcript. -/
def Occurred (decoded : Phase1KeyTuple) (transcript : List Pqxdh.Bytes) : Prop :=
  ∃ attempts, transcript = history attempts ∧ decoded ∈ attempts

/-- On the actual source-ordered transcript this event is exactly membership in its real attempt list, not membership in an alternative reconstruction. -/
theorem occurred_iff (decoded : Phase1KeyTuple) (attempts : List Phase1KeyTuple) :
    Occurred decoded (history attempts) ↔ decoded ∈ attempts := by
  constructor
  · rintro ⟨other, same, member⟩
    exact history_injective same ▸ member
  · intro member
    exact ⟨attempts, rfl, member⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding.history_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding.history_injective

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding.occurred_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptDecoding.occurred_iff
