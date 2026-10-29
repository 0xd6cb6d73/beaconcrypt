-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchProgram

/-! A matching candidate in the actual returned list makes an ideal all-negative batch unlikely. The proof selects the first matching candidate only in its analysis, keeps every preceding check's actual state, and charges at most one additional earlier literal address per preceding candidate. The executable tester never receives that selection or a protection predicate. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacSha512)
open RegistrationNativeRelatedFamily (Spec State)
open RegistrationNativeKnownInputBatchProgram (test cons_run')
open RegistrationNativeKnownInputBatchCache (addresses Covers)

def Matches (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidates : List DhOutput) : Prop :=
  ∃ first ∈ candidates, joint.staticDh seed (dh.publicKey scalar) = some first

/-- Returning false after the whole batch requires the actual first check to return false. -/
theorem prefix_false (implementation : QueryImpl Spec (StateT State ProbComp))
    (first : DhOutput) (rest : List DhOutput) (before : State) :
    Pr{let result ← (simulateQ implementation (test (first :: rest))).run' before}[result = false] ≤
      Pr{let result ← (simulateQ implementation (RegistrationNativeKnownInputCheck.check first)).run' before}[result = false] := by
  rw [cons_run', StateT.run'_eq, prEvent_map]
  apply prEvent_bind_le_prEvent_of_support
  intro result _supported notFalse
  cases found : result.1 with
  | false => exact (notFalse found).elim
  | true => simp only [ite_true, prEvent_pure, Bool.true_eq_false, ite_false]

/-- The actual ideal tester misses a list containing a matching first DH only with its explicit earlier-address and512-bit point-probability allowance. -/
theorem ideal_false (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (candidates : List DhOutput)
    (matching : Matches joint dh seed scalar candidates) (before : State) (covered : Covers joint dh seed scalar before) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar)
      (test candidates)).run' before}[result = false] ≤
      ((addresses joint dh seed scalar before.history).length + candidates.length : Nat) * (256 ^ 32 : ℝ≥0∞)⁻¹ +
        (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  induction candidates generalizing before with
  | nil =>
      obtain ⟨first, member, _same⟩ := matching
      cases member
  | cons first rest ih =>
      by_cases headMatch : joint.staticDh seed (dh.publicKey scalar) = some first
      · refine (prefix_false _ first rest before).trans ?_
        refine (RegistrationNativeKnownInputBatch.ideal_false_bound hmac joint dh seed scalar first before headMatch
          (addresses joint dh seed scalar before.history) covered).trans ?_
        gcongr
        omega
      · have tailMatch : Matches joint dh seed scalar rest := by
          obtain ⟨chosen, member, correct⟩ := matching
          rcases List.mem_cons.mp member with same | member
          · subst chosen
            exact (headMatch correct).elim
          · exact ⟨chosen, member, correct⟩
        rw [cons_run']
        apply prEvent_bind_le_of_forall_le_of_support
        intro middle reached
        cases found : middle.1 with
        | true =>
            simp only [ite_true, prEvent_pure, Bool.true_eq_false, ite_false]
            exact zero_le
        | false =>
            simp only [Bool.false_eq_true, ite_false]
            have nextCovered := RegistrationNativeKnownInputBatchCache.program_covers hmac joint dh seed scalar
              (RegistrationNativeKnownInputCheck.check first) before middle covered reached
            have count := RegistrationNativeKnownInputBatchCounting.program_count hmac joint dh seed scalar
              (RegistrationNativeKnownInputCheck.check first) 1 (RegistrationNativeKnownInputBatchCounting.check_cap first)
              before middle reached
            refine (ih tailMatch middle.2 nextCovered).trans ?_
            have total : (addresses joint dh seed scalar middle.2.history).length + rest.length ≤
                (addresses joint dh seed scalar before.history).length + (first :: rest).length := by
              simp only [List.length_cons]
              omega
            have cast : (((addresses joint dh seed scalar middle.2.history).length + rest.length : Nat) : ℝ≥0∞) ≤
                (((addresses joint dh seed scalar before.history).length + (first :: rest).length : Nat) : ℝ≥0∞) := by
              exact_mod_cast total
            simpa only [add_comm, mul_comm] using
              add_le_add_right (mul_le_mul_right cast (256 ^ 32 : ℝ≥0∞)⁻¹) (2 ^ 512 : ℝ≥0∞)⁻¹

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound.prefix_false' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound.prefix_false
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound.ideal_false' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound.ideal_false
