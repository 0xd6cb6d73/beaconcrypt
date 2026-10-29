-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSuffixKeyPrf
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTrace
import Mathlib.Data.FinEnum

/-! A terminal ordinary PRF adversary can check a list of candidate keys without knowing the primitive's secret key. It samples a fresh160-byte head, asks the complete108-byte suffix-key oracle once, and compares its final32-byte coordinate with public source evaluations of every guess. A true key in the list always Matches. A fresh ideal answer Matches with at most the list-length share of256^32, even after adaptive side computation. This checker is needed when real off-protected root computations could leak the candidate: independence is established in the ideal experiment, never assumed for the real one. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck
open RegistrationNativeSuffixKeyPrf (Prefix Secret Oracle Spec value realImpl idealImpl)

-- The output type is the existing actual108-byte schedule, not a new independent projection.
abbrev Output := PqxdhServerAuthKeySchedule.Output

def coins : QueryImpl unifSpec (OracleComp Spec) := fun coin => Spec.query (.inl coin)

def Matches (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (guesses : List Secret)
    (head : Prefix) (output : Output) : Prop := output.2 ∈ guesses.map (fun key => (value source key head).2)

instance (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (guesses : List Secret)
    (head : Prefix) (output : Output) : Decidable (Matches source guesses head output) :=
  inferInstanceAs (Decidable (output.2 ∈ guesses.map (fun key => (value source key head).2)))

noncomputable def testAt (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (guesses : List Secret) (head : Prefix) : OracleComp Spec Bool := do
  let answer ← (Spec.query (.inr head) : OracleComp Spec Output)
  pure (decide (Matches source guesses head answer))

noncomputable def test (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (guesses : List Secret) :
    OracleComp Spec Bool := do
  let head ← simulateQ coins ($ᵗ Prefix)
  testAt source guesses head

/-- The primitive's real key is recognized by the public checker for every head and every complete source answer. -/
theorem matches_real (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (key : Secret) (guesses : List Secret) (member : key ∈ guesses) (head : Prefix) :
    Matches source guesses head (value source key head) :=
  List.mem_map.mpr ⟨key, member, rfl⟩

/-- The fixed-head real tester returns true whenever the actual key occurs among its guesses. -/
theorem real_at (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (key : Secret) (guesses : List Secret) (member : key ∈ guesses) (head : Prefix) :
    simulateQ (realImpl source key) (testAt source guesses head) = pure true := by
  simp only [testAt, simulateQ_bind, simulateQ_spec_query, RegistrationNativeSuffixKeyPrf.real_query, pure_bind,
    simulateQ_pure, decide_eq_true (matches_real source key guesses member head)]

/-- A fresh complete ideal108-byte answer Matches the candidate list in its final32-byte coordinate only with the explicit finite-list allowance. -/
theorem uniform_match (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (guesses : List Secret) (head : Prefix) :
    Pr{let output ← $ᵗ Output}[Matches source guesses head output] ≤
      guesses.length * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  apply SampleableType.prEvent_uniformSample_prod_le_of_forall_fst
  intro first
  have bounded := RegistrationNativeSecretWordTrace.list_guess (guesses.map (fun key => (value source key head).2))
  simpa only [Matches, List.length_map] using bounded

/-- The fresh checker head has the full160-byte domain, with no fallback input or malformed-prefix branch. -/
theorem head_card : Fintype.card Prefix = 256 ^ 160 := by
  rw [card_vector, ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  rfl

/-- One fixed previously queried head catches only one point of the independently sampled160-byte head. -/
theorem head_point (head : Prefix) : Pr{let sampled ← $ᵗ Prefix}[sampled = head] = (256 ^ 160 : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample_eq_singleton, head_card]
  norm_num

end BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.matches_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.matches_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.real_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.real_at
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.uniform_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.uniform_match
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.head_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.head_card
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.head_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSuffixKeyCheck.head_point
