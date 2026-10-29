-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownInputCheck

/-! A candidate first-DH checker uses a new independent final input word after the actual prior Family state. The finite false-negative bound accounts for every earlier cached literal input before using the full512-bit fresh PRK point probability. No independence of an adaptively chosen earlier PRK is assumed. -/
open OracleComp OracleSpec CoreModels ENNReal Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhSecretInputKdf (HmacBlock HmacSha512)
open RegistrationNativeRelatedFamily (Spec State)
variable {Value : Type}

/-- Actual Family coin queries preserve the complete prior cache and observation history. -/
theorem coins_run (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl PqxdhSecretInputKdf.HmacOracle
      (StateT PqxdhSecretInputKdf.HmacOracle.QueryCache ProbComp))
    (work : ProbComp Value) (before : State) :
    (simulateQ (RegistrationNativeRelatedFamily.impl hmac joint dh seed scalar extractImpl)
      (simulateQ RegistrationNativeKnownInputCheck.coins work)).run before =
      (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind coin next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeKnownInputCheck.coins,
        RegistrationNativeRelatedFamily.impl, StateT.run,
        StateT.monad_bind_def, StateT.bind, bind_assoc, pure_bind, map_bind]
      apply bind_congr
      intro reply
      exact ih reply

/-- The actual randomized checker samples its suffix before running the complete original fixed-suffix checker. -/
theorem check_run (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (extractImpl : QueryImpl PqxdhSecretInputKdf.HmacOracle
      (StateT PqxdhSecretInputKdf.HmacOracle.QueryCache ProbComp))
    (first : DhOutput) (before : State) :
    (simulateQ (RegistrationNativeRelatedFamily.impl hmac joint dh seed scalar extractImpl)
      (RegistrationNativeKnownInputCheck.check first)).run' before =
      ($ᵗ DhOutput >>= fun suffix =>
        (simulateQ (RegistrationNativeRelatedFamily.impl hmac joint dh seed scalar extractImpl)
          (RegistrationNativeKnownInputCheck.checkAt first suffix)).run' before) := by
  simp only [RegistrationNativeKnownInputCheck.check, StateT.run'_eq, simulateQ_bind, StateT.run_bind,
    coins_run, bind_map_left, map_bind]

/-- A matching candidate's actual ideal false-negative probability is bounded by prior-address collisions plus the fresh complete-PRK point probability. -/
theorem ideal_false_bound (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first : DhOutput) (before : State)
    (matching : joint.staticDh seed (dh.publicKey scalar) = some first)
    (earlier : List Pqxdh.Bytes) (covered : ∀ bytes, before.cache bytes ≠ none → bytes ∈ earlier) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.check first)).run' before}[result = false] ≤
      earlier.length * (256 ^ 32 : ℝ≥0∞)⁻¹ + (2 ^ 512 : ℝ≥0∞)⁻¹ := by
  rw [RegistrationNativeRelatedFamily.idealImpl, check_run]
  refine (prEvent_bind_le_prEvent_add_of_support ($ᵗ DhOutput)
    (fun suffix => (simulateQ (RegistrationNativeRelatedFamily.idealImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.checkAt first suffix)).run' before)
    (fun suffix => RegistrationNativeKnownInputCheck.bytes first suffix ∈ earlier) (fun result => result = false)
    (ε := (2 ^ 512 : ℝ≥0∞)⁻¹) ?_).trans ?_
  · intro suffix _supported separate
    have fresh : before.cache (RegistrationNativeKnownInputCheck.bytes first suffix) = none := by
      by_contra cached
      exact separate (covered _ cached)
    exact le_of_eq (RegistrationNativeKnownInputCheck.ideal_fresh_false512 hmac joint dh seed scalar first suffix before matching fresh)
  · exact add_le_add (RegistrationNativeKnownInputCheck.earlier_collisions first earlier) le_rfl

/-- The actual randomized real checker always returns false after every prior native Family state. -/
theorem real_false (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first : DhOutput) (before : State) :
    (simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.check first)).run' before = (fun _ : DhOutput => false) <$> ($ᵗ DhOutput) := by
  rw [RegistrationNativeRelatedFamily.realImpl, check_run]
  change ($ᵗ DhOutput >>= fun suffix =>
    (simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.checkAt first suffix)).run' before) = _
  simp only [RegistrationNativeKnownInputCheck.real_false, bind_pure_comp]

/-- The randomized real tester has false output with probability one while retaining its actual suffix draw. -/
theorem real_false_probability (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (first : DhOutput) (before : State) :
    Pr{let result ← (simulateQ (RegistrationNativeRelatedFamily.realImpl hmac joint dh seed scalar)
      (RegistrationNativeKnownInputCheck.check first)).run' before}[result = false] = 1 := by
  rw [real_false, prEvent_map]
  exact (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr (fun _ => rfl)

end BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.coins_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.coins_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.check_run' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.check_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.ideal_false_bound' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.ideal_false_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.real_false' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.real_false

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.real_false_probability' depends on axioms: [propext,
 choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownInputBatch.real_false_probability
