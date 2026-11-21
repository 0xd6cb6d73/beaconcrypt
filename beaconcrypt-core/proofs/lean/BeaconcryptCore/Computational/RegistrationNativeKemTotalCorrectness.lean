-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemTotalChallenge
import BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped

/-! The total native source and its indexed candidate replacement differ by one ordinary CCA advantage and one ordinary KEM correctness error. Completed and unmatched branches remain present. The uniform unmatched branch retains its selected-handle dummy-challenge-ciphertext substitution explicitly; no active-agreement-only interpretation is asserted. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness
open PqxdhKemIndCca
open PqxdhInitializerSecrecy
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context)
open RegistrationNativeKemTotalChallenge (sourcePrepare sourcePost)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def correctnessError (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) : ℝ :=
  (𝒟[simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)] {true}).toReal

noncomputable def branch (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← sourcePrepare baseImpl kem other initial work count selected index chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2 pair.1
    (RegistrationNativeKemTotalGame.resume kem other selected ⟨chosen.1, pair.1, context⟩ (if real then pair.2 else uniform))

noncomputable def sourceReal (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← sourcePrepare baseImpl kem other initial work count selected index chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  sourcePost baseImpl kem other selected chosen ⟨chosen.1, pair.1, context⟩ pair.2

/-- The executable native CCA branch is exactly its complete source prephase and blocked postphase, retaining all private state. -/
theorem branch_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    RegistrationNativeKemTotalGame.branch baseImpl kem other initial work count selected index real =
      branch baseImpl kem other initial work count selected index real := by
  simp only [RegistrationNativeKemTotalGame.branch, oneKeyBranchMain, oneKeyPrefix, oneKeyFinish,
    RegistrationNativeKemTotalGame.adversary, branch, simulateQ_bind, bind_assoc, pure_bind,
    runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftProbComp]
  apply bind_congr
  intro chosen
  have same := RegistrationNativeKemChallenge.prepare_source baseImpl kem other initial work count selected index chosen
  change simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl chosen.2)
      (RegistrationNativeKemGame.prepare baseImpl kem other initial work count selected index chosen.1)) = _ at same
  rw [same]
  rfl

/-- The single ordinary correctness-error event covers every repeated native use of the selected challenge ciphertext. No perfect-correctness premise or conditioned error is introduced. -/
theorem branch_real_error (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    discreteDistance (branch baseImpl kem other initial work count selected index true)
      (sourceReal baseImpl kem other initial work count selected index) ≤ correctnessError baseImpl kem := by
  have point : ∀ (chosen : MlKem768PublicKey × KemSK) (context : Context ambient KemSK Auxiliary count)
      (pair : MlKem768Ciphertext × MlKemSharedSecret),
      discreteDistance (do
          let uniform ← $ᵗ MlKemSharedSecret
          PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2
            pair.1 (RegistrationNativeKemTotalGame.resume kem other selected ⟨chosen.1, pair.1, context⟩ (if true then pair.2 else uniform)))
        (do
          let _ ← $ᵗ MlKemSharedSecret
          sourcePost baseImpl kem other selected chosen
            ⟨chosen.1, pair.1, context⟩ pair.2) ≤
      (𝒟[simulateQ (kemAmbientImpl baseImpl) (do
          let recovered ← kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal := by
    intro chosen context pair
    by_cases good : functional.result chosen.2 pair.1 = some pair.2
    · have agreement : kem.decaps chosen.2 pair.1 = pure (some pair.2) :=
        (functional.exact chosen.2 pair.1).trans (congrArg pure good)
      have same := RegistrationNativeKemTotalChallenge.resume_source baseImpl kem other selected chosen context pair.1 pair.2
        agreement
      simp only [↓reduceIte, same, discreteDistance_self]
      exact ENNReal.toReal_nonneg
    · have bad : (𝒟[simulateQ (kemAmbientImpl baseImpl) (do
          let recovered ← kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal = 1 := by
        rw [functional.exact]
        simp [good]
      rw [bad]
      exact discreteDistance_le_one _ _
  unfold branch sourceReal
  refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
    (fun pair => simulateQ (kemAmbientImpl baseImpl)
      (PqxdhKemCorrectnessStopped.keyError kem pair.1 pair.2))
    (fun result => result = true) ?_) (le_of_eq ?_)
  · intro chosen
    refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
      (fun _ => simulateQ (kemAmbientImpl baseImpl)
        (PqxdhKemCorrectnessStopped.keyError kem chosen.1 chosen.2))
      (fun result => result = true) ?_) (le_of_eq ?_)
    · intro context
      refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
        (fun pair => simulateQ (kemAmbientImpl baseImpl) (do
          let recovered ← kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2))))
        (fun result => result = true) ?_) (le_of_eq ?_)
      · intro pair
        rw [prEvent_eq_evalDist_singleton]
        exact point chosen context pair
      · simp only [PqxdhKemCorrectnessStopped.keyError, simulateQ_bind]
    · rw [(OracleComp.EvalDistEq.bind_const _ _).prEvent_eq (fun result => result = true)]
  · rw [correctnessError, ← prEvent_eq_evalDist_singleton _ true,
      PqxdhKemCorrectnessStopped.error_keygen, simulateQ_bind]


/-- The actual native selected-getter source admits a genuine two-sided ordinary KEM hop with coefficient-one CCA and correctness losses. -/
theorem source_close (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Bool) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (sourceReal baseImpl kem other initial work count selected index).boolDistance
      (RegistrationNativeKemTotalGame.branch baseImpl kem other initial work count selected index false) ≤
    (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (RegistrationNativeKemTotalGame.adversary baseImpl kem other initial work count selected index).toINDCCA).toReal +
      correctnessError baseImpl kem := by
  have hop := RegistrationNativeKemTotalGame.branch_distance baseImpl kem other initial work count selected index
  have close : (sourceReal baseImpl kem other initial work count selected index).boolDistance
      (RegistrationNativeKemTotalGame.branch baseImpl kem other initial work count selected index true) ≤
      correctnessError baseImpl kem := by
    rw [ProbComp.boolDistance_comm, branch_source]
    refine le_trans ?_ (branch_real_error baseImpl kem functional other initial work count selected index)
    rw [ProbComp.boolDistance]
    simpa only [← prEvent_eq_evalDist_singleton] using abs_prEvent_toReal_sub_le_discreteDistance _ _
  have triangle := ProbComp.boolDistance_triangle
    (sourceReal baseImpl kem other initial work count selected index)
    (RegistrationNativeKemTotalGame.branch baseImpl kem other initial work count selected index true)
    (RegistrationNativeKemTotalGame.branch baseImpl kem other initial work count selected index false)
  rw [hop] at triangle
  linarith

end BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness.branch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness.branch_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness.branch_real_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness.branch_real_error

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemTotalCorrectness.source_close
