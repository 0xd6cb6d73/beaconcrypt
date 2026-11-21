-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedGame
import BeaconcryptCore.Computational.RegistrationNativeKemEarlyCorrectness

/-! The unchanged candidate-independent native client admits a pure final candidate observer in the ordinary early KEM hop. The real candidate is retained only by that observer, while the one unconditional correctness event covers every repeated selected challenge-ciphertext use. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness
open PqxdhKemIndCca
open PqxdhInitializerSecrecy
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (Context)
open RegistrationNativeKemTotalChallenge (sourcePrepare)
open RegistrationNativeKemEarlyGame (sourcePost)
open RegistrationNativeKemEarlyCorrectness (correctnessError)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

noncomputable def sourceReal (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool)
    (count : Nat) (selected : Fin (count + 1)) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← sourcePrepare baseImpl kem other initial (pure false) count selected 0 chosen
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  sourcePost baseImpl kem other selected chosen context pair.1 pair.2 (observe pair.2 <$> work)

/-- The single ordinary correctness-error event covers every repeated native use of the selected challenge ciphertext. No perfect-correctness premise or conditioned error is introduced. -/
theorem branch_real_error (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (initial : ProbComp Auxiliary)
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool) (count : Nat) (selected : Fin (count + 1)) :
    discreteDistance (RegistrationNativeKemEarlyObservedGame.expanded baseImpl kem other initial work observe count selected true)
      (sourceReal baseImpl kem other initial work observe count selected) ≤ correctnessError baseImpl kem := by
  have point : ∀ (chosen : MlKem768PublicKey × KemSK) (context : Context ambient KemSK Auxiliary count)
      (pair : MlKem768Ciphertext × MlKemSharedSecret),
      discreteDistance (do
          let uniform ← $ᵗ MlKemSharedSecret
          PqxdhDynamicKemPost.evaluate baseImpl kem chosen.2
            pair.1 (RegistrationNativeKemEarlyGame.resume kem other (observe pair.2 <$> work) selected ⟨chosen.1, pair.1, context⟩ (if true then pair.2 else uniform)))
        (do
          let _ ← $ᵗ MlKemSharedSecret
          sourcePost baseImpl kem other selected chosen context pair.1 pair.2 (observe pair.2 <$> work)) ≤
      (𝒟[simulateQ (kemAmbientImpl baseImpl) (do
          let recovered ← kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal := by
    intro chosen context pair
    by_cases good : functional.result chosen.2 pair.1 = some pair.2
    · have agreement : kem.decaps chosen.2 pair.1 = pure (some pair.2) :=
        (functional.exact chosen.2 pair.1).trans (congrArg pure good)
      have same := RegistrationNativeKemEarlyGame.resume_source baseImpl kem other selected chosen context pair.1 pair.2 (observe pair.2 <$> work)
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
  unfold RegistrationNativeKemEarlyObservedGame.expanded sourceReal
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
    (work : OracleComp (Spec ambient KemSK) Value) (observe : MlKemSharedSecret → Value → Bool) (count : Nat) (selected : Fin (count + 1)) :
    (sourceReal baseImpl kem other initial work observe count selected).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem other initial work observe count selected false) ≤
    (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
      (RegistrationNativeKemEarlyObservedGame.adversary baseImpl kem other initial work observe count selected).toINDCCA).toReal +
      correctnessError baseImpl kem := by
  have hop := RegistrationNativeKemEarlyObservedGame.branch_distance baseImpl kem other initial work observe count selected
  have close : (sourceReal baseImpl kem other initial work observe count selected).boolDistance
      (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem other initial work observe count selected true) ≤
      correctnessError baseImpl kem := by
    rw [ProbComp.boolDistance_comm, RegistrationNativeKemEarlyObservedGame.expanded_source]
    refine le_trans ?_ (branch_real_error baseImpl kem functional other initial work observe count selected)
    rw [ProbComp.boolDistance]
    simpa only [← prEvent_eq_evalDist_singleton] using abs_prEvent_toReal_sub_le_discreteDistance _ _
  have triangle := ProbComp.boolDistance_triangle
    (sourceReal baseImpl kem other initial work observe count selected)
    (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem other initial work observe count selected true)
    (RegistrationNativeKemEarlyObservedGame.branch baseImpl kem other initial work observe count selected false)
  rw [hop] at triangle
  linarith

end BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness.branch_real_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness.branch_real_error
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemEarlyObservedCorrectness.source_close
