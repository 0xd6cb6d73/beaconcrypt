-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawChallenge
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame
import BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-! One ordinary one-key ML-KEM IND-CCA adversary runs the initialized source prefix up to the encapsulation of the raw accept at the designated raw-accept ordinal and resumes its exact callback. The real branch is compared with the real stopped-source game through the ordinary ML-KEM correctness-error experiment, not through perfect correctness: no statement here takes a recipient-correctness premise. These games filter inactive selection and selected-key reveal stops exactly as `KemGame` does; they are not a global protocol secrecy assertion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemResume (post sourcePost)
open PqxdhRegistrationJointKemRawChallenge (preRaw sourcePreRaw)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The ordinary ML-KEM correctness-error probability: one actual key pair, one encapsulation to its public key and one actual decapsulation, won by rejection or by recovery of a different secret. -/
noncomputable def correctnessError (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) : ℝ :=
  (𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (PqxdhKemCorrectnessError.errorExperiment setup.kem)] {true}).toReal

/-- The correctness error of the raw-ordinal KEM hop is the existing correctness-error term `PqxdhServerAuthNegativeControl.kemError`: both are the probability that the same error experiment returns `true` under the experiment's ambient coins, so consumers have one quantity, not two. -/
theorem correctnessError_eq_kemError (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) :
    correctnessError setup = PqxdhServerAuthNegativeControl.kemError setup := by
  simp only [correctnessError, PqxdhServerAuthNegativeControl.kemError, ← prEvent_eq_evalDist_singleton _ true]

/-- The constructed ordinary adversary receives only a public challenge key and a candidate reply, runs the actual initialized source compiler up to the encapsulation of the selected raw accept and resumes the saved callback. -/
noncomputable def adversary (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : OneKeyAdversary setup.kem where
  Context := Context KemSK A Bool count
  preChallenge := preRaw setup codec checks ensureInit supplied decision work runtime count selected index
  postChallenge transcript candidate :=
    PqxdhRegistrationJointKemGame.decision <$> post setup count selected transcript candidate

/-- The explicit fixed branch at the raw-accept ordinal: `KemGame.branch` with the prephase `sourcePreRaw`. Both branches retain the challenger encapsulation and the branch-independent uniform draw. -/
noncomputable def branch (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreRaw setup codec checks ensureInit supplied decision work runtime count selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (post setup count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- The real raw-ordinal cut game: `KemGame.sourceReal` with the prephase `sourcePreRaw`. It resumes the literal source callback through the original stopped source interpreter and keeps the harmless challenger ghost draw. -/
noncomputable def sourceReal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreRaw setup codec checks ensureInit supplied decision work runtime count selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let _ ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> sourcePost setup count selected chosen
    ⟨chosen.1, encapsulated.1, context⟩ encapsulated.2

set_option backward.isDefEq.respectTransparency false in
/-- The fixed branch of the constructed ordinary adversary equals the explicit raw-ordinal branch, including failed initialization and every inactive or stopped continuation. -/
theorem branchRaw_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    simulateQ (kemAmbientImpl setup.baseImpl)
      (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied decision work runtime count selected index) real) =
      branch setup codec checks ensureInit supplied decision work runtime count selected index real := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, adversary, branch,
    simulateQ_bind, bind_assoc, pure_bind, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp, simulateQ_map]
  apply bind_congr
  intro chosen
  have same := PqxdhRegistrationJointKemRawChallenge.preRaw_source setup codec checks ensureInit supplied decision
    work runtime count selected index chosen
  change simulateQ (kemAmbientImpl setup.baseImpl)
    (simulateQ (setup.kem.IND_CCA_preChallengeImpl chosen.2)
      (preRaw setup codec checks ensureInit supplied decision work runtime count selected index chosen.1)) = _ at same
  rw [same]
  rfl

/-- The real branch and the real stopped-source game differ by at most the ordinary ML-KEM correctness error. For each key pair, prephase context and challenger encapsulation, the two continuations agree whenever actual decapsulation recovers the encapsulated secret (`KemResume.post_source` with the agreement from `FunctionalDecapsulation`); a bad encapsulation is charged in full. The same single error event covers every repeated use of the challenge ciphertext. No perfect-correctness premise is used and no program is commuted. -/
theorem branchRaw_real_error (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    tvDist (branch setup codec checks ensureInit supplied decision work runtime count selected index true)
      (sourceReal setup codec checks ensureInit supplied decision work runtime count selected index) ≤
      correctnessError setup := by
  have point : ∀ (chosen : MlKem768PublicKey × KemSK) (context : Context KemSK A Bool count)
      (pair : MlKem768Ciphertext × MlKemSharedSecret),
      tvDist (do
          let uniform ← $ᵗ MlKemSharedSecret
          PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
            pair.1 (post setup count selected ⟨chosen.1, pair.1, context⟩ (if true then pair.2 else uniform)))
        (do
          let _ ← $ᵗ MlKemSharedSecret
          PqxdhRegistrationJointKemGame.decision <$> sourcePost setup count selected chosen
            ⟨chosen.1, pair.1, context⟩ pair.2) ≤
      (𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (do
          let recovered ← setup.kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal := by
    intro chosen context pair
    by_cases good : functional.result chosen.2 pair.1 = some pair.2
    · have agreement : setup.kem.decaps chosen.2 pair.1 = pure (some pair.2) :=
        (functional.exact chosen.2 pair.1).trans (congrArg pure good)
      have same := PqxdhRegistrationJointKemResume.post_source setup count selected chosen context pair.1 pair.2
        agreement
      simp only [↓reduceIte, same, tvDist_self]
      exact ENNReal.toReal_nonneg
    · have bad : (𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (do
          let recovered ← setup.kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2)))] {true}).toReal = 1 := by
        rw [functional.exact]
        simp [good, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
      rw [bad]
      exact tvDist_le_one _ _
  unfold branch sourceReal
  refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
    (fun pair => simulateQ (kemAmbientImpl setup.baseImpl)
      (PqxdhKemCorrectnessStopped.keyError setup.kem pair.1 pair.2))
    (fun result => result = true) ?_) (le_of_eq ?_)
  · intro chosen
    refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
      (fun _ => simulateQ (kemAmbientImpl setup.baseImpl)
        (PqxdhKemCorrectnessStopped.keyError setup.kem chosen.1 chosen.2))
      (fun result => result = true) ?_) (le_of_eq ?_)
    · intro context
      refine le_trans (PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind _ _ _
        (fun pair => simulateQ (kemAmbientImpl setup.baseImpl) (do
          let recovered ← setup.kem.decaps chosen.2 pair.1
          pure (decide (recovered ≠ some pair.2))))
        (fun result => result = true) ?_) (le_of_eq ?_)
      · intro pair
        rw [prEvent_eq_evalDist_singleton]
        exact point chosen context pair
      · simp only [PqxdhKemCorrectnessStopped.keyError, simulateQ_bind]
    · rw [bind_assoc, OracleComp.prEvent_bind_const]
  · rw [correctnessError, ← prEvent_eq_evalDist_singleton _ true,
      PqxdhKemCorrectnessStopped.error_keygen, simulateQ_bind]

/-- The real raw-ordinal game and its candidate replacement are within one ordinary one-key ML-KEM IND-CCA advantage plus one ordinary ML-KEM correctness error, both with coefficient one. -/
theorem advantageRaw_error (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (sourceReal setup codec checks ensureInit supplied decision work runtime count selected index).boolDistAdvantage
      (branch setup codec checks ensureInit supplied decision work runtime count selected index false) ≤
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied decision work runtime count selected index).toINDCCA +
        correctnessError setup := by
  have exactHop := oneKey_indCCAAdvantage_eq_branchDist setup.kem
    (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (adversary setup codec checks ensureInit supplied decision work runtime count selected index)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl setup.baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp setup.baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl setup.baseImpl))
  have hop : (branch setup codec checks ensureInit supplied decision work runtime count selected index true).boolDistAdvantage
      (branch setup codec checks ensureInit supplied decision work runtime count selected index false) =
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied decision work runtime count selected index).toINDCCA := by
    simpa only [oneKeyBranch, runtimeOfImpl_evalDist, branchRaw_source, ProbComp.boolDistAdvantage,
      MeasureTheory.Measure.boolDist, prEvent_eq_evalDist_singleton] using
      exactHop.symm
  have close : (sourceReal setup codec checks ensureInit supplied decision work runtime count selected index).boolDistAdvantage
      (branch setup codec checks ensureInit supplied decision work runtime count selected index true) ≤
      correctnessError setup := by
    rw [ProbComp.boolDistAdvantage_comm]
    refine le_trans ?_ (branchRaw_real_error setup functional codec checks ensureInit supplied decision work runtime
      count selected index)
    rw [ProbComp.boolDistAdvantage]
    simpa only [VCVioLegacy.evalDist_singleton_eq_probOutput] using abs_probOutput_toReal_sub_le_tvDist _ _
  have triangle := ProbComp.boolDistAdvantage_triangle
    (sourceReal setup codec checks ensureInit supplied decision work runtime count selected index)
    (branch setup codec checks ensureInit supplied decision work runtime count selected index true)
    (branch setup codec checks ensureInit supplied decision work runtime count selected index false)
  rw [hop] at triangle
  linarith

/-- The two raw-ordinal games are close: the absolute difference of their `true` probabilities is at most the ordinary IND-CCA advantage of the plain adversary plus the ordinary correctness error. The plain adversary has no proved query bills; `KemRawCertified.ideal_close` is the same bound for the proof-carrying adversary. -/
theorem ideal_close (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    |(𝒟[sourceReal setup codec checks ensureInit supplied decision work runtime count selected index] {true}).toReal -
      (𝒟[branch setup codec checks ensureInit supplied decision work runtime count selected index false] {true}).toReal| ≤
      setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (adversary setup codec checks ensureInit supplied decision work runtime count selected index).toINDCCA +
        correctnessError setup :=
  advantageRaw_error setup functional codec checks ensureInit supplied decision work runtime count selected index

/-- One-sided form of `ideal_close` for the plain adversary: the real raw-ordinal game wins with at most the probability of the KEM-ideal branch plus the IND-CCA advantage and the correctness error. Consumers that also need query bills use `KemRawCertified.real_le_ideal`. -/
theorem real_le_ideal (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[sourceReal setup codec checks ensureInit supplied decision work runtime count selected index] {true} ≤
      𝒟[branch setup codec checks ensureInit supplied decision work runtime count selected index false] {true} +
        ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
          (adversary setup codec checks ensureInit supplied decision work runtime count selected index).toINDCCA +
          correctnessError setup) :=
  (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage _ _).trans (add_le_add le_rfl
    (ENNReal.ofReal_le_ofReal (advantageRaw_error setup functional codec checks ensureInit supplied decision work
      runtime count selected index)))

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.correctnessError_eq_kemError' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.correctnessError_eq_kemError

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.branchRaw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.branchRaw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.branchRaw_real_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.branchRaw_real_error

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.advantageRaw_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.advantageRaw_error

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.ideal_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.ideal_close

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.real_le_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawGame.real_le_ideal
