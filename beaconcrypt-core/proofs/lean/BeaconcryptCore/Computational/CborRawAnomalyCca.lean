-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyGuesserRun
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly

/-! The actual raw pool predictor is an explicit pre-challenge ML-KEM CCA adversary. Its complete original raw transcript is independent of the later comparison ciphertext; predict-then-compare gives coefficient-one IND-CCA advantage, actual KEM correctness error and a 256-bit random-key comparison term. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyCca
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhKemIndCca (MlKem768Ciphertext MlKemSharedSecret)
open PqxdhInitializerSecrecy (kemAmbientImpl runtimeOfImpl)
open PqxdhDeploymentIdealAnomalyGuesser (ctGuessByCca ctGuessByCca_evalKem)
open PqxdhPrivateKemSource (evalKem)
open CborRawAnomalyGuesser (guesser)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- The actual raw challenger-draw hit is exactly the explicit native CBOR predictor's ciphertext-guess probability. -/
theorem hit_cca (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[CborRawAnomalyPool.hit setup wire parse checks target ensureInit runtime bounds mode adversary] {true} =
      ctGuessByCca setup (guesser setup wire parse checks target ensureInit runtime bounds mode adversary) := by
  let predictions : PqxdhLiveKemReservation.Pair KemSK → ProbComp (Option MlKem768Ciphertext) := fun pair =>
    PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>= fun others =>
      CborRawAnomalyPool.fixed setup wire parse checks target
        ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ ensureInit runtime bounds mode adversary
  have law : LazyOracleDiscard.LawEq
      (CborRawAnomalyPool.hit setup wire parse checks target ensureInit runtime bounds mode adversary)
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair => predictions pair >>= fun guessed =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed = some encapsulated.1))) := by
    unfold CborRawAnomalyPool.hit PqxdhDeploymentIdealParams.drawParams
    simp only [bind_assoc, pure_bind]
    apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
    intro pair
    simp only [predictions, bind_assoc]
    apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
    intro others
    have independent : ∀ value : MlKem768Ciphertext × MlKemSharedSecret,
        CborRawAnomalyPool.fixed setup wire parse checks target ⟨pair, others, value.1⟩ ensureInit runtime bounds mode adversary =
          CborRawAnomalyPool.fixed setup wire parse checks target
            ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ ensureInit runtime bounds mode adversary :=
      fun value => CborRawAnomalyPool.fixed_challenge setup wire parse checks target
        ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ value.1 ensureInit runtime bounds mode adversary
    simp only [independent]
    exact LazyOracleDiscard.lawEq_swap _ _ _
  have cca : LazyOracleDiscard.LawEq
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair => predictions pair >>= fun guessed =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed = some encapsulated.1)))
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        evalKem setup.baseImpl setup.kem pair.2 (guesser setup wire parse checks target ensureInit runtime bounds mode adversary pair.1) >>= fun guessed =>
          simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
            pure (decide (guessed = some encapsulated.1))) := by
    apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
    intro pair
    exact LazyOracleDiscard.LawEq.bind
      (CborRawAnomalyGuesserRun.pair_law setup wire parse checks target ensureInit runtime bounds mode adversary pair)
      (fun _ => LazyOracleDiscard.LawEq.refl _)
  rw [(law.trans cca).evalDist_eq, ctGuessByCca_evalKem]

noncomputable def beta (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) : ℝ≥0∞ :=
  ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (PqxdhDeploymentHeadlineAnomaly.ptc setup.kem
      (guesser setup wire parse checks target ensureInit runtime bounds mode adversary)).toINDCCA).toReal) +
    ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) + (2 ^ 256 : ℝ≥0∞)⁻¹

/-- The actual raw predictor has the explicit coefficient-one CCA/correctness/random-key bound. -/
theorem hit_beta (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    𝒟[CborRawAnomalyPool.hit setup wire parse checks target ensureInit runtime bounds mode adversary] {true} ≤
      beta setup wire parse checks target ensureInit runtime bounds mode adversary := by
  rw [hit_cca]
  exact PqxdhDeploymentHeadlineAnomaly.ptc_bound setup functional
    (guesser setup wire parse checks target ensureInit runtime bounds mode adversary)

end BeaconcryptCore.Computational.CborRawAnomalyCca

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyCca.hit_cca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyCca.hit_cca
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyCca.hit_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyCca.hit_beta
