-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineChain
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser
import BeaconcryptCore.Computational.PqxdhKemCorrectnessError
import BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix

/-!
# The anomaly term of the CE-12 headlines: predict-then-compare (CE-12 P1, design-v2 section 6)

CE-11b's `PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk` bounds the Beacon-side anomaly of a target on the record world with its ideal environment by `ctGuessByCca setup (anomalyGuesser …)`, the probability that an explicit guesser with a decapsulation oracle for the selected key predicts the ciphertext of a later encapsulation to that key. This module turns that guess into one ML-KEM IND-CCA advantage.

- `ptc kem guess` (the probe `PtcProbe`): the predict-then-compare one-key IND-CCA adversary. Phase 1 runs `guess` on the public key with the decapsulation oracle and, on a prediction `c`, decapsulates `c` before the challenge (allowed, no challenge exists yet). Phase 2 receives the challenge ciphertext `c*` and the candidate key `K_b` and outputs `c = c*` and the decapsulation result equals `some K_b`. Phase 2 makes no query.
- `ptc_bound`: `ctGuessByCca setup guess ≤ ofReal Adv^IND-CCA(ptc setup.kem guess) + ofReal (correctnessError setup) + 2^-256`, coefficient one, premise `FunctionalDecapsulation`. The proof follows design.md section 6: the advantage is the distance of the two fixed branches (`ptc_advantage`, `PqxdhKemIndCca.oneKey_indCCAAdvantage_eq_branchDist`); both branches are the joint draws `ptcDraws` (key generation, the guess with the decapsulation oracle, the encapsulation) followed by a branch-independent uniform candidate (`ptc_branch`, `ptc_branch_eval`); in the real branch a correct prediction wins unless the functional decapsulation of the challenge ciphertext is not the encapsulated key, whose probability over the joint draws is the correctness error, because the guess is drawn before the encapsulation (`ctGuess_draws`, `ptc_real_draws`, `ptc_correct_draws`); in the random branch the candidate is a fresh uniform 32-byte key, hit with probability at most `2^-256` (`ptc_random_le`).
- Query bounds: phase 1 makes at most one logical decapsulation query more than the guesser (`ptc_decapsulations`), phase 2 makes no query of any kind (`ptc_post`); for the anomaly guesser this is at most `budget.finish + 1` decapsulations (`beta_decapsulations`, from `anomalyGuesser_decapsulations`). The uniform and base-query bills of phase 1 are design-v2 section 9's `ptc_bills` (unit P2).
- `beta` (design-v2 section 2's `β_g`) and `anomaly_beta`: under `Phase1ReadBack`, `Phase2ReadBack` and `FunctionalDecapsulation`, the record-world anomaly of the target of `g` is at most `β_g`; `chain_beta` composes it with `PqxdhDeploymentHeadlineChain.chain_slots`.

No assumption or contract is added: the terms are an ML-KEM IND-CCA advantage of an explicit adversary, the ML-KEM correctness error (a definition) and `2^-256`.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret MlKemCCAOracleSpec OneKeyAdversary
  oneKeyBranchMain oneKeyPrefix oneKeyFinish IsMlKemLogicalDecapsulationQuery)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)

section Ptc
variable {ι : Type} {baseSpec : OracleSpec ι} {SK : Type}

/-- Predict, decapsulate the prediction before the challenge, then compare with the challenge. -/
def ptc (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    OneKeyAdversary kem where
  Context := Option (MlKem768Ciphertext × Option MlKemSharedSecret)
  preChallenge pk := do
    let predicted ← guess pk
    match predicted with
    | none => pure none
    | some c => do
        let k ← (query (spec := kem.IND_CCA_oracleSpec) (Sum.inr c) :
          OracleComp kem.IND_CCA_oracleSpec (Option MlKemSharedSecret))
        pure (some (c, k))
  postChallenge transcript kStar :=
    pure (match transcript.context with
      | some (c, some k) => decide (c = transcript.ciphertext ∧ k = kStar)
      | _ => false)

/-- The outcome of a fixed branch of `ptc` as a function of the joint draws. -/
def ptcOutcome (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (functional : FunctionalDecapsulation kem) (real : Bool)
    (draw : (MlKem768PublicKey × SK) × Option MlKem768Ciphertext × (MlKem768Ciphertext × MlKemSharedSecret))
    (candidate : MlKemSharedSecret) : Bool :=
  match draw.2.1.map fun c => (c, functional.result draw.1.2 c) with
  | some (c, some k) => decide (c = draw.2.2.1 ∧ k = if real then draw.2.2.2 else candidate)
  | _ => false

/-- The joint draws of both branches before the candidate. -/
def ptcDraws (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    OracleComp (unifSpec + baseSpec)
      ((MlKem768PublicKey × SK) × Option MlKem768Ciphertext × (MlKem768Ciphertext × MlKemSharedSecret)) := do
  let pair ← kem.keygen
  let predicted ← simulateQ (kem.IND_CCA_preChallengeImpl pair.2) (guess pair.1)
  let encapsulated ← kem.encaps pair.1
  pure (pair, predicted, encapsulated)

/-- `ptc`'s pre-challenge phase under the decapsulation oracle of a secret key, with functional decapsulation: the guess, then its prediction paired with the functional decapsulation result. -/
theorem ptc_pre (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (functional : FunctionalDecapsulation kem)
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext))
    (pk : MlKem768PublicKey) (sk : SK) :
    simulateQ (kem.IND_CCA_preChallengeImpl sk) ((ptc kem guess).preChallenge pk) =
      simulateQ (kem.IND_CCA_preChallengeImpl sk) (guess pk) >>= fun predicted =>
        pure (predicted.map fun c => (c, functional.result sk c)) := by
  unfold ptc
  dsimp only
  rw [simulateQ_bind]
  refine bind_congr fun predicted => ?_
  cases predicted with
  | none => simp
  | some c =>
      simp [simulateQ_query, PqxdhKemIndCca.indCCA_preChallengeImpl_decapsulation, functional.exact]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A fixed branch of `ptc`, with functional decapsulation: the joint draws (`ptcDraws`), the branch-independent uniform candidate, then `ptcOutcome`. -/
theorem ptc_branch (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (functional : FunctionalDecapsulation kem)
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext))
    (real : Bool) :
    oneKeyBranchMain kem runtime (ptc kem guess) real =
      ptcDraws kem guess >>= fun draw => runtime.liftProbComp ($ᵗ MlKemSharedSecret) >>= fun candidate =>
        pure (ptcOutcome kem functional real draw candidate) := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, ptcDraws, bind_assoc, pure_bind]
  refine bind_congr fun pair => ?_
  simp only [ptc_pre kem functional guess, bind_assoc, pure_bind]
  refine bind_congr fun predicted => ?_
  refine bind_congr fun encapsulated => ?_
  refine bind_congr fun candidate => ?_
  simp only [ptc, simulateQ_pure, ptcOutcome]

end Ptc

section Bound
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- A fixed branch of `ptc` under the ambient interpreter: the joint draws, then the uniform candidate, then the outcome. -/
theorem ptc_branch_eval (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext))
    (real : Bool) :
    simulateQ (kemAmbientImpl setup.baseImpl)
        (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) real) =
      simulateQ (kemAmbientImpl setup.baseImpl) (ptcDraws setup.kem guess) >>= fun draw =>
        ($ᵗ MlKemSharedSecret) >>= fun candidate => pure (ptcOutcome setup.kem functional real draw candidate) := by
  rw [ptc_branch setup.kem functional]
  simp only [simulateQ_bind, simulateQ_pure, PqxdhInitializerSecrecy.runtimeOfImpl_liftProbComp,
    PqxdhInitializerSecrecy.simulateQ_kemAmbient_liftProbComp]

/-- The ciphertext guess of `guess` is the probability, over the joint draws, that the guess is the encapsulation's ciphertext. -/
theorem ctGuess_draws (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca setup guess =
      𝒟[(fun draw => decide (draw.2.1 = some draw.2.2.1)) <$>
        simulateQ (kemAmbientImpl setup.baseImpl) (ptcDraws setup.kem guess)] {true} := by
  have program : (do
      let pair ← setup.kem.keygen
      let guessed ← simulateQ (setup.kem.IND_CCA_preChallengeImpl pair.2) (guess pair.1)
      let encapsulated ← setup.kem.encaps pair.1
      pure (decide (guessed = some encapsulated.1)) : OracleComp (unifSpec + baseSpec) Bool) =
      (fun draw => decide (draw.2.1 = some draw.2.2.1)) <$> ptcDraws setup.kem guess := by
    simp only [ptcDraws, map_bind, map_pure]
  unfold PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca
  rw [program, simulateQ_map]

/-- The real branch of `ptc` succeeds exactly when the prediction is the challenge ciphertext and its decapsulation is the encapsulated key. -/
theorem ptc_real_draws (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
        (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) true)]
          {true} =
      𝒟[(fun draw => ptcOutcome setup.kem functional true draw draw.2.2.2) <$>
        simulateQ (kemAmbientImpl setup.baseImpl) (ptcDraws setup.kem guess)] {true} := by
  rw [ptc_branch_eval setup functional, evalDist_apply_singleton, evalDist_apply_singleton, map_eq_bind_pure_comp]
  refine probOutput_bind_congr' _ _ fun draw => ?_
  have same : ∀ candidate, ptcOutcome setup.kem functional true draw candidate =
      ptcOutcome setup.kem functional true draw draw.2.2.2 := fun _ => rfl
  simp only [same, Function.comp_apply]
  rw [probOutput_bind_const]
  simp

set_option linter.deprecated false in
/-- The random branch of `ptc` succeeds with probability at most `2^-256`: its candidate is a fresh uniform 32-byte key drawn after everything the comparison reads. -/
theorem ptc_random_le (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
        (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) false)]
          {true} ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [ptc_branch_eval setup functional, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun draw _ => ?_
  rw [bind_pure_comp, probEvent_map]
  cases mapped : draw.2.1.map (fun c => (c, functional.result draw.1.2 c)) with
  | none =>
      have never : ∀ candidate, ptcOutcome setup.kem functional false draw candidate = false := fun candidate => by
        simp only [ptcOutcome, mapped]
      simp [Function.comp_def, never]
  | some found =>
      obtain ⟨c, key⟩ := found
      cases key with
      | none =>
          have never : ∀ candidate, ptcOutcome setup.kem functional false draw candidate = false :=
            fun candidate => by simp only [ptcOutcome, mapped]
          simp [Function.comp_def, never]
      | some k =>
          calc Pr[(fun hit => hit = true) ∘ fun candidate => ptcOutcome setup.kem functional false draw candidate |
                $ᵗ MlKemSharedSecret]
              ≤ Pr[fun candidate => candidate = k | $ᵗ MlKemSharedSecret] := by
                refine probEvent_mono fun candidate _ hit => ?_
                simp only [Function.comp_apply, ptcOutcome, mapped, Bool.false_eq_true, ite_false,
                  decide_eq_true_eq] at hit
                exact hit.2.symm
            _ = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
                rw [probEvent_eq_eq_probOutput, probOutput_uniformSample,
                  PqxdhExtractRomHiddenSuffix.secret_card]
                norm_num

set_option linter.deprecated false in
/-- The correctness error, read on the joint draws: the probability that the functional decapsulation of the encapsulation's ciphertext under the drawn secret key is not the encapsulated key is `correctnessError setup`. The guess between key generation and encapsulation does not change the joint law of the key pair and the encapsulation. -/
theorem ptc_correct_draws (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    𝒟[(fun draw => decide (functional.result draw.1.2 draw.2.2.1 ≠ some draw.2.2.2)) <$>
        simulateQ (kemAmbientImpl setup.baseImpl) (ptcDraws setup.kem guess)] {true} =
      ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  have finite : 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
      (PqxdhKemCorrectnessError.errorExperiment setup.kem)] {true} ≠ ⊤ := by
    rw [evalDist_apply_singleton]
    exact probOutput_ne_top
  rw [PqxdhRegistrationJointKemRawGame.correctnessError, ENNReal.ofReal_toReal finite, evalDist_apply_singleton,
    evalDist_apply_singleton, PqxdhKemCorrectnessError.error_probability setup.baseImpl setup.kem functional,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  have projected : Pr[PqxdhKemCorrectnessError.Bad setup.kem functional |
      simulateQ (kemAmbientImpl setup.baseImpl) (PqxdhKemCorrectnessError.sample setup.kem)] =
      Pr[PqxdhKemCorrectnessError.Bad setup.kem functional |
        (fun draw => (⟨draw.1.1, draw.1.2, draw.2.2.1, draw.2.2.2⟩ : PqxdhKemCorrectnessError.Sample KemSK)) <$>
          simulateQ (kemAmbientImpl setup.baseImpl) (ptcDraws setup.kem guess)] := by
    rw [← simulateQ_map]
    simp only [PqxdhKemCorrectnessError.sample, ptcDraws, map_bind, map_pure, simulateQ_bind, simulateQ_pure]
    refine probEvent_bind_congr' _ _ fun pair => ?_
    rw [probEvent_bind_const]
    simp
  rw [projected, probEvent_map]
  congr 1
  funext draw
  simp [PqxdhKemCorrectnessError.Bad]

/-- `ptc`'s advantage is the distance of its two fixed branches under the ambient interpreter (`PqxdhKemIndCca.oneKey_indCCAAdvantage_eq_branchDist`, coefficient one). -/
theorem ptc_advantage (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess).toINDCCA =
      |(𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
          (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) true)]
            {true}).toReal -
        (𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
          (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) false)]
            {true}).toReal| := by
  rw [PqxdhKemIndCca.oneKey_indCCAAdvantage_eq_branchDist setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (ptc setup.kem guess) (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_pure _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_bind _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_liftProbComp _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_noFail_bool _)]
  rfl

/-- `ptc_bound` (design-v2 section 6): the ciphertext guess of a guesser with decapsulation access is at most the IND-CCA advantage of the predict-then-compare adversary `ptc` plus the ML-KEM correctness error plus `2^-256`, each with coefficient one. Premise: `FunctionalDecapsulation`. -/
theorem ptc_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem)
    (guess : MlKem768PublicKey → OracleComp setup.kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) :
    PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca setup guess ≤
      ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (ptc setup.kem guess).toINDCCA) +
      ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) + (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  set real := 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
    (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) true)] {true}
    with hreal
  set random := 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
    (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess) false)] {true}
    with hrandom
  have guessed : PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca setup guess ≤
      real + ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
    rw [hreal, ctGuess_draws, ptc_real_draws setup functional, ← ptc_correct_draws setup functional guess]
    have bits : (fun draw : (MlKem768PublicKey × KemSK) × Option MlKem768Ciphertext ×
        (MlKem768Ciphertext × MlKemSharedSecret) => ptcOutcome setup.kem functional true draw draw.2.2.2) =
        fun draw => decide (ptcOutcome setup.kem functional true draw draw.2.2.2 = true) := by
      funext draw
      simp
    rw [bits]
    refine PqxdhDeploymentKemTwoSided.chance_le_add _ _ _ _ fun draw _ hit => ?_
    by_cases good : functional.result draw.1.2 draw.2.2.1 = some draw.2.2.2
    · left
      simp [ptcOutcome, hit, good]
    · exact Or.inr good
  have finiteReal : real ≠ ⊤ := by
    rw [hreal, evalDist_apply_singleton]
    exact probOutput_ne_top
  have finiteRandom : random ≠ ⊤ := by
    rw [hrandom, evalDist_apply_singleton]
    exact probOutput_ne_top
  have close : real ≤ random + ENNReal.ofReal (setup.kem.IND_CCA_Advantage
      (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess).toINDCCA) := by
    rw [ptc_advantage setup guess]
    exact PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs finiteReal finiteRandom le_rfl
  calc PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca setup guess
      ≤ real + ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) := guessed
    _ ≤ ((2 ^ 256 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (setup.kem.IND_CCA_Advantage
          (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (ptc setup.kem guess).toINDCCA)) +
        ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) :=
          add_le_add (close.trans (add_le_add (ptc_random_le setup functional guess) le_rfl)) le_rfl
    _ = _ := by ring

end Bound

/-! ### Query bounds -/

section Queries
variable {ι : Type} {baseSpec : OracleSpec ι} {SK : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Phase 1 of `ptc` makes at most one logical decapsulation query more than the guesser: the decapsulation of its prediction. -/
theorem ptc_decapsulations (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext)) (count : ℕ)
    (bound : ∀ pk, (guess pk).IsQueryBoundP IsMlKemLogicalDecapsulationQuery count) (pk : MlKem768PublicKey) :
    ((ptc kem guess).preChallenge pk).IsQueryBoundP IsMlKemLogicalDecapsulationQuery (count + 1) := by
  change (guess pk >>= fun predicted => _).IsQueryBoundP IsMlKemLogicalDecapsulationQuery (count + 1)
  apply isQueryBoundP_bind (bound pk)
  intro predicted _
  cases predicted with
  | none => exact isQueryBoundP_pure _ _ _
  | some c => simp [isQueryBoundP_map_iff, IsMlKemLogicalDecapsulationQuery]

/-- Phase 2 of `ptc` makes no query of any kind. -/
theorem ptc_post (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option MlKem768Ciphertext))
    (transcript : PqxdhKemIndCca.MlKemChallengeTranscript (ptc kem guess).Context) (kStar : MlKemSharedSecret)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    ((ptc kem guess).postChallenge transcript kStar).IsQueryBoundP predicate 0 :=
  isQueryBoundP_pure _ _ _

end Queries

/-! ### `β_g` -/

section Beta
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealTrace (Anomaly)
open PqxdhRecordLiftIdeal (chainView realChains)
open PqxdhDeploymentHeadlineChain (kemLoss slotLoss slotted)

/-- `β_g` (design-v2 section 2): the IND-CCA advantage of the predict-then-compare adversary built from the anomaly guesser of the target of `g` (`PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser` at identity index 0), plus the ML-KEM correctness error, plus `2^-256`. -/
noncomputable def beta (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) : ℝ≥0∞ :=
  ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route checks
        (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary)).toINDCCA) +
    ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) + (2 ^ 256 : ℝ≥0∞)⁻¹

open Classical in
/-- `anomaly_beta` (design-v2 sections 3 and 6): under `Phase1ReadBack`, `Phase2ReadBack` and `FunctionalDecapsulation`, the Beacon-side anomaly of the target of `g` on the record world with its ideal environment has probability at most `β_g` (`PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk`, then `ptc_bound`). -/
theorem anomaly_beta (setup : Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        Anomaly setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) value.2.1.2.transcript)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
        setup.serverKeyId bounds mode adversary] {true} ≤
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime :=
  (PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk setup codec route checks phase1 phase2 (Target.ofCE budget g)
    ensureInit 0 runtime setup.serverKeyId bounds mode adversary).trans (ptc_bound setup functional _)

/-- C1-C6 with the anomaly term bounded (design-v2 section 3, step C6, Beacon-capable claims, one-sided): the probability that the deployment experiment ends with the event and the claim designating `g` is at most the probability of `dec_g ∧ IS_g` on the record lift's view of the all-real chain world with the ideal environment of the target of `g`, plus `β_g`, `kemLoss` and `slotLoss`. -/
theorem chain_beta (setup : Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (event : Observed X → Bool) (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      𝒟[slotted setup codec budget event claim g <$>
        (chainView <$> realChains setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime)
          setup.serverKeyId bounds mode adversary)] {true} +
      beta setup codec route checks ensureInit bounds mode adversary budget g runtime +
      ENNReal.ofReal (kemLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) +
      ENNReal.ofReal (slotLoss setup codec checks route ensureInit bounds mode adversary budget event claim g runtime) :=
  (PqxdhDeploymentHeadlineChain.chain_slots setup functional codec checks route ensureInit phase1 phase2 correct bounds
    mode adversary budget respects event claim g runtime).trans (add_le_add (add_le_add (add_le_add le_rfl
      (anomaly_beta setup functional codec checks route ensureInit phase1 phase2 bounds mode adversary budget g
        runtime)) le_rfl) le_rfl)

/-- Phase 1 of `β_g`'s adversary makes at most `budget.finish + 1` logical decapsulation queries for an adversary that respects the budget (`PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser_decapsulations` and `ptc_decapsulations`); phase 2 makes none (`ptc_post`). -/
theorem beta_decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (pk : MlKem768PublicKey) :
    ((ptc setup.kem (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route checks (Target.ofCE budget g)
        ensureInit 0 runtime bounds mode adversary)).preChallenge pk).IsQueryBoundP IsMlKemLogicalDecapsulationQuery
      (budget.finish + 1) :=
  ptc_decapsulations setup.kem _ budget.finish (fun pk =>
    PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser_decapsulations setup codec route checks (Target.ofCE budget g)
      ensureInit 0 runtime bounds mode adversary budget respects pk) pk

end Beta

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_pre' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_pre

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_branch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_branch_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_branch_eval

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ctGuess_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ctGuess_draws

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_real_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_real_draws

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_random_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_random_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_correct_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_correct_draws

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_advantage

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_decapsulations

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_post' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.ptc_post

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.anomaly_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.anomaly_beta

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.chain_beta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.chain_beta

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.beta_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly.beta_decapsulations
