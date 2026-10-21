-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGap
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly

/-!
# Collision terms of the CE-12 symbolic corollaries (CE-12 P2, design-v2 section 7.4)

The two collision terms that design-v2 section 7.4 introduces to bound how the public designation can move between symbolically eligible handles, as advantages of fixed reductions against existing games, with no distributional KEM or signature property assumed.

- `ε_inj` (`injTerm`, `identity_collision_game`): the probability that two distinct created owners of the experiment have equal identity public keys is at most the sum over the `qCreate + 1` identity indices of the joint-use weak-EUF advantage of the zero-query collision reduction `PqxdhDeploymentServerAuthInjective.collider` (the CE-game form of `owners_collision` and `collision_bound`, the second half of `PqxdhDeploymentServerAuthInjectiveGame.injective_bound`).
- `pairAdversary` (probe `PairProbe`) and `pair_cp_le`: the probability `CP` (`pairCollision`) that two independent encapsulations to a freshly generated ML-KEM key have equal ciphertexts is at most the IND-CCA advantage of the fixed encapsulate-and-compare adversary `pairAdversary` plus twice the ML-KEM correctness error plus `2^-256` (premise `FunctionalDecapsulation`). `pairAdversary` makes no pre-challenge query (`pair_pre`); after the challenge it encapsulates once to the challenge public key, its coins and base queries forwarded unchanged (`liftBase`, `post_lift`), and compares; it makes no decapsulation query (`pair_post_decapsulations`). The proof is the distance of its two fixed branches (`pair_advantage`): in the real branch a ciphertext collision gives equal keys unless one of the two encapsulations decapsulates incorrectly (`pair_real_draws`, `pair_first_error`, `pair_second_error`), in the random branch the candidate is a fresh uniform key (`pair_random_le`).
- `CtColl` (`CarriesTo`, `CtCollAt`, `CtCollEvent`, `ctCollEvent`, public): two distinct sessions carry one ciphertext (read with the Phase 2 reader from their first successful build responses) to the PQ key of an owner's first published bundle (read from their accept candidates with the source attached verification). `ctCollTerm` is its probability in the experiment.

Not proved here: design-v2's game-level step `ct_collision_game` (`𝒟[CtColl] ≤ (qCreate + 1)·C(qAccept, 2)·CP`, from the fresh encapsulation at the later accept); the symbolic corollaries that need it carry `ctCollTerm` explicitly, and `pair_cp_le` is the KEM-level half of `ε_ctcoll`. No new assumption or contract.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret MlKemCCAOracleSpec OneKeyAdversary
  oneKeyBranchMain oneKeyPrefix oneKeyFinish IsMlKemLogicalDecapsulationQuery)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)

/-! ### The encapsulate-and-compare adversary -/

section Pair
variable {ι : Type} {baseSpec : OracleSpec ι} {SK : Type}

/-- Base queries (public coins and the base oracle) on the IND-CCA query surface, unchanged. -/
def liftBase (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK)) :
    QueryImpl (unifSpec + baseSpec) (OracleComp kem.IND_CCA_oracleSpec) :=
  fun q => (query (spec := kem.IND_CCA_oracleSpec) (Sum.inl q) : OracleComp kem.IND_CCA_oracleSpec _)

/-- `pairAdversary` (design-v2 section 7.4, probe `PairProbe`): no pre-challenge query; after the challenge, one local encapsulation to the challenge public key (its coins and base queries forwarded unchanged), then the comparison of its ciphertext with the challenge ciphertext and of its key with the candidate key. It is fixed, efficient and independent of the deployment adversary. -/
def pairAdversary (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK)) : OneKeyAdversary kem where
  Context := Unit
  preChallenge _ := pure ()
  postChallenge transcript kStar := do
    let mine ← simulateQ (liftBase kem) (kem.encaps transcript.publicKey)
    pure (decide (mine.1 = transcript.ciphertext ∧ mine.2 = kStar))

/-- The joint draws of `pairAdversary`'s branches: key generation and two independent encapsulations to the key. -/
def pairDraws (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK)) :
    OracleComp (unifSpec + baseSpec)
      ((MlKem768PublicKey × SK) × (MlKem768Ciphertext × MlKemSharedSecret) × (MlKem768Ciphertext × MlKemSharedSecret)) := do
  let pair ← kem.keygen
  let first ← kem.encaps pair.1
  let second ← kem.encaps pair.1
  pure (pair, first, second)

/-- The outcome of a fixed branch of `pairAdversary`: the second encapsulation has the first one's ciphertext and the candidate key (the first one's key in the real branch). -/
def pairOutcome (real : Bool)
    (draw : (MlKem768PublicKey × SK) × (MlKem768Ciphertext × MlKemSharedSecret) ×
      (MlKem768Ciphertext × MlKemSharedSecret)) (candidate : MlKemSharedSecret) : Bool :=
  decide (draw.2.2.1 = draw.2.1.1 ∧ draw.2.2.2 = if real then draw.2.1.2 else candidate)

/-- The post-challenge decapsulation oracle forwards a lifted base computation unchanged. -/
theorem post_lift (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK)) (sk : SK)
    (cStar : MlKem768Ciphertext) {α : Type} (oa : OracleComp (unifSpec + baseSpec) α) :
    simulateQ (kem.IND_CCA_postChallengeImpl sk cStar) (simulateQ (liftBase kem) oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q f ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, ih]
      simp only [liftBase, KEMScheme.IND_CCA_postChallengeImpl]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A fixed branch of `pairAdversary`: key generation, the challenge encapsulation, the branch-independent uniform candidate, `pairAdversary`'s own encapsulation, then `pairOutcome`. -/
theorem pair_branch (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec))) (real : Bool) :
    oneKeyBranchMain kem runtime (pairAdversary kem) real =
      kem.keygen >>= fun pair => kem.encaps pair.1 >>= fun first =>
        runtime.liftProbComp ($ᵗ MlKemSharedSecret) >>= fun candidate => kem.encaps pair.1 >>= fun second =>
          pure (pairOutcome real (pair, first, second) candidate) := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, bind_assoc, pure_bind]
  refine bind_congr fun pair => ?_
  simp only [pairAdversary, simulateQ_pure, pure_bind]
  refine bind_congr fun first => ?_
  refine bind_congr fun candidate => ?_
  rw [simulateQ_bind, post_lift]
  refine bind_congr fun second => ?_
  simp only [simulateQ_pure, pairOutcome]

end Pair

/-! ### `pair_cp_le` -/

section PairBound
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- `CP` (design-v2 section 7.4): the probability that two independent encapsulations to a freshly generated ML-KEM key have equal ciphertexts, under the ambient interpreter of the setup. -/
noncomputable def pairCollision (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) : ℝ≥0∞ :=
  𝒟[(fun draw => decide (draw.2.2.1 = draw.2.1.1)) <$>
    simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem)] {true}

/-- A fixed branch of `pairAdversary` under the ambient interpreter. -/
theorem pair_branch_eval (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (real : Bool) :
    simulateQ (kemAmbientImpl setup.baseImpl)
        (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem) real) =
      simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun first =>
          ($ᵗ MlKemSharedSecret) >>= fun candidate =>
            simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun second =>
              pure (pairOutcome real (pair, first, second) candidate) := by
  rw [pair_branch setup.kem]
  simp only [simulateQ_bind, simulateQ_pure, PqxdhInitializerSecrecy.runtimeOfImpl_liftProbComp,
    PqxdhInitializerSecrecy.simulateQ_kemAmbient_liftProbComp]

/-- The joint draws under the ambient interpreter, in program order. -/
theorem pairDraws_eval (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) :
    simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem) =
      simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun first =>
          simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun second =>
            pure (pair, first, second) := by
  simp only [pairDraws, simulateQ_bind, simulateQ_pure]

/-- The real branch of `pairAdversary` succeeds exactly when the two encapsulations have equal ciphertexts and equal keys. -/
theorem pair_real_draws (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) :
    𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
        (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem) true)]
          {true} =
      𝒟[(fun draw => decide (draw.2.2.1 = draw.2.1.1 ∧ draw.2.2.2 = draw.2.1.2)) <$>
        simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem)] {true} := by
  rw [pair_branch_eval, pairDraws_eval]
  simp only [map_bind, map_pure]
  congr 1
  refine EvalDistEq.evalDist_eq (EvalDistEq.bind_right _ fun pair => EvalDistEq.bind_right _ fun first => ?_)
  have same : ∀ candidate second, pairOutcome true (pair, first, second) candidate =
      decide (second.1 = first.1 ∧ second.2 = first.2) := fun _ _ => rfl
  simp only [same]
  exact OracleComp.EvalDistEq.bind_const _ _

/-- The random branch of `pairAdversary` succeeds with probability at most `2^-256`: its candidate is a fresh uniform 32-byte key, independent of the second encapsulation. -/
theorem pair_random_le (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) :
    𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
        (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem) false)]
          {true} ≤ (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [pair_branch_eval, ← prEvent_eq_evalDist_singleton _ true]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun pair _ => ?_
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun first _ => ?_
  rw [(OracleComp.EvalDistEq.bind_bind_swap ($ᵗ MlKemSharedSecret)
    (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1)) _).prEvent_eq]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun second _ => ?_
  simp only [bind_assoc, pure_bind]
  calc Pr{let candidate ← $ᵗ MlKemSharedSecret}[pairOutcome false (pair, first, second) candidate = true]
      ≤ Pr{let candidate ← $ᵗ MlKemSharedSecret}[candidate = second.2] := by
        refine prEvent_mono_of_support _ _ _ fun candidate _ hit => ?_
        simp only [pairOutcome, Bool.false_eq_true, ite_false, decide_eq_true_eq] at hit
        exact hit.2.symm
    _ = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
        rw [SampleableType.prEvent_uniformSample_eq_singleton, PqxdhExtractRomHiddenSuffix.secret_card]
        norm_num

/-- The correctness error of the first encapsulation of the joint draws is the ML-KEM correctness error. -/
theorem pair_first_error (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem) :
    𝒟[(fun draw => decide (functional.result draw.1.2 draw.2.1.1 ≠ some draw.2.1.2)) <$>
        simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem)] {true} =
      ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  have finite : 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
      (PqxdhKemCorrectnessError.errorExperiment setup.kem)] {true} ≠ ⊤ := by
    rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  rw [PqxdhRegistrationJointKemRawGame.correctnessError, ENNReal.ofReal_toReal finite,
    ← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    PqxdhKemCorrectnessError.error_probability setup.baseImpl setup.kem functional, prEvent_map]
  have projected : Pr{let x ← simulateQ (kemAmbientImpl setup.baseImpl) (PqxdhKemCorrectnessError.sample setup.kem)}[(PqxdhKemCorrectnessError.Bad setup.kem functional) x] =
      Pr{let x ← ((fun draw : (MlKem768PublicKey × KemSK) × (MlKem768Ciphertext × MlKemSharedSecret) × (MlKem768Ciphertext × MlKemSharedSecret) =>
          (⟨draw.1.1, draw.1.2, draw.2.1.1, draw.2.1.2⟩ : PqxdhKemCorrectnessError.Sample KemSK)) <$>
          simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem))}[(PqxdhKemCorrectnessError.Bad setup.kem functional) x] := by
    rw [← simulateQ_map]
    simp only [PqxdhKemCorrectnessError.sample, pairDraws, map_bind, map_pure, simulateQ_bind, simulateQ_pure]
    refine EvalDistEq.prEvent_eq (EvalDistEq.bind_right _ fun pair => EvalDistEq.bind_right _ fun first => ?_) _
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  rw [projected, prEvent_map]
  refine prEvent_congr _ _ _ fun draw => ?_
  simp [PqxdhKemCorrectnessError.Bad]

/-- The correctness error of the second encapsulation of the joint draws is the ML-KEM correctness error: the two encapsulations are independent, so their order can be swapped. -/
theorem pair_second_error (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem) :
    𝒟[(fun draw => decide (functional.result draw.1.2 draw.2.2.1 ≠ some draw.2.2.2)) <$>
        simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem)] {true} =
      ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) := by
  have finite : 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
      (PqxdhKemCorrectnessError.errorExperiment setup.kem)] {true} ≠ ⊤ := by
    rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  rw [PqxdhRegistrationJointKemRawGame.correctnessError, ENNReal.ofReal_toReal finite,
    ← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    PqxdhKemCorrectnessError.error_probability setup.baseImpl setup.kem functional, prEvent_map]
  have projected : Pr{let x ← simulateQ (kemAmbientImpl setup.baseImpl) (PqxdhKemCorrectnessError.sample setup.kem)}[(PqxdhKemCorrectnessError.Bad setup.kem functional) x] =
      Pr{let x ← ((fun draw : (MlKem768PublicKey × KemSK) × (MlKem768Ciphertext × MlKemSharedSecret) × (MlKem768Ciphertext × MlKemSharedSecret) =>
          (⟨draw.1.1, draw.1.2, draw.2.2.1, draw.2.2.2⟩ : PqxdhKemCorrectnessError.Sample KemSK)) <$>
          simulateQ (kemAmbientImpl setup.baseImpl) (pairDraws setup.kem))}[(PqxdhKemCorrectnessError.Bad setup.kem functional) x] := by
    rw [← simulateQ_map]
    simp only [PqxdhKemCorrectnessError.sample, pairDraws, map_bind, map_pure, simulateQ_bind, simulateQ_pure]
    refine EvalDistEq.prEvent_eq (EvalDistEq.bind_right _ fun pair => ?_) _
    refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _).symm
    refine EvalDistEq.bind_right _ fun second => ?_
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  rw [projected, prEvent_map]
  refine prEvent_congr _ _ _ fun draw => ?_
  simp [PqxdhKemCorrectnessError.Bad]

/-- `pairAdversary`'s advantage is the distance of its two fixed branches under the ambient interpreter. -/
theorem pair_advantage (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) :
    setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem).toINDCCA =
      |(𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
          (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem) true)]
            {true}).toReal -
        (𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
          (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem)
            false)] {true}).toReal| := by
  rw [PqxdhKemIndCca.oneKey_indCCAAdvantage_eq_branchDist setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
    (pairAdversary setup.kem) (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_pure _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_bind _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_evalDist_liftProbComp _)
    (PqxdhInitializerSecrecy.runtimeOfImpl_noFail_bool _)]
  rfl

/-- `pair_cp_le` (design-v2 section 7.4): the probability `CP` that two independent encapsulations to a freshly generated key collide is at most the IND-CCA advantage of the fixed encapsulate-and-compare adversary `pairAdversary`, plus twice the ML-KEM correctness error, plus `2^-256`. In the real branch a ciphertext collision gives equal keys unless one of the two encapsulations is decapsulated incorrectly (`FunctionalDecapsulation` makes decapsulation a function); in the random branch the candidate is a fresh uniform key. No KEM min-entropy or collision property is assumed. Premise: `FunctionalDecapsulation`. -/
theorem pair_cp_le (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (functional : FunctionalDecapsulation setup.kem) :
    pairCollision setup ≤
      ENNReal.ofReal (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (pairAdversary setup.kem).toINDCCA) +
      2 * ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) + (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  set real := 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
    (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem) true)]
      {true} with hreal
  set random := 𝒟[simulateQ (kemAmbientImpl setup.baseImpl)
    (oneKeyBranchMain setup.kem (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem) false)]
      {true} with hrandom
  have collided : pairCollision setup ≤ real + (ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) +
      ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup)) := by
    rw [hreal, pair_real_draws]
    nth_rewrite 1 [← pair_first_error setup functional]
    rw [← pair_second_error setup functional]
    unfold pairCollision
    refine (PqxdhDeploymentHeadlineGap.chance_le_add_support _ _ _
      (fun draw => decide (functional.result draw.1.2 draw.2.1.1 ≠ some draw.2.1.2) ||
        decide (functional.result draw.1.2 draw.2.2.1 ≠ some draw.2.2.2)) fun draw _ hit => ?_).trans
      (add_le_add le_rfl (PqxdhDeploymentHeadlineGap.chance_le_add_support _ _ _ _ fun draw _ hit => by
        simpa using hit))
    simp only [decide_eq_true_eq] at hit
    by_cases first : functional.result draw.1.2 draw.2.1.1 = some draw.2.1.2
    · by_cases second : functional.result draw.1.2 draw.2.2.1 = some draw.2.2.2
      · left
        simp only [decide_eq_true_eq]
        refine ⟨hit, ?_⟩
        rw [hit, first, Option.some.injEq] at second
        exact second.symm
      · right
        simp [second]
    · right
      simp [first]
  have finiteReal : real ≠ ⊤ := by
    rw [hreal, ← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  have finiteRandom : random ≠ ⊤ := by
    rw [hrandom, ← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  have close : real ≤ random + ENNReal.ofReal (setup.kem.IND_CCA_Advantage
      (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem).toINDCCA) := by
    rw [pair_advantage setup]
    exact PqxdhDeploymentHeadlineChain.le_add_of_ofReal_abs finiteReal finiteRandom le_rfl
  calc pairCollision setup ≤ real + (ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) +
        ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup)) := collided
    _ ≤ ((2 ^ 256 : ℝ≥0∞)⁻¹ + ENNReal.ofReal (setup.kem.IND_CCA_Advantage
          (runtimeOfImpl (kemAmbientImpl setup.baseImpl)) (pairAdversary setup.kem).toINDCCA)) +
        (ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) +
          ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup)) :=
        add_le_add (close.trans (add_le_add (pair_random_le setup) le_rfl)) le_rfl
    _ = _ := by ring

end PairBound

/-! ### Query bounds of `pairAdversary` -/

section PairQueries
variable {ι : Type} {baseSpec : OracleSpec ι} {SK : Type}

/-- Phase 1 of `pairAdversary` makes no query of any kind. -/
theorem pair_pre (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK)) (pk : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    ((pairAdversary kem).preChallenge pk).IsQueryBoundP predicate 0 :=
  isQueryBoundP_pure _ _ _

/-- A lifted base computation makes no decapsulation query. -/
theorem liftBase_decapsulations (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK)) {α : Type}
    (oa : OracleComp (unifSpec + baseSpec) α) :
    (simulateQ (liftBase kem) oa).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind q f ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, liftBase]
      have first : (id <$> (query (spec := kem.IND_CCA_oracleSpec) (Sum.inl q) :
          OracleComp kem.IND_CCA_oracleSpec _)).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 := by
        simp [IsMlKemLogicalDecapsulationQuery]
      exact isQueryBoundP_bind (n := 0) (m := 0) first fun x _ => ih x

/-- Phase 2 of `pairAdversary` makes no decapsulation query: its only queries are the coins and base queries of one encapsulation to the challenge public key. -/
theorem pair_post_decapsulations (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (transcript : PqxdhKemIndCca.MlKemChallengeTranscript (pairAdversary kem).Context) (kStar : MlKemSharedSecret) :
    ((pairAdversary kem).postChallenge transcript kStar).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 := by
  change (simulateQ (liftBase kem) (kem.encaps transcript.publicKey) >>= fun mine =>
    pure (decide (mine.1 = transcript.ciphertext ∧ mine.2 = kStar))).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0
  exact isQueryBoundP_bind (n := 0) (m := 0) (liftBase_decapsulations kem _) fun _ _ => isQueryBoundP_pure _ _ _

end PairQueries

/-! ### The identity collision of the experiment (`ε_inj`) -/

section Identity
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)

/-- Two distinct created owners of the outcome have equal identity public keys (`PqxdhDeploymentServerAuthInjective.Collision` of the final native identity seeds). -/
def IdentityCollision (setup : Setup baseSpec KemSK)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A) :
    Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧
    PqxdhDeploymentServerAuthInjective.Collision setup.joint
      (PqxdhDeploymentServerAuthInjective.identities final.2.native)

/-- `ε_inj` (design-v2 section 2): the sum over the `qCreate + 1` identity indices of the joint-use weak-EUF advantage of the zero-query collision reduction `B^coll_t` (`PqxdhDeploymentServerAuthInjective.collider`). -/
noncomputable def injTerm (setup : Setup baseSpec KemSK) (budget : Budget) : ℝ≥0∞ :=
  ∑ target : Fin (budget.create + 1), PqxdhJointIdentity.advantage setup.joint
    (PqxdhDeploymentServerAuthInjective.collider setup.joint budget.create target)

/-- `identity_collision_game` (design-v2 section 7.4): in the experiment of a budget-respecting adversary (identity index 0), the probability that two distinct owners have equal identity public keys is at most `ε_inj`. It is the second half of `PqxdhDeploymentServerAuthInjectiveGame.injective_bound`, through CE-COMPILE, the constructor, `owners_collision` and `collision_bound`. Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. No distributional property of key generation is assumed: a collision of identity keys gives a forgery by signing correctness. -/
theorem identity_collision_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[(fun outcome => @decide (IdentityCollision setup outcome) (Classical.propDecidable _)) <$>
      (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true} ≤
      injTerm setup budget := by
  classical
  rw [UniformTargetSelection.chance_eq]
  refine le_trans ?_ (PqxdhDeploymentServerAuthInjective.collision_bound setup budget.create)
  rw [← PqxdhDeploymentCompileSecrecy.compile_full_game setup codec checks route ensureInit 0 phase1 phase2 bounds mode
    adversary runtime, prEvent_map]
  simp only [PqxdhRegistrationJointInitializedSchedule.native, PqxdhLiveServerConstruction.construct, StateT.run]
  rw [bind_assoc (ensureInit runtime)]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun ready _ => ?_
  cases ready.1 with
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [pure_bind]
      refine le_of_eq_of_le ((OracleComp.prEvent_eq_zero_iff _ _).mpr ?_) zero_le
      intro outcome member
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      simp [PqxdhDeploymentCompileSecrecy.mergeFull, IdentityCollision]
  | true =>
      simp only [ite_true, bind_map_left]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun seed _ => ?_
      rw [prEvent_map]
      refine le_of_eq_of_le (prEvent_congr_of_support _ _ _ fun result _ => ?_)
        (PqxdhDeploymentServerAuthInjective.owners_collision setup codec checks seed
          (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) (budget.create + 1)
          (PqxdhDeploymentServerAuthInjectiveGame.compiled_creates setup codec route bounds mode adversary budget
            respects) _ rfl)
      simp only [PqxdhDeploymentCompileSecrecy.mergeFull, Option.map_some, IdentityCollision,
        Option.some.injEq]
      constructor
      · rintro ⟨_, _, _, equal, collision⟩
        cases equal
        simpa [PqxdhDeploymentServerAuthInjectiveGame.identities_merge] using collision
      · intro collision
        exact ⟨_, _, _, rfl, by simpa [PqxdhDeploymentServerAuthInjectiveGame.identities_merge] using collision⟩

end Identity

/-! ### The public ciphertext-collision event (`CtColl`) -/

section Ciphertext
variable {Reader Response X : Type}
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentTranscript (buildOf acceptOf bundleOf candidateOf acceptedKeys publishedPq)

/-- Session `session` carries the ciphertext `ciphertext` to the PQ key `pqKey`: its first successful build response reads back that ciphertext with the Phase 2 reader, and its accept bytes give a candidate that the source attached verification accepts with a key tuple carrying `pqKey`. It is `PqxdhDeploymentTranscript.Linked` without the Server-identity conjunct. -/
def CarriesTo (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (session : Nat) :
    Prop :=
  ∃ response accepted keys, buildOf transcript session = some response ∧
    (codec.read2 response.serialized).bind codec.ciphertext = some ciphertext ∧
    (acceptOf transcript session).bind (candidateOf codec) = some accepted ∧
    acceptedKeys crypto accepted = some keys ∧ keys.2.pqKey = pqKey

/-- `CtCollAt k i j` (design-v2 section 7.4): two distinct sessions `i < j` carry one ciphertext to the PQ key that owner `k`'s first published bundle carries. -/
def CtCollAt (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (transcript : List Entry) (k i j : Nat) : Prop :=
  i < j ∧ ∃ ciphertext published pqKey, (bundleOf transcript k).bind (candidateOf codec) = some published ∧
    publishedPq published = some pqKey ∧ CarriesTo crypto codec transcript ciphertext pqKey i ∧
    CarriesTo crypto codec transcript ciphertext pqKey j

/-- `CtColl` on the observation: two distinct sessions carry one ciphertext to an owner's published PQ key. -/
def CtCollEvent (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (observed : Observed X) : Prop :=
  ∃ k i j, CtCollAt crypto codec observed.2.1.transcript k i j

open Classical in
/-- `CtCollEvent` as a Boolean of the observation. -/
noncomputable def ctCollEvent (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (observed : Observed X) : Bool :=
  decide (CtCollEvent crypto codec observed)

end Ciphertext

section CiphertextTerm
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)

/-- The explicit public ciphertext-collision term: the probability that the experiment ends with `CtCollEvent`. Design-v2 section 7.4's `ct_collision_game` would bound it by `ε_ctcoll = (qCreate + 1)·C(qAccept, 2)·(Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)` through `pair_cp_le`; that game-level step is not proved here. -/
noncomputable def ctCollTerm (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (runtime : A) : ℝ≥0∞ :=
  𝒟[(fun outcome => PqxdhDeploymentKemTransfer.happens (ctCollEvent setup.source.crypto codec) outcome) <$>
    (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit 0 bounds mode adversary).run runtime] {true}

end CiphertextTerm

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.post_lift' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.post_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_branch

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_branch_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_branch_eval

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pairDraws_eval' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pairDraws_eval

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_real_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_real_draws

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_random_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_random_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_first_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_first_error

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_second_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_second_error

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_advantage

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_cp_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_cp_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_pre' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_pre

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.liftBase_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.liftBase_decapsulations

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_post_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.pair_post_decapsulations

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.identity_collision_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision.identity_collision_game
