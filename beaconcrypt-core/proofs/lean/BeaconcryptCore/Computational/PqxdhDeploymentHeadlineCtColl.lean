-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtTrace
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineBills

/-!
# `ct_collision_game` and `ε_ctcoll` (CE-12 P2b, design-v2 section 7.4)

The game-level step of design-v2 section 7.4, which turns the explicit public term `ctCollTerm` of the CE-12 symbolic corollaries (`PqxdhDeploymentHeadlineCollision`) into the advantage of a fixed reduction.

- `ct_collision_game`: in the common deployment experiment of a budget-respecting adversary (Server identity index 0), `ctCollTerm ≤ qCreate · C(qAccept, 2) · CP`, where `CP = pairCollision setup` is the probability that two independent encapsulations to a freshly generated ML-KEM key have equal ciphertexts. The proof forgets the ghost of the instrumented experiment (`PqxdhDeploymentHeadlineCtGhost.game_ghost`), bounds the indicator of the transcript event by the sum of the indicators of the ghost collisions of the triples `k < qCreate`, `i < j < qAccept` (`PqxdhDeploymentHeadlineCtTrace.ctColl_triple`), and bounds each triple by `CP` (`triple_expect`, from `PqxdhDeploymentHeadlineCtGhost.triple_le`); `sum_pairs` and `sum_triples` count the `qCreate · C(qAccept, 2)` triples.
- `ctCollEps` (`ε_ctcoll`) and `ct_coll_le`: with `pair_cp_le` (premise `FunctionalDecapsulation`), `ctCollTerm ≤ qCreate · C(qAccept, 2) · (Adv^IND-CCA(pairAdversary) + 2δ_corr + 2^-256)`. `ct_coll_billed` adds the bill of `pairAdversary` (`PqxdhDeploymentHeadlineBills.pair_bills`, from `KemBound`). `ctCollEps_le_design` compares with design-v2's form, which counts `qCreate + 1` owners: the owners whose keys a collision can use are created owners, at most `qCreate` of them, since the Server holds no KEM key.

Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget; `FunctionalDecapsulation` for `ε_ctcoll`; `KemBound` for the bill. No KEM min-entropy or collision property is assumed, and no other assumption or contract is used. `ctGapTerm` stays explicit (D-ct, deferred).
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentHeadlineCtGhost (gameG forget TripleColl)
open PqxdhDeploymentHeadlineCollision (ctCollTerm ctCollEvent pairCollision pairAdversary)
open PqxdhInitializerSecrecy (runtimeOfImpl kemAmbientImpl)
open OracleComp.ProgramLogic (wp)

/-! ### Counting the triples -/

/-- The number of ordered pairs `i < j` below `n` is `C(n, 2)`. -/
theorem sum_pairs (n : Nat) (value : ℝ≥0∞) :
    ∑ j ∈ Finset.range n, ∑ _i ∈ Finset.range j, value = (n.choose 2 : ℝ≥0∞) * value := by
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.sum_mul, ← Nat.cast_sum, Finset.sum_range_id, Nat.choose_two_right]

/-- The number of triples of an owner index below `owners` and attempts `i < j` below `attempts`. -/
theorem sum_triples (owners attempts : Nat) (value : ℝ≥0∞) :
    ∑ _k ∈ Finset.range owners, ∑ j ∈ Finset.range attempts, ∑ _i ∈ Finset.range j, value =
      ((owners * attempts.choose 2 : Nat) : ℝ≥0∞) * value := by
  rw [Finset.sum_congr rfl fun _ _ => sum_pairs attempts value, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_mul, mul_assoc]

/-! ### `ct_collision_game` -/

section Game
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The per-triple bound of `PqxdhDeploymentHeadlineCtGhost.triple_le` as an expectation of the triple's indicator. -/
theorem triple_expect (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (k i j : Nat)
    (order : i < j) :
    wp ((gameG setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime)
      (fun outcome => @ite _ (TripleColl k i j outcome) (Classical.propDecidable _) 1 0) ≤ pairCollision setup := by
  have bound := PqxdhDeploymentHeadlineCtGhost.triple_le setup codec checks route ensureInit identityIndex bounds mode
    adversary runtime k i j order
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map,
    OracleComp.ProgramLogic.prEvent_eq_wp_indicator] at bound
  refine le_trans (le_of_eq ?_) bound
  congr 1
  funext outcome
  rcases Classical.em (TripleColl k i j outcome) with holds | fails
  · simp [holds]
  · simp [fails]

/-- `ct_collision_game` (design-v2 section 7.4): in the common deployment experiment of a budget-respecting adversary (Server identity index 0), the probability that two distinct sessions carry one ciphertext to the PQ key of an owner's first published bundle (`ctCollTerm`, the public event `CtCollEvent`) is at most `qCreate · C(qAccept, 2) · CP`, where `CP = pairCollision setup` is the probability that two independent encapsulations to a freshly generated ML-KEM key have equal ciphertexts. Each transcript collision is the ghost collision of a triple of an owner `k < qCreate` and raw accept attempts `i < j < qAccept` (`PqxdhDeploymentHeadlineCtTrace.ctColl_triple`), and each triple has probability at most `CP` (`PqxdhDeploymentHeadlineCtGhost.triple_le`): at the later of owner `k`'s key generation and attempt `i`'s encapsulation, and again at attempt `j`'s encapsulation, the draw is fresh while everything the collision compares it with is fixed, so the adversary's adaptivity costs nothing. Premises: the approved Phase 1 and Phase 2 read-back contracts and the budget. No KEM min-entropy or collision property is assumed. -/
theorem ct_collision_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime ≤
      ((budget.create * budget.accept.choose 2 : Nat) : ℝ≥0∞) * pairCollision setup := by
  classical
  unfold ctCollTerm
  rw [PqxdhDeploymentHeadlineCtGhost.game_ghost, Functor.map_map, ← prEvent_eq_evalDist_singleton _ true,
    prEvent_map, OracleComp.ProgramLogic.prEvent_eq_wp_indicator,
    ← sum_triples]
  set run := (gameG setup codec checks route ensureInit 0 bounds mode adversary).run runtime with runEq
  calc wp run (fun outcome => if ((fun hit => hit = true) ∘ (PqxdhDeploymentKemTransfer.happens
          (ctCollEvent setup.source.crypto codec) ∘ forget)) outcome then 1 else 0)
      ≤ wp run (fun outcome => ∑ k ∈ Finset.range budget.create, ∑ j ∈ Finset.range budget.accept,
          ∑ i ∈ Finset.range j, @ite _ (TripleColl k i j outcome) (Classical.propDecidable _) 1 0) := by
        refine OracleComp.ProgramLogic.wp_mono_of_support _ fun outcome member => ?_
        by_cases event : ((fun hit => hit = true) ∘ (PqxdhDeploymentKemTransfer.happens
            (ctCollEvent setup.source.crypto codec) ∘ forget)) outcome
        · simp only [event, ite_true]
          obtain ⟨k, kBound, j, jBound, i, iBound, triple⟩ := PqxdhDeploymentHeadlineCtTrace.ctColl_triple setup codec
            checks route ensureInit 0 phase1 phase2 bounds mode adversary budget respects runtime outcome member event
          calc (1 : ℝ≥0∞) = @ite _ (TripleColl k i j outcome) (Classical.propDecidable _) 1 0 := by simp [triple]
            _ ≤ ∑ i' ∈ Finset.range j, @ite _ (TripleColl k i' j outcome) (Classical.propDecidable _) 1 0 :=
              Finset.single_le_sum (f := fun i' => @ite _ (TripleColl k i' j outcome) (Classical.propDecidable _) 1 0)
                (fun _ _ => zero_le) (Finset.mem_range.mpr iBound)
            _ ≤ ∑ j' ∈ Finset.range budget.accept, ∑ i' ∈ Finset.range j',
                @ite _ (TripleColl k i' j' outcome) (Classical.propDecidable _) 1 0 :=
              Finset.single_le_sum (f := fun j' => ∑ i' ∈ Finset.range j',
                @ite _ (TripleColl k i' j' outcome) (Classical.propDecidable _) 1 0) (fun _ _ => zero_le)
                (Finset.mem_range.mpr jBound)
            _ ≤ ∑ k' ∈ Finset.range budget.create, ∑ j' ∈ Finset.range budget.accept, ∑ i' ∈ Finset.range j',
                @ite _ (TripleColl k' i' j' outcome) (Classical.propDecidable _) 1 0 :=
              Finset.single_le_sum (f := fun k' => ∑ j' ∈ Finset.range budget.accept, ∑ i' ∈ Finset.range j',
                @ite _ (TripleColl k' i' j' outcome) (Classical.propDecidable _) 1 0) (fun _ _ => zero_le)
                (Finset.mem_range.mpr kBound)
        · simp only [event, ite_false]
          exact zero_le
    _ = ∑ k ∈ Finset.range budget.create, ∑ j ∈ Finset.range budget.accept, ∑ i ∈ Finset.range j,
          wp run (fun outcome => @ite _ (TripleColl k i j outcome) (Classical.propDecidable _) 1 0) := by
        rw [OracleComp.ProgramLogic.wp_finsetSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [OracleComp.ProgramLogic.wp_finsetSum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [OracleComp.ProgramLogic.wp_finsetSum]
    _ ≤ ∑ _k ∈ Finset.range budget.create, ∑ j ∈ Finset.range budget.accept, ∑ _i ∈ Finset.range j,
          pairCollision setup := by
        refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i member => ?_
        exact triple_expect setup codec checks route ensureInit 0 bounds mode adversary runtime k i j
          (Finset.mem_range.mp member)

end Game


/-! ### `ε_ctcoll` -/

section Closed
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- `ε_ctcoll` (design-v2 section 2, with `qCreate` owners instead of `qCreate + 1`): `qCreate · C(qAccept, 2)` times the IND-CCA advantage of the fixed encapsulate-and-compare adversary `pairAdversary` plus twice the ML-KEM correctness error plus `2^-256`. -/
noncomputable def ctCollEps (setup : Setup baseSpec KemSK) (budget : Budget) : ℝ≥0∞ :=
  ((budget.create * budget.accept.choose 2 : Nat) : ℝ≥0∞) *
    (ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
      (pairAdversary setup.kem).toINDCCA).toReal) +
      2 * ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) + (2 ^ 256 : ℝ≥0∞)⁻¹)

/-- `ct_coll_le`: the explicit term `ctCollTerm` of the CE-12 symbolic corollaries is at most `ε_ctcoll`, by `ct_collision_game` and `pair_cp_le` (`PqxdhDeploymentHeadlineCollision`). Premises: the approved Phase 1 and Phase 2 read-back contracts, `FunctionalDecapsulation` (the premise of `pair_cp_le`) and the budget. -/
theorem ct_coll_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime ≤ ctCollEps setup budget :=
  (ct_collision_game setup codec checks route ensureInit phase1 phase2 bounds mode adversary budget respects runtime).trans
    (mul_le_mul' le_rfl (PqxdhDeploymentHeadlineCollision.pair_cp_le setup functional))

/-- `ε_ctcoll` is at most design-v2's form, which counts `qCreate + 1` owners. -/
theorem ctCollEps_le_design (setup : Setup baseSpec KemSK) (budget : Budget) :
    ctCollEps setup budget ≤ (((budget.create + 1) * budget.accept.choose 2 : Nat) : ℝ≥0∞) *
      (ENNReal.ofReal ((setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (pairAdversary setup.kem).toINDCCA).toReal) +
        2 * ENNReal.ofReal (PqxdhRegistrationJointKemRawGame.correctnessError setup) + (2 ^ 256 : ℝ≥0∞)⁻¹) :=
  mul_le_mul' (Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.le_succ _))) le_rfl

/-- `ct_coll_le` with the bill of its reduction: `ctCollTerm ≤ ε_ctcoll`, and `pairAdversary` makes no query before the challenge and, after it, only the uniform and base queries of one encapsulation (`PqxdhDeploymentHeadlineBills.pair_bills`, from `KemBound`). -/
theorem ct_coll_billed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    ctCollTerm setup codec checks route ensureInit bounds mode adversary runtime ≤ ctCollEps setup budget ∧
      (pairAdversary setup.kem).MakesAtMostQueries 0 0 0 caps.encapsUniform caps.encapsBase 0 :=
  ⟨ct_coll_le setup codec checks route ensureInit phase1 phase2 functional bounds mode adversary budget respects runtime,
    PqxdhDeploymentHeadlineBills.pair_bills setup caps bounded⟩

end Closed

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.sum_pairs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.sum_pairs

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.sum_triples' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.sum_triples

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.triple_expect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.triple_expect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ct_collision_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ct_collision_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ct_coll_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ct_coll_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ctCollEps_le_design' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ctCollEps_le_design

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ct_coll_billed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtColl.ct_coll_billed
