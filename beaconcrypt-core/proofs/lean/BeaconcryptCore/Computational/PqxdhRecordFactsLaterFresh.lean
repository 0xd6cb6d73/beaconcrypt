-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsLaterLor
import BeaconcryptCore.Computational.PqxdhRecordLiftFresh

/-! Fresh-message guessing after the complete E-only post phase. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas MeasureTheory
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftFlat PqxdhRecordLiftSwap
open PqxdhRecordLiftFresh PqxdhRecordLiftLaterWorlds PqxdhRecordFactsLaterFlat PqxdhRecordFactsLaterTargets
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhDeploymentLater (PostSpec)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Out R : Type}

/-- A fresh message on a caller-known handle remains excluded after the post phase. -/
theorem post_escaped (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (adversary : OracleComp PostSpec Out) (index : Nat)
    (ledger : Ledger) (state : NativeState n E) (escaped : FreshEscaped index (ledger, state))
    (result : Out × NativeState n E) (reached : result ∈ support (postRun modes replace setup codec route env adversary state)) :
    FreshEscaped index (ledger, result.2) := by
  obtain ⟨entry, present, known⟩ := escaped
  exact ⟨entry, present, postRun_known modes replace setup codec route env adversary state entry.handle known result reached⟩

/-- Append the E-only post phase to the byte-shift coupling, preserving the full native state on related runs and the caller-known exclusion on escaped runs. -/
theorem post_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (bounds : FreshBounds) (reveal : E → R) (second : X → R → OracleComp PostSpec Out)
    (claim : Out → Option (Nat × Pqxdh.Bytes)) (index length : Nat) (offsets : Fin length → Fin 256)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (firstResult secondResult : X × Ledger × NativeState n E)
    (related : SimRel (FreshRelated bounds index (extend offsets)) (FreshEscaped index) (FreshEscaped index)
      firstResult secondResult) :
    Swap (fun r₁ r₂ => hitAt claim index length (ctxView r₁) =
        shiftedHit bounds claim index length offsets (ctxView r₂))
      ((fun later => ((some (created, (later.1, firstResult.2.1), later.2.1.1), later.2.1.2), later.2.2)) <$>
        postRun modes zeros setup codec route env
          (second firstResult.1 (reveal firstResult.2.2.1.1)) firstResult.2.2)
      ((fun later => ((some (created, (later.1, secondResult.2.1), later.2.1.1), later.2.1.2), later.2.2)) <$>
        postRun modes zeros setup codec route env
          (second secondResult.1 (reveal secondResult.2.2.1.1)) secondResult.2.2) := by
  rcases firstResult with ⟨x₁, ledger₁, state₁⟩
  rcases secondResult with ⟨x₂, ledger₂, state₂⟩
  rcases related with ⟨hx, hstate, hledger, long⟩ | ⟨escaped₁, escaped₂⟩
  · dsimp only at hx hstate hledger
    subst x₂ state₂ ledger₂
    refine (Swap.refl (postRun modes zeros setup codec route env (second x₁ (reveal state₁.1.1)) state₁)
      (R := Eq) fun _ => rfl).map ?_
    rintro later _ rfl
    exact hitAt_shift bounds claim index length offsets later.1 ledger₁ later.2.1.1 _ _ _ long
  · refine Swap.escape _ _ fun a ha b hb => ?_
    rw [support_map] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact (hitAt_escaped claim index length a.1 ledger₁ a.2 _ _
      (post_escaped modes zeros setup codec route env _ index ledger₁ state₁ escaped₁ a ha)).trans
      (shiftedHit_escaped bounds claim index length offsets b.1 ledger₂ b.2 _ _
        (post_escaped modes zeros setup codec route env _ index ledger₂ state₂ escaped₂ b hb)).symm

/-- The run-phase byte-shift coupling survives the complete E-only post phase. The final adaptive index and byte claim are computed from the post output. -/
theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) (claim : Out → Option (Nat × Pqxdh.Bytes))
    (index length : Nat) (offsets : Fin length → Fin 256) :
    Swap (fun r₁ r₂ => hitAt claim index length (ctxView r₁) =
        shiftedHit bounds claim index length offsets (ctxView r₂))
      (laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros)
      (laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros) := by
  rw [laterCtxRun_flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨_ | ⟨created, initial⟩, control⟩, secret⟩
  · exact .pure _ _ (by simp [ctxView, viewOf, hitAt, shiftedHit, FreshHit])
  · refine (Swap.refl (install modes zeros setup codec route created control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env serverKid bounds)
      (fullImpl modes zeros setup codec route env serverKid bounds) (FreshRelated bounds index (extend offsets))
      (FreshEscaped index) (FreshEscaped index)
      (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
      (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
      (step_couple modes setup codec route env serverKid bounds index (extend offsets)) (asModeO mode first) _ _
      ⟨rfl, (shiftLedger_empty index (extend offsets)).symm, fun _ h => absurd h List.not_mem_nil⟩).bind ?_
    exact post_couple modes setup codec route env bounds reveal second claim index length offsets
      (PqxdhRegistrationJointServerBirth.encode created)

/-- Every fixed index-and-length hit has at most `256^{-min}` times the probability of that same adaptive claim; the whole post execution is included in both probabilities. -/
theorem hitAt_bound (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) (claim : Out → Option (Nat × Pqxdh.Bytes))
    (index length : Nat) :
    𝒟[(fun result => hitAt claim index length (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros] {true} ≤
      ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ * 𝒟[(fun result => keyAt claim index length (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros] {true} := by
  have same : ∀ offsets : Fin length → Fin 256,
      𝒟[(fun result => hitAt claim index length (ctxView result)) <$>
          laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros] {true} =
        𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$>
          laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros] {true} := fun offsets => by
    rw [(world_couple modes setup codec route env serverKid bounds mode reveal first second claim index length
      offsets).evalDist_map _ _ fun _ _ related => related]
  generalize laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros = work at same ⊢
  let _ : MeasurableSpace (Client n E Out × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E Out × CtxPrivate n) := ⟨fun _ => trivial⟩
  by_cases short : length < bounds.min
  case neg =>
    have long : bounds.min ≤ length := Nat.le_of_not_lt short
    have sum : ∑ offsets : Fin length → Fin 256,
        𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$> work] {true} ≤
          𝒟[(fun result => keyAt claim index length (ctxView result)) <$> work] {true} := by
      simp only [evalDist_map_true]
      rw [← measure_biUnion_finset]
      · exact measure_mono (Set.iUnion_subset fun offsets => Set.iUnion_subset fun _ =>
          fun result hit => shiftedHit_key bounds claim index length offsets (ctxView result) hit)
      · exact fun a _ b _ distinct => Set.disjoint_left.mpr fun result ha hb =>
          distinct (shiftedHit_disjoint bounds claim index length a b (ctxView result) ha hb)
      · exact fun _ _ => .of_discrete
    have card : ∑ _offsets : Fin length → Fin 256,
        𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} =
          ((256 ^ length : ℕ) : ℝ≥0∞) * 𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    apply (ENNReal.mul_le_iff_le_inv (by simp) (ENNReal.natCast_ne_top _)).mp
    refine le_trans (b := ((256 ^ length : ℕ) : ℝ≥0∞) *
      𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true}) ?_ ?_
    · gcongr
    · exact (card.symm.trans (Finset.sum_congr rfl fun offsets _ => same offsets)).le.trans sum
  case pos =>
    rw [same (fun _ => 0), evalDist_map_true]
    simp [shiftedHit, Nat.not_le_of_gt short]

/-- Adaptive fresh-message guessing in the zeroed later world is bounded by `2^{-min}`, without an index-selection loss: the disjoint adaptive claims provide their own probability weights. -/
theorem fresh_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) (claim : Out → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$>
        laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros] {true} ≤
      ((2 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  have bound := fun key : ℕ × ℕ =>
    hitAt_bound modes setup codec route env serverKid bounds mode reveal first second claim key.1 key.2
  generalize laterCtxRun setup codec route env serverKid bounds mode reveal first second modes zeros = work at bound ⊢
  let _ : MeasurableSpace (Client n E Out × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E Out × CtxPrivate n) := ⟨fun _ => trivial⟩
  simp only [evalDist_map_true] at bound ⊢
  calc 𝒟[work] {result | freshEvent claim (ctxView result) = true}
      ≤ 𝒟[work] (⋃ key : ℕ × ℕ, {result | hitAt claim key.1 key.2 (ctxView result) = true}) := by
        exact measure_mono fun result hit => Set.mem_iUnion.mpr (freshEvent_cover claim (ctxView result) hit)
    _ ≤ ∑' key : ℕ × ℕ, 𝒟[work] {result | hitAt claim key.1 key.2 (ctxView result) = true} :=
        measure_iUnion_le _
    _ ≤ ∑' key : ℕ × ℕ, ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] {result | keyAt claim key.1 key.2 (ctxView result) = true} := ENNReal.tsum_le_tsum bound
    _ = ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] (⋃ key : ℕ × ℕ, {result | keyAt claim key.1 key.2 (ctxView result) = true}) := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion]
        · exact fun a b distinct => Set.disjoint_left.mpr fun result ha hb =>
            distinct (keyAt_unique claim a b (ctxView result) ha hb)
        · exact fun _ => .of_discrete
    _ ≤ ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ * 1 := by
        gcongr
        exact (measure_mono (Set.subset_univ _)).trans (evalDist_apply_univ_le_one work)
    _ ≤ ((2 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := by
        simpa only [mul_one] using ENNReal.inv_le_inv.mpr (Nat.cast_le.mpr (Nat.pow_le_pow_left (show 2 ≤ 256 by decide) bounds.min))

/-- The frozen later fresh-message target, with a final adaptive index and bytes chosen after any E-only reveal and post adversary. No cryptographic, `Frame` or budget premise. -/
theorem later_idealRecords_fresh (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (n : Nat) :
    LaterFreshGuessStatement setup codec route serverKid bounds n := by
  intro E X Out R env reveal first second claim
  rw [PqxdhRecordFactsLaterLor.law_zeros setup codec route env serverKid bounds reveal first second _
    (freshEvent_hiding claim)]
  exact fresh_zeros (fun _ => .random) setup codec route env serverKid bounds .P reveal first second claim

end BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.post_escaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.post_escaped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.post_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.post_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.world_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.hitAt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.hitAt_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.fresh_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.fresh_zeros

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.later_idealRecords_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsLaterFresh.later_idealRecords_fresh
