import BeaconcryptCore.Computational.PqxdhServerAuthPublicationRandom

/-! Ordinary IND$ reductions for the actual pre-raw publication-reference observer. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy
open CtxRomAuth AdaptiveCtxReceive PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open PqxdhServerAuthSourceCosts PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh
variable {ι KemSK Reader WireResponse : Type} {baseSpec : OracleSpec ι}

/-- The ordinary prefix-validation distinguisher is constructed from the exact reference/cutoff decision. -/
noncomputable def validation (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (H : Nat) :=
  AdaptiveCtxPrefixValidation.validationReduction decode setup.source.crypto
    (PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode) H

/-- The ordinary ciphertext-view distinguisher uses the same complete reference/cutoff decision. -/
noncomputable def view (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1)) (decode : RawDecoder) :=
  AdaptiveCtxPrivacyGuard.viewReduction decode
    (PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode)

set_option linter.deprecated false in
/-- No selected raw is issued, so the existing ordinary privacy comparison has no integrity or raw-alias term. The only statistical terms are the prefix-validation allowance and the unconditional tag guess. -/
theorem canonical_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (H : Nat)
    (hashBound : (PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode).IsQueryBoundP
      AdaptiveCtxQueryBounds.SourceHash H) :
    Pr[fun answer => answer = true | AdaptiveCtxPrivacyGuard.canonicalView decode setup.source.crypto
      (PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode)] ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage setup.source.crypto
        (validation setup codec checks adversary Q j decode H)) +
      (H : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage setup.source.crypto
        (view setup codec checks adversary Q j decode)) + ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ := by
  let work := PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode
  have sealBound : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 1 :=
    PqxdhServerAuthPublicationRandom.decision_budget setup codec checks adversary Q j decode _ _ _
      (PqxdhServerAuthPublicationRandom.source_seal setup codec checks adversary Q j)
  let fallback : ModifiedNonceAeadForgery :=
    ⟨List.Vector.replicate 12 0, [], ⟨[], List.replicate 16 0, by simp⟩⟩
  have privacy := AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound decode setup.source.crypto
    fallback work H 1 0 hashBound sealBound
    (PqxdhServerAuthPublicationRandom.decision_no_raw setup codec checks adversary Q j decode) (by norm_num)
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Nat.cast_zero, ENNReal.zero_div, add_zero] at privacy
  have comparison := ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage
    (AdaptiveCtxPrivacyGuard.canonicalView decode setup.source.crypto work)
    (AdaptiveCtxPrivacyGuard.randomView decode work)
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput] at comparison
  exact (comparison.trans (add_le_add
    (PqxdhServerAuthPublicationRandom.random_bound setup codec checks adversary Q j decode) privacy)).trans
    (le_of_eq (by simp only [validation, view, work]; ac_rfl))

/-- The exact ordinary privacy loss retains both constructed IND$ advantages, prefix validation, and the unconditional guessed tag. -/
noncomputable def lossENN (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (H : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage setup.source.crypto
    (validation setup codec checks adversary Q j decode H)) +
  (H : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹ +
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage setup.source.crypto
    (view setup codec checks adversary Q j decode)) + ((2 ^ 128 : Nat) : ℝ≥0∞)⁻¹

/-- Real-valued form for the enclosing finite source/key-schedule sum. -/
noncomputable def loss (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (H : Nat) : ℝ :=
  (lossENN setup codec checks adversary Q j decode H).toReal

/-- Both ordinary advantages and the explicit point-mass terms are finite, so real conversion loses no infinite mass. -/
theorem loss_finite (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (decode : RawDecoder) (H : Nat) :
    lossENN setup codec checks adversary Q j decode H ≠ ⊤ := by
  simp only [lossENN, ENNReal.add_ne_top]
  exact ⟨⟨⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top (by simp) (by norm_num)⟩,
    ENNReal.ofReal_ne_top⟩, by norm_num⟩

set_option linter.deprecated false in
/-- The exact ordinary real/canonical reference probability is bounded with the hash certificate derived from the complete source control and samplers. -/
theorem source_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (adversary : Adversary)
    (qCoin Q qHash qH : Nat)
    (coins : ∀ input, (adversary input).IsQueryBoundP IsAuthCoin qCoin)
    (accepts : ∀ input, (adversary input).IsQueryBoundP IsAcceptQuery Q)
    (hashes : ∀ input, (adversary input).IsQueryBoundP IsHashQuery qHash)
    (rom : ∀ input, (adversary input).IsQueryBoundP IsRomQuery qH)
    (j : Fin (Q + 1)) (decode : RawDecoder) :
    (Pr[fun answer => answer = true | AdaptiveCtxPrivacyGuard.canonicalView decode setup.source.crypto
      (PqxdhServerAuthPublicationRandom.decision setup codec checks adversary Q j decode)]).toReal ≤
      loss setup codec checks adversary Q j decode (entryReductionBudget caps qCoin Q qHash qH + 76) := by
  exact ENNReal.toReal_mono (loss_finite setup codec checks adversary Q j decode _)
    (canonical_bound setup codec checks adversary Q j decode _
      (PqxdhServerAuthPublicationRandom.decision_bills setup codec checks caps bounded adversary
        qCoin Q qHash qH coins accepts hashes rom j decode).2.1)

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy.canonical_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy.canonical_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy.loss_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy.loss_finite
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacy.source_bound
