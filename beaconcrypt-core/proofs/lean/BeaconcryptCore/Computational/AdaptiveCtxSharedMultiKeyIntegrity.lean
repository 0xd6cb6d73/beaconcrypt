import BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection
import BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity

/-!
Adjacent integrity hybrids change exactly one original key mode inside the same sampled family and common-cache experiment. After constructing each adjacent ordinary reduction, the finite hybrid inequality sums the displayed validation IND$, twice the indexed INT-CTXT advantages, and the secret-prefix/commitment terms. This does not assert an all-key ciphertext-randomization or evolving-protocol result.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation AdaptiveCtxReceive
open AdaptiveCtxSharedKeySelection AdaptiveCtxSharedModeBounds RawKeyPartition AdaptiveCtxQueryBounds
open AdaptiveRawMultiKeyIntegrity (realAt otherReal hybrid_before hybrid_after first_flags final_flags)

noncomputable def clientReduction {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) : OracleComp ReceiveSpec Bool :=
  AdaptiveCtxSharedModePreparation.decisionClient (AdaptiveCtxSharedModePreparation.independentSetup count ())
    (otherReal target) (fun other => decode (target.succAbove other)) c
    (fun _ => simulateQ (select target) client)

noncomputable def validationReduction {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) (qHash : Nat) :=
  AdaptiveCtxPrefixValidation.validationReduction (decode target) c (clientReduction target decode c client) qHash

noncomputable def forgeryReduction {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (attempt : Nat) :=
  AdaptiveRawNonceAead.indexedReduction (baseDecoder (decode target)) fallback
    (AdaptiveCtxReceive.wrapped (decode target) (clientReduction target decode c client)) attempt

noncomputable def loss {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (qHash qRaw : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (validationReduction target decode c client qHash)) +
    (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
    2 * ∑ attempt ∈ Finset.range qRaw,
      modifiedNonceAeadINTCTXTAdvantage c (forgeryReduction target decode c fallback client attempt) +
    (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat)

noncomputable def game {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) (hop : Nat) : ProbComp Bool :=
  Prod.fst <$> sourceGame (realAt count hop) decode c client

theorem hop_distance {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) qHash)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal)
    (rawBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((game decode c client target.val).boolDistAdvantage (game decode c client (target.val + 1))) ≤
      loss target decode c fallback client qHash qRaw := by
  simpa only [game, loss, clientReduction, validationReduction, forgeryReduction,
    hybrid_before, hybrid_after, join_reconstruct] using
    selected_integrity target (decode target) (otherReal target)
      (fun other => decode (target.succAbove other)) c fallback client qHash qSeal qRaw hashBound sealBound rawBound small

theorem loss_finite {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (qHash qRaw : Nat) :
    loss target decode c fallback client qHash qRaw ≠ ⊤ := by
  unfold loss
  have attempts : (∑ attempt ∈ Finset.range qRaw,
      modifiedNonceAeadINTCTXTAdvantage c (forgeryReduction target decode c fallback client attempt)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun _ _ => probEvent_ne_top)
  simp only [ENNReal.add_ne_top]
  exact ⟨⟨⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top qHash) (ENNReal.inv_ne_top.mpr (by norm_num))⟩,
    ENNReal.mul_ne_top (by norm_num) attempts⟩,
    ENNReal.div_ne_top (ENNReal.natCast_ne_top qRaw) (Nat.cast_ne_zero.mpr (pow_ne_zero 512 (by decide : (2 : Nat) ≠ 0)))⟩

theorem hop_bound {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) qHash)
    (sealBound : client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) qSeal)
    (rawBound : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) qRaw)
    (small : qSeal < 2 ^ 96) :
    (game decode c client target.val).boolDistAdvantage (game decode c client (target.val + 1)) ≤
      (loss target decode c fallback client qHash qRaw).toReal := by
  have converted := ENNReal.toReal_mono (loss_finite target decode c fallback client qHash qRaw)
    (hop_distance target decode c fallback client qHash qSeal qRaw hashBound sealBound rawBound small)
  simpa only [ENNReal.toReal_ofReal (show 0 ≤ (game decode c client target.val).boolDistAdvantage
    (game decode c client (target.val + 1)) from abs_nonneg _)] using converted

noncomputable def hopLoss {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (qHash qRaw : Fin (count + 1) → Nat) (hop : Nat) : ℝ :=
  if valid : hop < count + 1 then
    (loss ⟨hop, valid⟩ decode c fallback client (qHash ⟨hop, valid⟩) (qRaw ⟨hop, valid⟩)).toReal
  else 0

theorem family_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (qHash qSeal qRaw : Fin (count + 1) → Nat)
    (hashBound : ∀ target, client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) (qHash target))
    (sealBound : ∀ target, client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) (qSeal target))
    (rawBound : ∀ target, client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) (qRaw target))
    (small : ∀ target, qSeal target < 2 ^ 96) :
    (game decode c client 0).boolDistAdvantage (game decode c client (count + 1)) ≤
      ∑ target : Fin (count + 1), (loss target decode c fallback client (qHash target) (qRaw target)).toReal := by
  have bound := PqxdhComposition.finiteHybridBound_of_hop_bounds (game decode c client) (count + 1)
    (hopLoss decode c fallback client qHash qRaw) (fun hop valid => by
      simpa only [hopLoss, dif_pos valid] using
        hop_bound ⟨hop, valid⟩ decode c fallback client (qHash ⟨hop, valid⟩) (qSeal ⟨hop, valid⟩) (qRaw ⟨hop, valid⟩)
          (hashBound ⟨hop, valid⟩) (sealBound ⟨hop, valid⟩) (rawBound ⟨hop, valid⟩) (small ⟨hop, valid⟩))
  rw [← Fin.sum_univ_eq_sum_range] at bound
  simpa only [hopLoss, dif_pos (Fin.isLt _)] using bound

end BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.hop_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.hop_distance

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.loss_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.loss_finite

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.hop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.hop_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyIntegrity.family_bound
