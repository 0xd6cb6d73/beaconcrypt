import BeaconcryptCore.Computational.AdaptiveCtxSharedReplayCompiler
import BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds

/-!
The actual all-real shared-cache CTX source reaches one explicit ciphertext-randomized view through the proved integrity/replay family and the exact key-free ordinary privacy compiler. The middle experiment is identical, with every per-target cap and explicit reduction retained.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyPrivacy
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation AdaptiveCtxReceive AdaptiveCtxQueryBounds
open AdaptiveCtxSharedKeySelection AdaptiveCtxSharedModeBounds AdaptiveCtxSharedMultiKeyIntegrity
open AdaptiveRawMultiKeyIntegrity (otherReal first_flags final_flags)

noncomputable def privacyReduction {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) : ModifiedNonceAeadINDDollarAdversary :=
  AdaptiveSealMultiKeyPrivacy.reduction target (otherReal target) c
    (AdaptiveCtxSharedReplayCompiler.compiledClient decode client)

/-- Integrity/replay and ciphertext privacy are adjacent simulations of the same sampled source and one common CTX cache. -/
theorem family_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (qHash qSeal qRaw : Fin (count + 1) → Nat)
    (hashBound : ∀ target, client.IsQueryBoundP (SelectionClass target (HashRoute (otherReal target))) (qHash target))
    (sealBound : ∀ target, client.IsQueryBoundP (SelectionClass target (TargetClass SourceSeal)) (qSeal target))
    (rawBound : ∀ target, client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) (qRaw target))
    (small : ∀ target, qSeal target < 2 ^ 96) :
    (Prod.fst <$> sourceGame (fun _ => true) decode c client).boolDistance
      (AdaptiveCtxSharedReplayCompiler.randomView decode c client) ≤
      (∑ target : Fin (count + 1), (loss target decode c fallback client (qHash target) (qRaw target)).toReal) +
        ∑ target : Fin (count + 1), modifiedNonceAeadINDDollarAdvantage c (privacyReduction target decode c client) := by
  have integrity := AdaptiveCtxSharedMultiKeyIntegrity.family_bound decode c fallback client qHash qSeal qRaw
    hashBound sealBound rawBound small
  simp only [game, first_flags, final_flags] at integrity
  exact (ProbComp.boolDistance_triangle _ _ _).trans
    (add_le_add integrity (AdaptiveCtxSharedReplayCompiler.replay_privacy_bound decode c client))

/-- Global public/seal/raw caps instantiate each selected integrity ledger before the same privacy compiler is applied. -/
theorem global_family_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (qPublic qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (AdaptiveCtxSharedMultiKeyBounds.SourceClass SourceHash) qPublic)
    (sealBound : client.IsQueryBoundP (AdaptiveCtxSharedMultiKeyBounds.SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (AdaptiveCtxSharedMultiKeyBounds.SourceClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    (Prod.fst <$> sourceGame (fun _ => true) decode c client).boolDistance
      (AdaptiveCtxSharedReplayCompiler.randomView decode c client) ≤
      (∑ target : Fin (count + 1), (loss target decode c fallback client (qPublic + (qSeal + qRaw)) qRaw).toReal) +
        ∑ target : Fin (count + 1), modifiedNonceAeadINDDollarAdvantage c (privacyReduction target decode c client) := by
  have integrity := AdaptiveCtxSharedMultiKeyBounds.global_family_bound decode c fallback client qPublic qSeal qRaw
    hashBound sealBound rawBound small
  simp only [game, first_flags, final_flags] at integrity
  exact (ProbComp.boolDistance_triangle _ _ _).trans
    (add_le_add integrity (AdaptiveCtxSharedReplayCompiler.replay_privacy_bound decode c client))

end BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyPrivacy

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyPrivacy.family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyPrivacy.family_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyPrivacy.global_family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyPrivacy.global_family_bound
