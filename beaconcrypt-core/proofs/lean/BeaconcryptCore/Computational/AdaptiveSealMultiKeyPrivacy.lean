import BeaconcryptCore.Computational.AdaptiveSealKeySelection
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
Each adjacent original-key ciphertext replacement is exactly the ordinary Boolean IND$ advantage of the constructed reduction. The finite hybrid bound then sums those advantages in the same indexed source experiment, without a second target-selection guess.

This independent-key component does not establish the production evolving-material distribution, native reveal/restore freshness or the common computational-symbolic experiment. No primitive implementation is proved. The exact experiments, assumptions, statement explanations and complete query/byte ledgers are maintained in `doc/impl/adaptive-shared-ctx-privacy.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation
open RawKeyPartition AdaptiveSealKeyFamily AdaptiveSealKeySelection
open AdaptiveRawMultiKeyIntegrity (realAt otherReal hybrid_before hybrid_after first_flags final_flags)

noncomputable def reduction {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) : ModifiedNonceAeadINDDollarAdversary :=
  ⟨Prod.fst <$> prepared target real c client⟩

set_option backward.isDefEq.respectTransparency false in
theorem real_reduction {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) :
    𝒟[Prod.fst <$> sourceGame (join target true real) c client] =
      𝒟[modifiedNonceAeadINDDollarRealExp c (reduction target real c client)] := by
  refine EvalDistEq.evalDist_eq ?_
  refine ((source_prepared_selection target true real c client).map Prod.fst).trans ?_
  simp only [map_bind, Functor.map_map, modifiedNonceAeadINDDollarRealExp, reduction,
    simulateQ_map, StateT.run_map, bind_pure_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem random_reduction {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) :
    𝒟[Prod.fst <$> sourceGame (join target false real) c client] =
      𝒟[modifiedNonceAeadINDDollarRandomExp (reduction target real c client)] := by
  refine EvalDistEq.evalDist_eq ?_
  refine ((source_prepared_selection target false real c client).map Prod.fst).trans ?_
  simp only [map_bind, Functor.map_map, modifiedNonceAeadINDDollarRandomExp, reduction,
    simulateQ_map, StateT.run_map, bind_pure_comp, localImpl, Bool.false_eq_true, ite_false, reconstruct]
  exact OracleComp.EvalDistEq.bind_const ($ᵗ CtxKey) _

/-- One original key replacement is exactly the constructed ordinary Boolean IND$ game. -/
theorem selected_advantage {count : Nat} (target : Fin (count + 1)) (real : Fin count → Bool)
    (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) :
    (Prod.fst <$> sourceGame (join target true real) c client).boolDistAdvantage
      (Prod.fst <$> sourceGame (join target false real) c client) =
        modifiedNonceAeadINDDollarAdvantage c (reduction target real c client) := by
  simp only [modifiedNonceAeadINDDollarAdvantage, ProbComp.boolDistAdvantage,
    real_reduction target real c client, random_reduction target real c client]

noncomputable def game {count : Nat} (c : Pqxdh.Crypto)
    (client : OracleComp (Spec (count + 1)) Bool) (hop : Nat) : ProbComp Bool :=
  Prod.fst <$> sourceGame (realAt count hop) c client

theorem hop_advantage {count : Nat} (target : Fin (count + 1)) (c : Pqxdh.Crypto)
    (client : OracleComp (Spec (count + 1)) Bool) :
    (game c client target.val).boolDistAdvantage (game c client (target.val + 1)) =
      modifiedNonceAeadINDDollarAdvantage c (reduction target (otherReal target) c client) := by
  simpa only [game, hybrid_before, hybrid_after] using
    selected_advantage target (otherReal target) c client

noncomputable def hopLoss {count : Nat} (c : Pqxdh.Crypto)
    (client : OracleComp (Spec (count + 1)) Bool) (hop : Nat) : ℝ :=
  if valid : hop < count + 1 then
    modifiedNonceAeadINDDollarAdvantage c (reduction ⟨hop, valid⟩ (otherReal ⟨hop, valid⟩) c client)
  else 0

/-- Every adjacent game is discharged by its constructed one-key reduction before applying the finite hybrid bound. -/
theorem family_bound {count : Nat} (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) :
    (game c client 0).boolDistAdvantage (game c client (count + 1)) ≤
      ∑ target : Fin (count + 1), modifiedNonceAeadINDDollarAdvantage c
        (reduction target (otherReal target) c client) := by
  have bound := PqxdhComposition.finiteHybridBound_of_hop_bounds (game c client) (count + 1)
    (hopLoss c client) (fun hop valid => by
      simpa only [hopLoss, dite_eq_left valid] using
        (hop_advantage ⟨hop, valid⟩ c client).le)
  rw [← Fin.sum_univ_eq_sum_range] at bound
  simpa only [hopLoss, dite_eq_left (Fin.isLt _)] using bound

/-- The actual all-real indexed family is bounded against the same all-random indexed family. -/
theorem all_keys_bound {count : Nat} (c : Pqxdh.Crypto) (client : OracleComp (Spec (count + 1)) Bool) :
    (Prod.fst <$> sourceGame (fun _ => true) c client).boolDistAdvantage
      (Prod.fst <$> sourceGame (fun _ => false) c client) ≤
        ∑ target : Fin (count + 1), modifiedNonceAeadINDDollarAdvantage c
          (reduction target (otherReal target) c client) := by
  simpa only [game, first_flags, final_flags] using family_bound c client

end BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.real_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.real_reduction

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.random_reduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.random_reduction

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.selected_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.selected_advantage

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.hop_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.hop_advantage

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.family_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.all_keys_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveSealMultiKeyPrivacy.all_keys_bound
