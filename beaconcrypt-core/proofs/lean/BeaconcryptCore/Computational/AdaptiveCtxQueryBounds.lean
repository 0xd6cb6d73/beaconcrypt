import BeaconcryptCore.Computational.AdaptiveCtxReceive

/-!
# Adaptive CTX reduction query accounting

Private and public digest misses each require at most 64 individual uniform-byte calls. Every well-formed raw attempt is charged for its private lookup even if commitment comparison or base opening rejects. Source sealing calls and raw deliveries remain separate budgets.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxQueryBounds

open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveRawNonceAead AdaptiveCtxReceive

abbrev TargetUniform := primitiveClass IsPrimitiveUniformQuery
abbrev TargetSeal := primitiveClass IsModifiedNonceAeadSealQuery

/-- Lifting a probabilistic subroutine exposes every uniform query to the constructed reduction's budget. -/
theorem liftProbability_uniform {Result : Type} (work : ProbComp Result) (bound : ℕ)
    (h : work.IsTotalQueryBound bound) :
    (OracleComp.liftComp work AdaptiveSpec).IsQueryBoundP TargetUniform bound := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := AdaptiveSpec) (p := fun _ => True)
    (hpq := fun query => by simp [TargetUniform, primitiveClass, IsPrimitiveUniformQuery, SubSpec.onQuery])
  exact (OracleComp.isQueryBoundP_true_iff work bound).mpr h

/-- Lifting a probabilistic subroutine cannot produce a sealing request. -/
theorem liftProbability_no_seal {Result : Type} (work : ProbComp Result) :
    (OracleComp.liftComp work AdaptiveSpec).IsQueryBoundP TargetSeal 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := AdaptiveSpec) (p := fun _ => False)
    (hpq := fun query => by simp [TargetSeal, primitiveClass, IsModifiedNonceAeadSealQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false work 0)

theorem privateStep_uniform (suffix : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) :
    (privateStep suffix state).IsQueryBoundP TargetUniform 64 := by
  simpa only [privateStep, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    liftProbability_uniform (ctxKeyFreeSuffixStep suffix state.ctx.cache) 64
      (CtxUnclaimedAcceptance.suffixStep_uniform_query_bound suffix state.ctx.cache)

theorem publicStep_uniform (query : CtxRO.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    (publicStep query state).IsQueryBoundP TargetUniform 64 := by
  simpa only [publicStep, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    liftProbability_uniform ((ctxIndependentPublicOracle query).run state.ctx) 64
      (CtxComputationalSecurity.ctxIndependentPublicOracle_total_query_bound query state.ctx)

theorem privateStep_no_seal (suffix : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) :
    (privateStep suffix state).IsQueryBoundP TargetSeal 0 := by
  simpa only [privateStep, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    liftProbability_no_seal (ctxKeyFreeSuffixStep suffix state.ctx.cache)

theorem publicStep_no_seal (query : CtxRO.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    (publicStep query state).IsQueryBoundP TargetSeal 0 := by
  simpa only [publicStep, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    liftProbability_no_seal ((ctxIndependentPublicOracle query).run state.ctx)

/-- Sealing may sample one 64-byte commitment but introduces no uncharged primitive uniform call. -/
theorem sealStep_uniform (input : CtxSealInput) (state : AdaptiveCtxReceive.ReceiveState) :
    (sealStep input state).IsQueryBoundP TargetUniform 64 := by
  unfold sealStep
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl id, ?_⟩
  intro answer
  cases answer with
  | none => trivial
  | some ciphertext =>
    simpa only [TargetUniform, primitiveClass, IsPrimitiveUniformQuery, if_false,
      bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
      privateStep_uniform (outerSuffix input.nonce input.context ciphertext.tag) state

/-- Every source sealing call produces exactly one primitive sealing query, including nonce-rejected calls. -/
theorem sealStep_seal_bound (input : CtxSealInput) (state : AdaptiveCtxReceive.ReceiveState) :
    (sealStep input state).IsQueryBoundP TargetSeal 1 := by
  unfold sealStep
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), ?_⟩
  intro answer
  cases answer with
  | none => trivial
  | some ciphertext =>
    simpa only [TargetSeal, primitiveClass, IsModifiedNonceAeadSealQuery, if_true,
      Nat.sub_self, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
      privateStep_no_seal (outerSuffix input.nonce input.context ciphertext.tag) state

/-- Raw opening performs its full private lookup before either rejecting or asking for the genuine optional plaintext. -/
theorem rawStep_uniform (decode : AdaptiveCtxReceive.RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) :
    (rawStep decode raw state).IsQueryBoundP TargetUniform 64 := by
  cases parsed : decode raw with
  | none => simp [rawStep, parsed]
  | some target =>
    simp only [rawStep, parsed]
    simpa only [Nat.add_zero] using
      OracleComp.isQueryBoundP_bind (n := 64) (m := 0) (privateStep_uniform _ _)
        (fun result _ => by
          split
          · simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
              (OracleComp.isQueryBoundP_query_iff (spec := AdaptiveSpec)
                (p := TargetUniform) (.inr raw) 0).mpr (by simp [TargetUniform, primitiveClass])
          · trivial)

/-- Raw verification never calls the encryption oracle. -/
theorem rawStep_no_seal (decode : AdaptiveCtxReceive.RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) :
    (rawStep decode raw state).IsQueryBoundP TargetSeal 0 := by
  cases parsed : decode raw with
  | none => simp [rawStep, parsed]
  | some target =>
    simp only [rawStep, parsed]
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0) (privateStep_no_seal _ _)
      (fun result _ => by
        split
        · simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
            (OracleComp.isQueryBoundP_query_iff (spec := AdaptiveSpec)
              (p := TargetSeal) (.inr raw) 0).mpr (by simp [TargetSeal, primitiveClass])
        · trivial)

def SourceUniform : ReceiveSpec.Domain → Prop
  | .inl (.inl _) => True
  | _ => False

def SourceSeal : ReceiveSpec.Domain → Prop
  | .inl (.inr (.inr _)) => True
  | _ => False

def SourceHash : ReceiveSpec.Domain → Prop
  | .inl (.inr (.inl _)) => True
  | _ => False

def SourceWork (query : ReceiveSpec.Domain) : Prop := ¬SourceUniform query

instance : DecidablePred SourceUniform := fun query => by
  cases query with
  | inl query => cases query <;> simp only [SourceUniform] <;> infer_instance
  | inr raw => simp only [SourceUniform]; infer_instance
instance : DecidablePred SourceSeal := fun query => by
  cases query with
  | inl query => cases query with
    | inl coin => simp only [SourceSeal]; infer_instance
    | inr query => cases query <;> simp only [SourceSeal] <;> infer_instance
  | inr raw => simp only [SourceSeal]; infer_instance
instance : DecidablePred SourceHash := fun query => by
  cases query with
  | inl query => cases query with
    | inl coin => simp only [SourceHash]; infer_instance
    | inr query => cases query <;> simp only [SourceHash] <;> infer_instance
  | inr raw => simp only [SourceHash]; infer_instance
instance : DecidablePred SourceWork := fun query => inferInstanceAs (Decidable (¬SourceUniform query))

/-- Each source class has its actual uniform cost: one forwarded coin query or at most one 64-byte digest miss. -/
theorem reductionImpl_uniform_step (decode : AdaptiveCtxReceive.RawDecoder)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((reductionImpl decode query).run state).IsQueryBoundP TargetUniform
      (if SourceUniform query then 1 else 64) := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      simp only [StateT.run, reductionImpl, SourceUniform, if_true,
        bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff (spec := AdaptiveSpec)
        (p := TargetUniform) (.inl (.inl coin)) 1).mpr (by intro _; decide)
    | inr query =>
      cases query with
      | inl publicQuery => exact publicStep_uniform publicQuery state
      | inr input => exact sealStep_uniform input state
  | inr raw => exact rawStep_uniform decode raw state

/-- Primitive seals are produced only by source seal calls, once per call. -/
theorem reductionImpl_seal_step (decode : AdaptiveCtxReceive.RawDecoder)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    ((reductionImpl decode query).run state).IsQueryBoundP TargetSeal
      (if SourceSeal query then 1 else 0) := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      simp only [StateT.run, reductionImpl, SourceSeal, if_false,
        bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff (spec := AdaptiveSpec)
        (p := TargetSeal) (.inl (.inl coin)) 0).mpr (by simp [TargetSeal, primitiveClass, IsModifiedNonceAeadSealQuery])
    | inr query =>
      cases query with
      | inl publicQuery => exact publicStep_no_seal publicQuery state
      | inr input => exact sealStep_seal_bound input state
  | inr raw => exact rawStep_no_seal decode raw state

/-- The entire adaptive wrapper inherits the source seal cap independently of raw and public-hash traffic. -/
theorem wrapped_seal_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qSeal : ℕ)
    (bounded : adversary.IsQueryBoundP SourceSeal qSeal) :
    (wrapped decode adversary).IsQueryBoundP TargetSeal qSeal :=
  bounded.simulateQ_run_StateT_of_step (reductionImpl_seal_step decode) initialState

/-- Two query classes are bounded jointly by the sum of their independently supplied caps. -/
theorem query_union_bound {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (left right : ReceiveSpec.Domain → Prop) [DecidablePred left] [DecidablePred right]
    (qLeft qRight : ℕ) (hl : adversary.IsQueryBoundP left qLeft)
    (hr : adversary.IsQueryBoundP right qRight) :
    adversary.IsQueryBoundP (fun query => left query ∨ right query) (qLeft + qRight) := by
  induction adversary using OracleComp.inductionOn generalizing qLeft qRight with
  | pure _ => trivial
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at hl hr ⊢
    refine ⟨?_, ?_⟩
    · by_cases hleft : left query <;> by_cases hright : right query
      all_goals simp only [hleft, hright, not_true_eq_false, false_or, not_false_eq_true, true_or] at hl hr ⊢
      all_goals omega
    · intro answer
      refine (ih answer _ _ (hl.2 answer) (hr.2 answer)).mono ?_
      by_cases hleft : left query <;> by_cases hright : right query
      all_goals simp only [hleft, hright, not_true_eq_false, false_or, not_false_eq_true, true_or, if_true, if_false] at hl hr ⊢
      all_goals omega

/-- The total hash-work cap counts all raw requests, including malformed and repeated rejected attempts. -/
theorem sourceWork_bound {Result : Type} (adversary : OracleComp ReceiveSpec Result)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    adversary.IsQueryBoundP SourceWork (qHash + qSeal + qRaw) := by
  have combined := query_union_bound adversary _ AdaptiveCtxReceive.IsRawQuery (qHash + qSeal) qRaw
    (query_union_bound adversary SourceHash SourceSeal qHash qSeal hashBound sealBound) rawBound
  refine OracleComp.IsQueryBoundP.of_imp (fun query h => ?_) combined
  cases query with
  | inl query =>
    cases query with
    | inl coin => simp [SourceWork, SourceUniform] at h
    | inr query => cases query <;> simp [SourceHash, SourceSeal]
  | inr raw => simp [AdaptiveCtxReceive.IsRawQuery]

/-- The wrapper forwards each source coin once and charges up to 64 new bytes for every other call. -/
theorem wrapped_uniform_pair_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qCoins qWork : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (workBound : adversary.IsQueryBoundP SourceWork qWork) :
    (wrapped decode adversary).IsQueryBoundP TargetUniform (qCoins + 64 * qWork) := by
  have vector := coinBound.and_isQueryBound_pair workBound
  exact vector.simulateQ_run_of_step
    (mapBudget := fun budget : ℕ × ℕ => budget.1 + 64 * budget.2)
    (stepBudget := fun query _ => if SourceUniform query then 1 else 64)
    (combine := Nat.add)
    (fun hstep hrest => OracleComp.isQueryBoundP_bind hstep (fun result _ => hrest result))
    (fun query _ state _ => reductionImpl_uniform_step decode query state)
    (fun query budget allowed => by
      by_cases coins : SourceUniform query
      · simp only [SourceWork, coins, not_true_eq_false, false_or, not_false_eq_true,
          true_or, if_true, if_false] at allowed ⊢
        change 1 + (budget.1 - 1 + 64 * budget.2) = budget.1 + 64 * budget.2
        omega
      · simp only [SourceWork, coins, not_true_eq_false, false_or, not_false_eq_true,
          true_or, if_true, if_false] at allowed ⊢
        change 64 + (budget.1 + 64 * (budget.2 - 1)) = budget.1 + 64 * budget.2
        omega)
    initialState

/-- Source randomness, public hashing, honest sealing and raw receive attempts are charged separately. Failed private queries remain included. -/
theorem wrapped_uniform_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    (wrapped decode adversary).IsQueryBoundP TargetUniform
      (qCoins + 64 * (qHash + qSeal + qRaw)) :=
  wrapped_uniform_pair_bound decode adversary qCoins (qHash + qSeal + qRaw) coinBound
    (sourceWork_bound adversary qHash qSeal qRaw hashBound sealBound rawBound)

/-- Every stopped ordinary INT-CTXT reduction inherits all generated digest randomness and the source seal cap; it has one final verification and no opening oracle. -/
theorem indexedReduction_bounds {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp ReceiveSpec Result)
    (qCoins qHash qSeal qRaw index : ℕ)
    (coinBound : adversary.IsQueryBoundP SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    (indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index).main.IsQueryBoundP
      IsPrimitiveUniformQuery (qCoins + 64 * (qHash + qSeal + qRaw)) ∧
    (indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index).MakesAtMostSealQueries qSeal :=
  AdaptiveRawNonceAead.indexedReduction_query_bounds (baseDecoder decode) fallback (wrapped decode adversary)
    (qCoins + 64 * (qHash + qSeal + qRaw)) qSeal index
    (wrapped_uniform_bound decode adversary qCoins qHash qSeal qRaw coinBound hashBound sealBound rawBound)
    (wrapped_seal_bound decode adversary qSeal sealBound)

end BeaconcryptCore.Computational.AdaptiveCtxQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxQueryBounds.wrapped_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxQueryBounds.wrapped_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxQueryBounds.wrapped_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxQueryBounds.wrapped_seal_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxQueryBounds.indexedReduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxQueryBounds.indexedReduction_bounds
