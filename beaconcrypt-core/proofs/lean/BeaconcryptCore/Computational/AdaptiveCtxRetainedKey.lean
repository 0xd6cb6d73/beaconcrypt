import BeaconcryptCore.Computational.AdaptiveCtxIndependent

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxRetainedKey

open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead

/-- Retain the challenger's sampled key only in the terminal analysis result, never in the adaptive adversary's input. -/
noncomputable def retainedAdaptiveGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp AdaptiveSpec Result) :
    ProbComp (CtxKey × (Result × (ReceiveState × Bool))) := do
  let key ← $ᵗ CtxKey
  let result ← adaptiveGame real decode c key adversary
  pure (key, result)

/-- The discrepancy coupling retains the exact correlation between the terminal key and full adaptive transcript. -/
theorem retainedAdaptiveGame_distance_le_bad (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp AdaptiveSpec Result) :
    tvDist (retainedAdaptiveGame true decode c adversary)
      (retainedAdaptiveGame false decode c adversary) ≤
      Pr[fun result => result.2.2 = true | uniformAdaptiveGame true decode c adversary].toReal := by
  have convex := tvDist_bind_left_le ($ᵗ CtxKey)
    (fun key => (Prod.mk key) <$> adaptiveGame true decode c key adversary)
    (fun key => (Prod.mk key) <$> adaptiveGame false decode c key adversary)
  rw [tsum_fintype] at convex
  calc
    _ ≤ ∑ key : CtxKey, Pr[= key | ($ᵗ CtxKey)].toReal *
        (Pr[fun result => result.2.2 = true | adaptiveGame true decode c key adversary]).toReal := by
      refine convex.trans (Finset.sum_le_sum fun key _ => ?_)
      exact mul_le_mul_of_nonneg_left
        ((tvDist_map_le (Prod.mk key) _ _).trans
          (adaptiveGame_distance_le_discrepancy decode c key adversary)) ENNReal.toReal_nonneg
    _ = _ := by
      unfold uniformAdaptiveGame
      rw [probEvent_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum]
      · simp only [ENNReal.toReal_mul]
      · intro key _
        exact ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top

/-- The same explicit ordinary integrity family bounds the retained-key transcript distance. -/
theorem retainedAdaptiveGame_distance_le_intctxt_sum (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type} (adversary : OracleComp AdaptiveSpec Result)
    (count : ℕ) (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    ENNReal.ofReal (tvDist (retainedAdaptiveGame true decode c adversary)
      (retainedAdaptiveGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c (indexedReduction decode fallback adversary index) := by
  calc
    _ ≤ ENNReal.ofReal (Pr[fun result => result.2.2 = true |
        uniformAdaptiveGame true decode c adversary].toReal) :=
      ENNReal.ofReal_le_ofReal (retainedAdaptiveGame_distance_le_bad decode c adversary)
    _ = Pr[fun result => result.2.2 = true | uniformAdaptiveGame true decode c adversary] :=
      ENNReal.ofReal_toReal probEvent_ne_top
    _ ≤ _ := uniformAdaptive_bad_le_intctxt_sum decode c fallback adversary count bounded

/-- Terminal key retention for the linked CTX wrapper does not alter any adaptive answer. -/
noncomputable def retainedLinkedGame (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    ProbComp (CtxKey × (Result × (AdaptiveCtxReceive.ReceiveState × (ReceiveState × Bool)))) := do
  let key ← $ᵗ CtxKey
  let result ← AdaptiveCtxReceive.linkedGame real decode c key adversary
  pure (key, result)

/-- Retain key and both private states while reassociating the linked execution. -/
def retainKeyAndBoth {Result : Type}
    (result : CtxKey × ((Result × AdaptiveCtxReceive.ReceiveState) × (ReceiveState × Bool))) :
    CtxKey × (Result × (AdaptiveCtxReceive.ReceiveState × (ReceiveState × Bool))) :=
  (result.1, AdaptiveCtxReceive.retainBoth result.2)

/-- Key retention preserves the exact full-continuation linking equality. -/
theorem retainedLinkedGame_eq (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    retainedLinkedGame real decode c adversary =
      retainKeyAndBoth <$> retainedAdaptiveGame real (AdaptiveCtxReceive.baseDecoder decode) c
        (AdaptiveCtxReceive.wrapped decode adversary) := by
  simp only [retainedLinkedGame, retainedAdaptiveGame, AdaptiveCtxReceive.linkedGame_eq,
    map_bind, bind_pure_comp, Functor.map_map, retainKeyAndBoth]

/-- The full linked transcript keeps the same key-dependent coupling and explicit attempted-forgery family. -/
theorem retainedLinkedGame_distance_le_intctxt_sum (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery count) :
    ENNReal.ofReal (tvDist (retainedLinkedGame true decode c adversary)
      (retainedLinkedGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c
          (indexedReduction (AdaptiveCtxReceive.baseDecoder decode) fallback
            (AdaptiveCtxReceive.wrapped decode adversary) index) := by
  rw [retainedLinkedGame_eq, retainedLinkedGame_eq]
  exact (ENNReal.ofReal_le_ofReal (tvDist_map_le retainKeyAndBoth _ _)).trans
    (retainedAdaptiveGame_distance_le_intctxt_sum _ c fallback _ count
      (AdaptiveCtxReceive.wrapped_raw_query_bound decode adversary count bounded))

/-- The direct independent-public experiment retains the actual sampled key in its analysis result. -/
noncomputable def retainedIndependentGame (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    ProbComp (CtxKey × (Result × AdaptiveCtxReceive.ReceiveState)) := do
  let key ← $ᵗ CtxKey
  let result ← AdaptiveCtxIndependent.independentGame decode c key adversary
  pure (key, result)

/-- Project only the auxiliary primitive-game instrumentation, retaining the source state and the same key. -/
def sourceProjection {Result : Type}
    (result : CtxKey × (Result × (AdaptiveCtxReceive.ReceiveState × (ReceiveState × Bool)))) :
    CtxKey × (Result × AdaptiveCtxReceive.ReceiveState) :=
  (result.1, Prod.map id Prod.fst result.2)

/-- The full source projection still holds jointly with the sampled key. -/
theorem retainedLinkedGame_projection (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) :
    sourceProjection <$> retainedLinkedGame true decode c adversary =
      retainedIndependentGame decode c adversary := by
  simp only [retainedLinkedGame, retainedIndependentGame, map_bind, bind_pure_comp,
    Functor.map_map, sourceProjection]
  congr 1
  funext key
  simpa only [Functor.map_map, Function.comp_def] using
    congrArg (fun game => (Prod.mk key) <$> game)
      (AdaptiveCtxIndependent.linkedGame_projection decode c key adversary)

/-- Key-dependent transcript events inherit the same sum of concrete ordinary integrity reductions. -/
theorem retainedIndependentGame_distance_le_intctxt_sum (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery count) :
    ENNReal.ofReal (tvDist (retainedIndependentGame decode c adversary)
      (sourceProjection <$> retainedLinkedGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c
          (indexedReduction (AdaptiveCtxReceive.baseDecoder decode) fallback
            (AdaptiveCtxReceive.wrapped decode adversary) index) := by
  rw [← retainedLinkedGame_projection]
  exact (ENNReal.ofReal_le_ofReal (tvDist_map_le sourceProjection _ _)).trans
    (retainedLinkedGame_distance_le_intctxt_sum decode c fallback adversary count bounded)

end BeaconcryptCore.Computational.AdaptiveCtxRetainedKey

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxRetainedKey.retainedAdaptiveGame_distance_le_intctxt_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxRetainedKey.retainedAdaptiveGame_distance_le_intctxt_sum

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxRetainedKey.retainedLinkedGame_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxRetainedKey.retainedLinkedGame_projection

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxRetainedKey.retainedIndependentGame_distance_le_intctxt_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxRetainedKey.retainedIndependentGame_distance_le_intctxt_sum
