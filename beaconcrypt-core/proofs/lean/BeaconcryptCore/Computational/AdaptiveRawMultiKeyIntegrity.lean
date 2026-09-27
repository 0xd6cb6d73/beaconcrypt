import BeaconcryptCore.Computational.AdaptiveRawKeySelection
import BeaconcryptCore.Computational.PqxdhComposition

/-!
Fourteen statements construct adjacent hybrids in the same adaptive independent-key raw nonce-AEAD experiment. Each step replaces actual opening at one original key index by the existing public encryption-log simulation. The reduction family stops at each selected raw attempt and uses the ordinary modified nonce-AEAD INT-CTXT endpoint. The total bound sums those explicitly constructed advantages over every original key and attempt before any uniform security estimate is applied.

With K = count + 1 keys and a global raw cap R, a common per-forger bound epsilon gives K * R * epsilon. Each forger samples the other K - 1 keys, costing 32 * (K - 1) byte-valued uniform queries, forwards all U caller uniform requests and at most S target seals; the original source costs 32 * K + U. All other local cryptographic work remains part of the actual reduction and its source traffic/length costs. There is no nonce inequality premise across different key indices and no key-injectivity premise. The source handlers enforce the ordinary per-index encryption nonce history; accidental equal key values are retained in the games and their primitive advantages. This component does not instantiate source evolving-key freshness, native decoding, CTX, persistence or the final protocol experiment.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveRawKeyFamily RawKeyPartition AdaptiveRawKeySelection

def realAt (count hop : Nat) : Fin (count + 1) → Bool :=
  fun index => decide (hop ≤ index.val)

def otherReal {count : Nat} (target : Fin (count + 1)) : Fin count → Bool :=
  fun other => realAt count target.val (target.succAbove other)

set_option backward.isDefEq.respectTransparency false in
/-- The selected key is the next real-opening index in the actual ordered family hybrid. -/
theorem hybrid_before {count : Nat} (target : Fin (count + 1)) :
    join target true (otherReal target) = realAt count target.val := by
  unfold otherReal
  simpa only [realAt, le_refl, decide_true] using
    join_reconstruct target (realAt count target.val)

/-- Replacing that index advances precisely one step of the same family hybrid. -/
theorem hybrid_after {count : Nat} (target : Fin (count + 1)) :
    join target false (otherReal target) = realAt count (target.val + 1) := by
  rw [join_selected_update target true false, hybrid_before]
  funext index
  by_cases same : index = target
  · simp [same, Function.update, realAt]
  · simp only [Function.update_of_ne same, realAt]
    have distinct : index.val ≠ target.val := fun equal => same (Fin.ext equal)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega

noncomputable def reduction {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (index : Nat) : ModifiedNonceAeadAdversary :=
  indexedReduction (decode target) fallback
    (AdaptiveRawKeyPreparation.wrapped (AdaptiveRawKeyPreparation.independentSetup count ())
      (otherReal target) (fun other => decode (target.succAbove other)) c
      (fun _ => simulateQ (select target) client)) index

/-- The adjacent full-state source distributions use the constructed ordinary forger family. -/
theorem hop_distance {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (rawCount : Nat)
    (bounded : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) rawCount) :
    ENNReal.ofReal (tvDist (sourceGame (realAt count target.val) decode c client)
      (sourceGame (realAt count (target.val + 1)) decode c client)) ≤
      ∑ index ∈ Finset.range rawCount, modifiedNonceAeadINTCTXTAdvantage c
        (reduction target decode c fallback client index) := by
  simpa only [hybrid_before, hybrid_after, join_reconstruct, reduction] using
    selected_integrity target (decode target) (otherReal target)
      (fun other => decode (target.succAbove other)) c fallback client rawCount bounded

noncomputable def game {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (client : OracleComp (SourceSpec count) Bool) (hop : Nat) : ProbComp Bool :=
  Prod.fst <$> sourceGame (realAt count hop) decode c client

/-- The observable decision gap inherits the full-state statistical-distance bound. -/
theorem hop_bound {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (rawCount : Nat)
    (bounded : client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) rawCount) :
    (game decode c client target.val).boolDistAdvantage (game decode c client (target.val + 1)) ≤
      ∑ index ∈ Finset.range rawCount,
        (modifiedNonceAeadINTCTXTAdvantage c (reduction target decode c fallback client index)).toReal := by
  have each : ∀ index ∈ Finset.range rawCount,
      modifiedNonceAeadINTCTXTAdvantage c (reduction target decode c fallback client index) ≠ ⊤ :=
    fun index _ => probEvent_ne_top
  have finite : (∑ index ∈ Finset.range rawCount,
      modifiedNonceAeadINTCTXTAdvantage c (reduction target decode c fallback client index)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr each
  have converted := ENNReal.toReal_mono finite (hop_distance target decode c fallback client rawCount bounded)
  rw [ENNReal.toReal_ofReal (tvDist_nonneg _ _), ENNReal.toReal_sum each] at converted
  have observation :
      (game decode c client target.val).boolDistAdvantage
          (game decode c client (target.val + 1)) ≤
        tvDist (sourceGame (realAt count target.val) decode c client)
          (sourceGame (realAt count (target.val + 1)) decode c client) := by
    unfold game
    simpa only [ProbComp.boolDistAdvantage, evalDist_apply_singleton] using
      (abs_probOutput_toReal_sub_le_tvDist
        (Prod.fst <$> sourceGame (realAt count target.val) decode c client)
        (Prod.fst <$> sourceGame (realAt count (target.val + 1)) decode c client)).trans
          (tvDist_map_le (m := ProbComp) (Prod.fst : Bool × SourceState count → Bool)
            (sourceGame (realAt count target.val) decode c client)
            (sourceGame (realAt count (target.val + 1)) decode c client))
  exact observation.trans converted

noncomputable def hopLoss {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (rawCount : Fin (count + 1) → Nat) (hop : Nat) : ℝ :=
  if valid : hop < count + 1 then
    ∑ index ∈ Finset.range (rawCount ⟨hop, valid⟩),
      (modifiedNonceAeadINTCTXTAdvantage c (reduction ⟨hop, valid⟩ decode c fallback client index)).toReal
  else 0

/-- Only after adjacent simulations are established are their explicit primitive advantages summed. -/
theorem family_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool)
    (rawCount : Fin (count + 1) → Nat)
    (bounded : ∀ target, client.IsQueryBoundP (SelectionClass target (TargetClass IsRawQuery)) (rawCount target)) :
    (game decode c client 0).boolDistAdvantage (game decode c client (count + 1)) ≤
      ∑ target : Fin (count + 1), ∑ index ∈ Finset.range (rawCount target),
        (modifiedNonceAeadINTCTXTAdvantage c (reduction target decode c fallback client index)).toReal := by
  have bound := PqxdhComposition.finiteHybridBound_of_hop_bounds (game decode c client) (count + 1)
    (hopLoss decode c fallback client rawCount) (fun hop valid => by
      simpa only [hopLoss, dif_pos valid] using
        hop_bound ⟨hop, valid⟩ decode c fallback client (rawCount ⟨hop, valid⟩) (bounded ⟨hop, valid⟩))
  rw [← Fin.sum_univ_eq_sum_range] at bound
  simpa only [hopLoss, dif_pos (Fin.isLt _)] using bound

/-- The initial hybrid uses actual opening at every original key index. -/
theorem first_flags (count : Nat) : realAt count 0 = fun _ => true := by
  funext index
  simp [realAt]

/-- The final hybrid uses the encryption-log simulation at every original key index. -/
theorem final_flags (count : Nat) : realAt count (count + 1) = fun _ => false := by
  funext index
  simp [realAt, Nat.not_le.mpr index.isLt]

def SourceClass {count : Nat} (p : AdaptiveSpec.Domain → Prop) : (SourceSpec count).Domain → Prop :=
  fun query => p query.2

instance {count : Nat} (p : AdaptiveSpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (SourceClass (count := count) p) := fun query => inferInstanceAs (Decidable (p query.2))

/-- Every selected-key resource cap follows from its global original-interface cap. -/
theorem selected_source_bound {count : Nat} (target : Fin (count + 1))
    (p : AdaptiveSpec.Domain → Prop) [DecidablePred p] {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (SourceClass p) bound) :
    client.IsQueryBoundP (SelectionClass target (TargetClass p)) bound :=
  bounded.of_imp (fun query selected => (selection_target_class target p query).mp selected |>.2)

/-- A global raw-attempt cap bounds all original-key and receive-slot reductions explicitly. -/
theorem global_attempt_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (rawCount : Nat)
    (bounded : client.IsQueryBoundP (SourceClass IsRawQuery) rawCount) :
    (game decode c client 0).boolDistAdvantage (game decode c client (count + 1)) ≤
      ∑ target : Fin (count + 1), ∑ index ∈ Finset.range rawCount,
        (modifiedNonceAeadINTCTXTAdvantage c (reduction target decode c fallback client index)).toReal :=
  family_bound decode c fallback client (fun _ => rawCount)
    (fun target => selected_source_bound target IsRawQuery client rawCount bounded)

/-- A common bound on the constructed primitive forgers incurs the displayed key-times-attempt loss. -/
theorem uniform_advantage_bound {count : Nat} (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (client : OracleComp (SourceSpec count) Bool) (rawCount : Nat)
    (bounded : client.IsQueryBoundP (SourceClass IsRawQuery) rawCount) (epsilon : ℝ)
    (primitiveBound : ∀ target index, index < rawCount →
      (modifiedNonceAeadINTCTXTAdvantage c (reduction target decode c fallback client index)).toReal ≤ epsilon) :
    (game decode c client 0).boolDistAdvantage (game decode c client (count + 1)) ≤
      (count + 1 : Nat) * (rawCount * epsilon) := by
  apply (global_attempt_bound decode c fallback client rawCount bounded).trans
  calc
    _ ≤ ∑ target : Fin (count + 1), ∑ _index ∈ Finset.range rawCount, epsilon :=
      Finset.sum_le_sum (fun target _ => Finset.sum_le_sum (fun index member =>
        primitiveBound target index (Finset.mem_range.mp member)))
    _ = _ := by simp

/-- Every forger charges non-target key generation and all randomness, with the original seal cap. -/
theorem ordinary_reduction_bounds {count : Nat} (target : Fin (count + 1))
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (uniformCount sealCount index : Nat)
    (uniformBound : client.IsQueryBoundP SourceUniform uniformCount)
    (sealBound : client.IsQueryBoundP (SourceClass (primitiveClass IsModifiedNonceAeadSealQuery)) sealCount) :
    (reduction target decode c fallback client index).main.IsQueryBoundP
      IsPrimitiveUniformQuery (count * 32 + uniformCount) ∧
      (reduction target decode c fallback client index).MakesAtMostSealQueries sealCount :=
  selected_reduction_bounds target (decode target) (otherReal target)
    (fun other => decode (target.succAbove other)) c fallback client uniformCount sealCount index
    uniformBound (selected_source_bound target _ client sealCount sealBound)

set_option backward.isDefEq.respectTransparency false in
/-- The actual all-key source step preserves its explicit caller-uniform cost. -/
theorem source_uniform_step {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey)
    (query : (SourceSpec count).Domain) (state : SourceState count) :
    ((AdaptiveRawKeySelection.sourceImpl real decode c keys query).run state).IsTotalQueryBound
      (if SourceUniform query then 1 else 0) := by
  simpa only [AdaptiveRawKeySelection.sourceImpl, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff, SourceUniform] using
    local_uniform_bound (real query.1) (decode query.1) c (keys query.1) query.2 (state query.1)

/-- The actual full adaptive source continuation obeys the caller-uniform budget. -/
theorem source_run_uniform {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP SourceUniform bound) (state : SourceState count) :
    ((simulateQ (AdaptiveRawKeySelection.sourceImpl real decode c keys) client).run state).IsTotalQueryBound bound := by
  apply (isQueryBoundP_true_iff _ bound).mp
  apply bounded.simulateQ_run_StateT_of_step
  intro query before
  exact (isQueryBoundP_true_iff _ _).mpr (source_uniform_step real decode c keys query before)

/-- The source program charges its entire sampled key family in addition to caller randomness. -/
theorem source_uniform_bound {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (bound : Nat)
    (bounded : client.IsQueryBoundP SourceUniform bound) :
    (sourceGame real decode c client).IsTotalQueryBound ((count + 1) * 32 + bound) := by
  unfold sourceGame
  apply isTotalQueryBound_bind (AdaptiveRawKeyPreparation.key_family_bound (count + 1))
  intro keys
  exact source_run_uniform real decode c keys client bound bounded _

end BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hybrid_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hybrid_before

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hybrid_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hybrid_after

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hop_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hop_distance

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.hop_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.family_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.first_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.first_flags

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.final_flags' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.final_flags

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.selected_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.selected_source_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.global_attempt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.global_attempt_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.uniform_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.uniform_advantage_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.ordinary_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.ordinary_reduction_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.source_uniform_step' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.source_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.source_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.source_run_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.source_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawMultiKeyIntegrity.source_uniform_bound
