import BeaconcryptCore.Computational.AdaptiveCtxSharedKeySelection
import BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds
import BeaconcryptCore.Computational.AdaptiveCtxSharedMultiKeyBounds

/-!
Eight statements count every actual uniform query in the fully indexed mixed canonical/replay source. Canonical operations use the one shared commitment cache; processed-key operations retain their existing private suffix dictionaries. Cache hits and rejected requests remain in the computation, and the conservative bound charges each non-coin source call at most 64 byte-valued draws. No equal-key, nonce, encoding or cache-input injectivity is required.

The original all-index source classes give U + 64(H + S + R) draws for every adaptive continuation and arbitrary entry state. The displayed sourceGame additionally executes the actual independently sampled family of count + 1 32-byte keys, giving 32(count + 1) + U + 64(H + S + R). This counts the specified independent-key game; it neither proves native evolving-key independence nor supplies a security reduction, a native runtime cost bound or new reveal permissions. The complete per-key history and common cache remain retained private state. Local AEAD, parsing, indexing and table work remain real computation. The statements are explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxQueryBounds AdaptiveCtxSharedHash
open AdaptiveCtxSharedReplayBounds AdaptiveCtxSharedKeySelection

abbrev SourceClass {count : Nat} (p : ReceiveSpec.Domain → Prop) : (SourceSpec count).Domain → Prop :=
  AdaptiveCtxSharedMultiKeyBounds.SourceClass p

/-- The actual shared hash interpreter forwards one coin or pays at most 64 bytes for a digest miss. -/
theorem hash_step_bound (query : HashSpec.Domain) (cache : CtxRO.QueryCache) :
    ((hashImpl query).run cache).IsTotalQueryBound (if HashClass false query then 1 else 64) := by
  cases query with
  | inl coin =>
    rw [AdaptiveCtxSharedModes.hash_uniform_step]
    simp [HashClass, IsTotalQueryBound]
  | inr hash => exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound hash cache

/-- Every adaptive hash-interface continuation retains its complete cache and both resource classes. -/
theorem hash_run_bound {Result : Type} (work : OracleComp HashSpec Result)
    (qUniform qHash : Nat)
    (uniformBound : work.IsQueryBoundP (HashClass false) qUniform)
    (hashBound : work.IsQueryBoundP (HashClass true) qHash) (cache : CtxRO.QueryCache) :
    ((simulateQ hashImpl work).run cache).IsTotalQueryBound (qUniform + 64 * qHash) := by
  have vector := uniformBound.and_isQueryBound_pair hashBound
  exact vector.simulateQ_run_of_step
    (mapBudget := fun budget : Nat × Nat => budget.1 + 64 * budget.2)
    (stepBudget := fun query _ => if HashClass false query then 1 else 64)
    (combine := Nat.add)
    (fun step rest => isTotalQueryBound_bind step rest)
    (fun query _ state _ => hash_step_bound query state)
    (fun query budget allowed => by
      cases query with
      | inl coin =>
        simp [HashClass] at allowed ⊢
        change 1 + (budget.1 - 1 + 64 * budget.2) = budget.1 + 64 * budget.2
        omega
      | inr hash =>
        simp [HashClass] at allowed ⊢
        change 64 + (budget.1 + 64 * (budget.2 - 1)) = budget.1 + 64 * budget.2
        omega) cache

/-- Either canonical or processed-key execution pays one coin draw or at most 64 private/public digest draws. -/
theorem target_step_bound (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxSharedModes.State) :
    ((AdaptiveCtxSharedModes.targetImpl real decode c key query).run state).IsTotalQueryBound
      (if SourceUniform query then 1 else 64) := by
  rw [AdaptiveCtxSharedModes.target_run]
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  have bounded := hash_run_bound ((AdaptiveCtxSharedModes.localImpl real decode c key query).run state.1)
    _ _ (mode_uniform_step real decode c key query state.1)
    (mode_hash_step real decode c key query state.1) state.2
  apply bounded.mono
  cases real <;> rcases query with (coin | (hash | input)) | raw <;>
    simp [ModePrivate, ModeHash, SourceWork, SourceUniform, SourceHash]

set_option backward.isDefEq.respectTransparency false in
/-- Original-index routing retains the complete family state and the selected operation bound. -/
theorem source_step_bound {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey)
    (query : (SourceSpec count).Domain) (state : SourceState count) :
    ((sourceImpl real decode c keys query).run state).IsTotalQueryBound
      (if SourceClass SourceUniform query then 1 else 64) := by
  simpa only [sourceImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff,
    SourceClass, AdaptiveCtxSharedMultiKeyBounds.SourceClass] using target_step_bound (real query.1) (decode query.1) c (keys query.1)
      query.2 (state.1 query.1, state.2)

/-- Arbitrary adaptive source traffic consumes the original coin and non-coin budgets. -/
theorem source_run_pair_bound {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (qUniform qWork : Nat)
    (uniformBound : client.IsQueryBoundP (SourceClass SourceUniform) qUniform)
    (workBound : client.IsQueryBoundP (SourceClass SourceWork) qWork) (state : SourceState count) :
    ((simulateQ (sourceImpl real decode c keys) client).run state).IsTotalQueryBound
      (qUniform + 64 * qWork) := by
  have vector := uniformBound.and_isQueryBound_pair workBound
  exact vector.simulateQ_run_of_step
    (mapBudget := fun budget : Nat × Nat => budget.1 + 64 * budget.2)
    (stepBudget := fun query _ => if SourceClass SourceUniform query then 1 else 64)
    (combine := Nat.add)
    (fun step rest => isTotalQueryBound_bind step rest)
    (fun query _ state _ => source_step_bound real decode c keys query state)
    (fun query budget allowed => by
      by_cases coins : SourceUniform query.2
      · simp only [SourceClass, AdaptiveCtxSharedMultiKeyBounds.SourceClass, SourceWork, coins, not_true_eq_false, false_or,
          not_false_eq_true, true_or, ite_true, ite_false] at allowed ⊢
        change 1 + (budget.1 - 1 + 64 * budget.2) = budget.1 + 64 * budget.2
        omega
      · simp only [SourceClass, AdaptiveCtxSharedMultiKeyBounds.SourceClass, SourceWork, coins, not_true_eq_false, false_or,
          not_false_eq_true, true_or, ite_true, ite_false] at allowed ⊢
        change 64 + (budget.1 + 64 * (budget.2 - 1)) = budget.1 + 64 * budget.2
        omega) state

set_option backward.isDefEq.respectTransparency false in
/-- Every original public-hash, seal and raw-attempt budget contributes to the source work union. -/
theorem source_work_bound {count : Nat} {Result : Type}
    (client : OracleComp (SourceSpec count) Result) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP (SourceClass SourceHash) qHash)
    (sealBound : client.IsQueryBoundP (SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (SourceClass IsRawQuery) qRaw) :
    client.IsQueryBoundP (SourceClass SourceWork) (qHash + qSeal + qRaw) := by
  simpa only [Nat.add_assoc] using
    AdaptiveCtxSharedMultiKeyBounds.global_work_bound client qHash qSeal qRaw hashBound sealBound rawBound

/-- The complete all-index source run counts every public query and attempted record operation. -/
theorem source_run_bound {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto) (keys : Fin (count + 1) → CtxKey)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (SourceClass SourceUniform) qUniform)
    (hashBound : client.IsQueryBoundP (SourceClass SourceHash) qHash)
    (sealBound : client.IsQueryBoundP (SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (SourceClass IsRawQuery) qRaw) (state : SourceState count) :
    ((simulateQ (sourceImpl real decode c keys) client).run state).IsTotalQueryBound
      (qUniform + 64 * (qHash + qSeal + qRaw)) :=
  source_run_pair_bound real decode c keys client qUniform _ uniformBound
    (source_work_bound client qHash qSeal qRaw hashBound sealBound rawBound) state

/-- The actual full-key sampler is included in the complete mixed-mode source uniform cap. -/
theorem source_game_bound {count : Nat} (real : Fin (count + 1) → Bool)
    (decode : Fin (count + 1) → RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp (SourceSpec count) Result) (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : client.IsQueryBoundP (SourceClass SourceUniform) qUniform)
    (hashBound : client.IsQueryBoundP (SourceClass SourceHash) qHash)
    (sealBound : client.IsQueryBoundP (SourceClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (SourceClass IsRawQuery) qRaw) :
    (sourceGame real decode c client).IsTotalQueryBound
      (32 * (count + 1) + qUniform + 64 * (qHash + qSeal + qRaw)) := by
  unfold sourceGame
  have bound := isTotalQueryBound_bind (AdaptiveRawKeyPreparation.key_family_bound (count + 1))
    (fun keys => source_run_bound real decode c keys client qUniform qHash qSeal qRaw
      uniformBound hashBound sealBound rawBound ((fun _ => AdaptiveCtxSharedModes.initialEntry), ∅))
  simpa only [Nat.mul_comm (count + 1) 32, Nat.add_assoc] using bound

end BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.hash_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.hash_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.hash_run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.hash_run_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.target_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.target_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_step_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_run_pair_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_run_pair_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_work_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_work_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_run_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_game_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedSourceBounds.source_game_bound
