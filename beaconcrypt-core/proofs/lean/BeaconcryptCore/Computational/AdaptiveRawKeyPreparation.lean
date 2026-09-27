import BeaconcryptCore.Computational.AdaptiveRawKeyFamily
import BeaconcryptCore.Computational.JointEagerTable
import BeaconcryptCore.Computational.CtxComputationalSecurity

/-!
Ten statements construct the actual independent preparation for the selected-key adaptive raw nonce-AEAD hop. An explicit probabilistic preparation returns private non-target keys, full entry states and a context. The complete evaluated execution retains that preparation and all final histories while moving the independent target-key draw across the entire preparation and continuation. The reduction never receives the target key. No equality of marginal key distributions substitutes for this complete continuation law.

The same prepared reduction gives the explicit ordinary attempt-indexed INT-CTXT sum. Preparation uniform queries and all client uniform requests are charged separately; actual source generation adds the target's 32 byte-valued draws. The concrete finite non-target sampler draws one independent uniform 32-byte key for every index and initializes its real empty primitive history. Its source cost is 32 times the complete key count plus client uniform requests. Other setup/local AEAD computation is not free. This component starts at its displayed independent target distribution; it does not prove evolving source-key independence, a CTX shared-cache simulation, native source correspondence, compromise freshness or the all-key/session selection bound. Retained setup/key/history records are private analysis state, never an automatic reveal or persistence interface.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveRawKeyPreparation
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveRawKeyFamily

structure Prepared (Context : Type) (count : Nat) where
  context : Context
  keys : Fin count → CtxKey
  states : OtherState count

noncomputable def wrapped {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    OracleComp AdaptiveSpec (Prepared Context count × (Result × OtherState count)) := do
  let prepared ← OracleComp.liftComp prepare AdaptiveSpec
  let result ← AdaptiveRawKeyFamily.wrapped real decode c prepared.keys (client prepared.context) prepared.states
  pure (prepared, result)

noncomputable def source {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    ProbComp (Prepared Context count × (Result × State count)) := do
  let prepared ← prepare
  let result ← uniformSource targetReal targetDecode real decode c prepared.keys (client prepared.context) prepared.states
  pure (prepared, result)

def reassociate {Context Result : Type} {count : Nat}
    (result : (Prepared Context count × (Result × OtherState count)) × LocalState) :
    Prepared Context count × (Result × State count) :=
  (result.1.1, result.1.2.1, result.1.2.2, result.2)

/-- Independent generation order commutes only with the entire retained setup and adaptive execution. -/
theorem prepared_interpretation {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) :
    𝒮[source prepare targetReal targetDecode real decode c client] =
      𝒮[reassociate <$> uniformAdaptiveGame targetReal targetDecode c (wrapped prepare real decode c client)] := by
  simp only [source, uniformSource, uniformAdaptiveGame, adaptiveGame, wrapped,
    simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    targetUniform, map_bind, bind_assoc, bind_map_left, map_pure]
  simp only [schedule_interpretation, bind_map_left]
  exact evalSPMF_bind_bind_swap prepare ($ᵗ CtxKey) _

/-- Preparation does not consume target encryption or raw-opening queries. -/
theorem prepared_target_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result)
    (p : AdaptiveSpec.Domain → Prop) [DecidablePred p]
    (noUniform : ∀ coin, ¬p (.inl (.inl coin))) (bound : Nat)
    (bounded : ∀ context, (client context).IsQueryBoundP (TargetClass p) bound) :
    (wrapped prepare real decode c client).IsQueryBoundP p bound := by
  unfold wrapped
  rw [← Nat.zero_add bound]
  apply isQueryBoundP_bind (n := 0) (m := bound) (lift_no_class p noUniform prepare)
  intro prepared _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
    wrapped_target_bound real decode c prepared.keys p noUniform (client prepared.context) bound
      (bounded prepared.context) prepared.states

/-- Preparation uniform draws are added explicitly to all client uniform calls. -/
theorem prepared_uniform_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) (setupCount clientCount : Nat)
    (setupBound : prepare.IsTotalQueryBound setupCount)
    (clientBound : ∀ context, (client context).IsQueryBoundP UniformClass clientCount) :
    (wrapped prepare real decode c client).IsQueryBoundP IsUniform (setupCount + clientCount) := by
  unfold wrapped
  apply isQueryBoundP_bind (lift_uniform_bound prepare setupCount setupBound)
  intro prepared _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
    wrapped_uniform_bound real decode c prepared.keys (client prepared.context) clientCount
      (clientBound prepared.context) prepared.states

/-- The actual prepared source hop uses the displayed constructed family of ordinary INT-CTXT forgers. -/
theorem prepared_integrity_bound {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result)
    (fallback : ModifiedNonceAeadForgery) (rawCount : Nat)
    (bounded : ∀ context, (client context).IsQueryBoundP (TargetClass IsRawQuery) rawCount) :
    ENNReal.ofReal (tvDist (source prepare true targetDecode real decode c client)
      (source prepare false targetDecode real decode c client)) ≤
      ∑ index ∈ Finset.range rawCount, modifiedNonceAeadINTCTXTAdvantage c
        (indexedReduction targetDecode fallback (wrapped prepare real decode c client) index) := by
  have linked := uniformAdaptiveGame_distance_le_intctxt_sum targetDecode c fallback
    (wrapped prepare real decode c client) rawCount
    (prepared_target_bound prepare real decode c client IsRawQuery
      (by intro coin; simp [IsRawQuery]) rawCount bounded)
  have mapped := (ENNReal.ofReal_le_ofReal (tvDist_map_le reassociate
    (uniformAdaptiveGame true targetDecode c (wrapped prepare real decode c client))
    (uniformAdaptiveGame false targetDecode c (wrapped prepare real decode c client)))).trans linked
  simpa only [tvDist, ← prepared_interpretation] using mapped

/-- The original prepared source charges preparation, target-key generation and all client randomness. -/
theorem prepared_source_uniform {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (targetReal : Bool) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) (setupCount clientCount : Nat)
    (setupBound : prepare.IsTotalQueryBound setupCount)
    (clientBound : ∀ context, (client context).IsQueryBoundP UniformClass clientCount) :
    (source prepare targetReal targetDecode real decode c client).IsTotalQueryBound (setupCount + (32 + clientCount)) := by
  unfold source
  apply isTotalQueryBound_bind setupBound
  intro prepared
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    source_uniform_bound targetReal targetDecode real decode c prepared.keys (client prepared.context)
      clientCount (clientBound prepared.context) prepared.states

/-- Each actual ordinary forger includes preparation draws and inherits the target seal cap. -/
theorem prepared_reduction_bounds {Context Result : Type} {count : Nat}
    (prepare : ProbComp (Prepared Context count)) (targetDecode : RawDecoder)
    (real : Fin count → Bool) (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) (fallback : ModifiedNonceAeadForgery)
    (setupCount uniformCount sealCount index : Nat)
    (setupBound : prepare.IsTotalQueryBound setupCount)
    (uniformBound : ∀ context, (client context).IsQueryBoundP UniformClass uniformCount)
    (sealBound : ∀ context, (client context).IsQueryBoundP (TargetClass (primitiveClass IsModifiedNonceAeadSealQuery)) sealCount) :
    (indexedReduction targetDecode fallback (wrapped prepare real decode c client) index).main.IsQueryBoundP
      IsPrimitiveUniformQuery (setupCount + uniformCount) ∧
      (indexedReduction targetDecode fallback (wrapped prepare real decode c client) index).MakesAtMostSealQueries sealCount := by
  apply indexedReduction_query_bounds
  · simpa only [uniform_class_exact] using
      prepared_uniform_bound prepare real decode c client setupCount uniformCount setupBound uniformBound
  · exact prepared_target_bound prepare real decode c client (primitiveClass IsModifiedNonceAeadSealQuery)
      (by intro coin; simp [primitiveClass, IsModifiedNonceAeadSealQuery]) sealCount sealBound

/-- The explicit vector sampler draws 32 independent bytes per non-target key. -/
theorem key_vector_bound (count : Nat) :
    ($ᵗ Vector CtxKey count).IsTotalQueryBound (count * 32) := by
  induction count with
  | zero =>
      change IsTotalQueryBound (pure #v[]) 0
      trivial
  | succ count ih =>
      change IsTotalQueryBound
        (Vector.push <$> ($ᵗ Vector CtxKey count) <*> ($ᵗ CtxKey)) ((count + 1) * 32)
      rw [Nat.add_mul, Nat.one_mul]
      exact isTotalQueryBound_seq ((isQueryBound_map_iff _ _ _ _ _).2 ih)
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)

/-- Reindexing the sampled vector as a finite key family adds no random draws. -/
theorem key_family_bound (count : Nat) :
    ($ᵗ (Fin count → CtxKey)).IsTotalQueryBound (count * 32) := by
  change IsTotalQueryBound ((fun (v : Vector CtxKey count) (i : Fin count) => v.get i) <$> ($ᵗ Vector CtxKey count)) (count * 32)
  exact (isQueryBound_map_iff _ _ _ _ _).2 (key_vector_bound count)

/-- The actual non-target preparation samples a uniform key family and installs empty per-key histories. -/
noncomputable def independentSetup {Context : Type} (count : Nat) (context : Context) :
    ProbComp (Prepared Context count) := do
  let keys ← $ᵗ (Fin count → CtxKey)
  pure ⟨context, keys, fun _ => (initialState, false)⟩

/-- All independent non-target key generation is charged in byte-valued uniform queries. -/
theorem independent_setup_bound {Context : Type} (count : Nat) (context : Context) :
    (independentSetup count context).IsTotalQueryBound (count * 32) := by
  simpa only [independentSetup, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using key_family_bound count

/-- The actual independent-key source charges all keys, including the hidden selected key. -/
theorem independent_source_bound {Context Result : Type} (count : Nat) (context : Context)
    (targetReal : Bool) (targetDecode : RawDecoder) (real : Fin count → Bool)
    (decode : Fin count → RawDecoder) (c : Pqxdh.Crypto)
    (client : Context → OracleComp (FamilySpec count) Result) (uniformCount : Nat)
    (bounded : ∀ context, (client context).IsQueryBoundP UniformClass uniformCount) :
    (source (independentSetup count context) targetReal targetDecode real decode c client).IsTotalQueryBound
      ((count + 1) * 32 + uniformCount) := by
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
    prepared_source_uniform (independentSetup count context) targetReal targetDecode real decode c client
      (count * 32) uniformCount (independent_setup_bound count context) bounded

end BeaconcryptCore.Computational.AdaptiveRawKeyPreparation

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_interpretation

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_target_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_integrity_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_integrity_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_source_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.prepared_reduction_bounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.key_vector_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.key_vector_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.key_family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.key_family_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.independent_setup_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.independent_setup_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.independent_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawKeyPreparation.independent_source_bound
