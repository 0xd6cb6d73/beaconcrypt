import BeaconcryptCore.Computational.AdaptiveCtxSharedModes

/-!
Mode-aware query accounting charges real private work to the shared public hash service and replay private dictionary misses to actual uniform sampling. All possible raw and seal attempts are counted. A private operation is separate from an original caller uniform request.

The final family games use independently sampled hidden keys; the lower-level operational simulations retain their stated arbitrary-key parameters. Source evolving-key distributions, reveal/restore freshness, dynamic sessions and the final computational-symbolic bridge require further composition. No primitive implementation is proved. Every substantial statement is explained in `doc/impl/adaptive-shared-ctx-hybrids.md`.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxQueryBounds
open AdaptiveCtxSharedReplay

theorem lift_hash_bound {Result : Type} (work : ProbComp Result) :
    (OracleComp.liftComp work HashSpec).IsQueryBoundP (HashClass true) 0 := by
  exact IsQueryBoundP.liftComp_subSpec (spec := unifSpec) (superSpec := HashSpec)
    (p := fun _ => False) (hpq := fun query => by simp [HashClass, SubSpec.onQuery])
    (isQueryBoundP_false work 0)

theorem private_hash_bound (suffix : Pqxdh.Bytes) (entry : AdaptiveCtxSharedReplay.Local) :
    (localPrivate suffix entry).IsQueryBoundP (HashClass true) 0 := by
  simpa only [localPrivate, bind_pure_comp, isQueryBoundP_map_iff] using lift_hash_bound (privateLookup suffix entry.2)

set_option backward.isDefEq.respectTransparency false in
theorem replay_hash_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : AdaptiveCtxSharedReplay.Local) :
    ((AdaptiveCtxSharedReplay.localImpl decode c key query).run entry).IsQueryBoundP (HashClass true)
      (if SourceHash query then 1 else 0) := by
  rcases query with (coin | (hash | input)) | raw
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceHash, ite_false, isQueryBoundP_query_iff, HashClass]
    decide
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceHash, ite_true, isQueryBoundP_query_iff, HashClass]
    decide
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, AdaptiveCtxSharedReplay.localSeal,
      SourceHash, ite_false]
    split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using private_hash_bound _ entry
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, AdaptiveCtxSharedReplay.localRaw,
      SourceHash, ite_false]
    split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using private_hash_bound _ _

def ModeHash (real : Bool) (query : ReceiveSpec.Domain) : Prop :=
  if real then SourceWork query else SourceHash query

instance (real : Bool) : DecidablePred (ModeHash real) := fun query => by
  unfold ModeHash
  split <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem mode_hash_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : AdaptiveCtxSharedModes.Entry) :
    ((AdaptiveCtxSharedModes.localImpl real decode c key query).run entry).IsQueryBoundP (HashClass true)
      (if ModeHash real query then 1 else 0) := by
  cases real
  · exact replay_hash_step decode c key query entry
  · simpa only [AdaptiveCtxSharedModes.localImpl, StateT.run, ite_true, bind_pure_comp,
      isQueryBoundP_map_iff, ModeHash, SourceClass] using
      AdaptiveCtxSharedHash.local_step_bound true decode c key query entry.1

theorem mode_hash_schedule (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (bound : Nat)
    (bounded : client.IsQueryBoundP (ModeHash real) bound) (entry : AdaptiveCtxSharedModes.Entry) :
    ((simulateQ (AdaptiveCtxSharedModes.localImpl real decode c key) client).run entry).IsQueryBoundP (HashClass true) bound :=
  bounded.simulateQ_run_StateT_of_step (mode_hash_step real decode c key) entry

set_option maxRecDepth 10000 in
theorem private_lookup_uniform (suffix : Pqxdh.Bytes) (cache : CtxSuffixRO.QueryCache) :
    (privateLookup suffix cache).IsTotalQueryBound 64 := by
  unfold privateLookup
  split
  · trivial
  · simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
      CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64

theorem lift_uniform_bound {Result : Type} (work : ProbComp Result) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) :
    (OracleComp.liftComp work HashSpec).IsQueryBoundP (HashClass false) bound := by
  apply IsQueryBoundP.liftComp_subSpec (spec := unifSpec) (superSpec := HashSpec)
    (p := fun _ => True) (hpq := fun query => by simp [HashClass, SubSpec.onQuery])
  exact (isQueryBoundP_true_iff _ _).mpr bounded

theorem private_uniform_bound (suffix : Pqxdh.Bytes) (entry : AdaptiveCtxSharedReplay.Local) :
    (localPrivate suffix entry).IsQueryBoundP (HashClass false) 64 := by
  simpa only [localPrivate, bind_pure_comp, isQueryBoundP_map_iff] using
    lift_uniform_bound (privateLookup suffix entry.2) 64 (private_lookup_uniform suffix entry.2)

set_option backward.isDefEq.respectTransparency false in
theorem replay_uniform_step (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : AdaptiveCtxSharedReplay.Local) :
    ((AdaptiveCtxSharedReplay.localImpl decode c key query).run entry).IsQueryBoundP (HashClass false)
      (if SourceUniform query then 1 else if SourceHash query then 0 else 64) := by
  rcases query with (coin | (hash | input)) | raw
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceUniform, ite_true, isQueryBoundP_query_iff, HashClass]
    decide
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff,
      SourceUniform, SourceHash, ite_false, ite_true, isQueryBoundP_query_iff, HashClass]
    decide
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, AdaptiveCtxSharedReplay.localSeal,
      SourceUniform, SourceHash, ite_false]
    split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using private_uniform_bound _ entry
  · simp only [AdaptiveCtxSharedReplay.localImpl, StateT.run, AdaptiveCtxSharedReplay.localRaw,
      SourceUniform, SourceHash, ite_false]
    split
    · trivial
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using private_uniform_bound _ _

def ModePrivate (real : Bool) (query : ReceiveSpec.Domain) : Prop :=
  if real then False else ¬SourceUniform query ∧ ¬SourceHash query

instance (real : Bool) : DecidablePred (ModePrivate real) := fun query => by
  unfold ModePrivate
  split <;> infer_instance

theorem mode_private_not_uniform (real : Bool) (query : ReceiveSpec.Domain)
    (privateCall : ModePrivate real query) : ¬SourceUniform query := by
  cases real <;> simp only [ModePrivate, Bool.false_eq_true, ite_false, ite_true] at privateCall
  · exact privateCall.1

set_option backward.isDefEq.respectTransparency false in
theorem mode_uniform_step (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : AdaptiveCtxSharedModes.Entry) :
    ((AdaptiveCtxSharedModes.localImpl real decode c key query).run entry).IsQueryBoundP (HashClass false)
      (if SourceUniform query then 1 else if ModePrivate real query then 64 else 0) := by
  cases real
  · have bound := replay_uniform_step decode c key query entry
    by_cases coins : SourceUniform query <;> by_cases hash : SourceHash query <;>
      simpa only [AdaptiveCtxSharedModes.localImpl, StateT.run, Bool.false_eq_true, ite_false,
        ModePrivate, coins, hash, not_true_eq_false, not_false_eq_true, false_and, true_and, ite_true] using bound
  · simpa only [AdaptiveCtxSharedModes.localImpl, StateT.run, ite_true, bind_pure_comp,
      isQueryBoundP_map_iff, ModePrivate, ite_false, SourceClass, Bool.false_eq_true] using
      AdaptiveCtxSharedHash.local_step_bound false decode c key query entry.1

theorem mode_uniform_schedule (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (qUniform qPrivate : Nat)
    (uniformBound : client.IsQueryBoundP SourceUniform qUniform)
    (privateBound : client.IsQueryBoundP (ModePrivate real) qPrivate) (entry : AdaptiveCtxSharedModes.Entry) :
    ((simulateQ (AdaptiveCtxSharedModes.localImpl real decode c key) client).run entry).IsQueryBoundP (HashClass false)
      (qUniform + 64 * qPrivate) := by
  have vector := uniformBound.and_isQueryBound_pair privateBound
  exact vector.simulateQ_run_of_step (mapBudget := fun budget : Nat × Nat => budget.1 + 64 * budget.2)
    (stepBudget := fun query _ => if SourceUniform query then 1 else if ModePrivate real query then 64 else 0)
    (combine := Nat.add)
    (fun stepBound restBound => isQueryBoundP_bind stepBound (fun result _ => restBound result))
    (fun query _ state _ => mode_uniform_step real decode c key query state)
    (fun query budget allowed => by
      by_cases coins : SourceUniform query
      · have noPrivate : ¬ModePrivate real query := fun hit => mode_private_not_uniform real query hit coins
        simp only [coins, noPrivate, ite_true, ite_false] at allowed ⊢
        change 1 + (budget.1 - 1 + 64 * budget.2) = budget.1 + 64 * budget.2
        simp only [not_true_eq_false, false_or] at allowed
        omega
      · by_cases privateCall : ModePrivate real query
        · simp only [coins, privateCall, ite_true, ite_false] at allowed ⊢
          change 64 + (budget.1 + 64 * (budget.2 - 1)) = budget.1 + 64 * budget.2
          simp only [not_true_eq_false, false_or] at allowed
          omega
        · simp only [coins, privateCall, ite_false]
          change 0 + (budget.1 + 64 * budget.2) = budget.1 + 64 * budget.2
          exact Nat.zero_add _) entry

end BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.lift_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.lift_hash_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.private_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.private_hash_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.replay_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.replay_hash_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_hash_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_hash_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_hash_schedule

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.private_lookup_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.private_lookup_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.lift_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.lift_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.private_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.private_uniform_bound

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.replay_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.replay_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_private_not_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_private_not_uniform

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_uniform_step

/-- info: 'BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_uniform_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxSharedReplayBounds.mode_uniform_schedule
