-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-! Selected-coordinate raw rejection after private-cache erasure. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash AdaptiveCtxReplayDictionary
open PqxdhRecordLiftIdeal
abbrev State := PqxdhRecordFactsPrivateCache.State

/-- Forget private digest-bearing copies of the selected coordinate; retain all nonce and input instrumentation and the complete shared cache. -/
def project (state : State) : State :=
  (({ state.1.1 with successfulSeals := [] }, ∅), state.2)

/-- The selected raw callback records the actual parse and input counters but suppresses its replay reply. -/
noncomputable def raw (decode : RawDecoder) (bytes : Pqxdh.Bytes) :
    StateT State ProbComp (Option Pqxdh.Bytes) := fun state =>
  (fun result => (none, result.2)) <$> (PqxdhRecordFactsPrivateCache.rawBase decode bytes).run state

/-- Muting changes only the selected raw optional reply after the separately proved discarded-cache erasure. -/
noncomputable def impl (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT State ProbComp) := fun query state =>
  match query with
  | .inr bytes => raw decode bytes state
  | .inl request => (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((keyImpl decode crypto key mode (.inl request)).run state.1)).run state.2

/-- The private-copy projection is idempotent. -/
theorem project_idempotent (state : State) : project (project state) = project state := rfl

/-- Muted parsing and exact raw instrumentation cannot read the selected record or private cache. -/
theorem raw_project (decode : RawDecoder) (bytes : Pqxdh.Bytes) (state : State) :
    Prod.map id project <$> (raw decode bytes).run state =
      Prod.map id project <$> (raw decode bytes).run (project state) := by
  unfold raw PqxdhRecordFactsPrivateCache.rawBase
  cases decode bytes <;> simp only [StateT.run, map_pure, project] <;> rfl

/-- Muted source coins remain the literal original coin and retain the complete state. -/
theorem uniform_run (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (coin : unifSpec.Domain) (state : State) :
    (impl mode decode crypto key (.inl (.inl coin))).run state =
      (fun reply => (reply, state)) <$> (unifSpec.query coin : ProbComp _) := by
  cases mode <;> simp only [impl, keyImpl, randomImpl, AdaptiveCtxSharedModes.localImpl,
    AdaptiveCtxSharedReplay.localImpl, AdaptiveCtxSharedHash.localImpl, Bool.false_eq_true,
    ite_true, ite_false, StateT.run, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, hashImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget,
    PFunctor.Handler.liftTarget]
  all_goals change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun reply => (reply, state.1)) <$> (StateT.lift (unifSpec.query coin : ProbComp _))).run state.2 = _
  all_goals simp only [StateT.run_map, StateT.run_lift, Functor.map_map]
  all_goals simp only [bind_pure_comp, Functor.map_map]

/-- Public hashes keep their literal shared-cache behavior and cannot consult the selected private record copies. -/
theorem public_project (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : CtxRO.Domain) (state : State) :
    Prod.map id project <$> (impl mode decode crypto key (.inl (.inr (.inl query)))).run state =
      Prod.map id project <$> (impl mode decode crypto key (.inl (.inr (.inl query)))).run (project state) := by
  cases mode <;> simp only [impl, keyImpl, randomImpl, AdaptiveCtxSharedModes.localImpl,
    AdaptiveCtxSharedReplay.localImpl, AdaptiveCtxSharedHash.localImpl, Bool.false_eq_true,
    ite_true, ite_false, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    hashImpl, QueryImpl.add_apply_inr]
  all_goals have mapApply {α β : Type} (f : α → β) (work : StateT CtxRO.QueryCache ProbComp α)
      (cache : CtxRO.QueryCache) :
      (f <$> work) cache = (fun result => (f result.1, result.2)) <$> work cache :=
    StateT.run_map f work cache
  all_goals simp only [mapApply, Functor.map_map, project]
  all_goals rfl

/-- Every nonsealing query preserves the exact projected state and actual muted reply, including all raw attempts. -/
theorem query_project (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : State) (noSeal : ¬ AdaptiveCtxQueryBounds.SourceSeal query) :
    Prod.map id project <$> (impl mode decode crypto key query).run state =
      Prod.map id project <$> (impl mode decode crypto key query).run (project state) := by
  rcases query with ((coin | (hash | input)) | bytes)
  · simp only [uniform_run, Functor.map_map, Prod.map_apply, id_eq, project_idempotent]
  · exact public_project mode decode crypto key hash state
  · exact False.elim (noSeal trivial)
  · exact raw_project decode bytes state

/-- Every adaptive muted continuation with no later selected seal is independent of private record/cache copies in its starting state. -/
theorem program_project {X : Type} (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp ReceiveSpec X) (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (state : State) :
    Prod.map id project <$> (simulateQ (impl mode decode crypto key) work).run state =
      Prod.map id project <$> (simulateQ (impl mode decode crypto key) work).run (project state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq, project_idempotent]
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noSeal
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have factor (start : State) :
        (do let result ← (impl mode decode crypto key query).run start
            Prod.map id project <$> (simulateQ (impl mode decode crypto key) (next result.1)).run result.2) =
          (do let result ← Prod.map id project <$> (impl mode decode crypto key query).run start
              Prod.map id project <$> (simulateQ (impl mode decode crypto key) (next result.1)).run result.2) := by
      rw [bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 (noSeal.2 result.1) result.2
    rw [factor state, factor (project state)]
    exact congrArg (fun work => work >>= fun result =>
      Prod.map id project <$> (simulateQ (impl mode decode crypto key) (next result.1)).run result.2)
      (query_project mode decode crypto key query state noSeal.1)

/-- Equal projected starting states give identical replies and retained state for the entire muted adaptive continuation. -/
theorem program_congr {X : Type} (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp ReceiveSpec X) (noSeal : work.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0)
    (left right : State) (same : project left = project right) :
    Prod.map id project <$> (simulateQ (impl mode decode crypto key) work).run left =
      Prod.map id project <$> (simulateQ (impl mode decode crypto key) work).run right := by
  rw [program_project mode decode crypto key work noSeal left,
    program_project mode decode crypto key work noSeal right, same]

/-- Before an actual replay match, muting preserves the raw reply and every retained state field after discarded-cache erasure. -/
theorem raw_agrees (decode : RawDecoder) (bytes : Pqxdh.Bytes) (state : State)
    (noMatch : ∀ target, decode bytes = some target →
      replayPlaintext (AdaptiveCtxSharedReplay.install state.1 ∅).ctx target = none) :
    (raw decode bytes).run state =
      (fun result => (result.1.1, result.2)) <$> (PqxdhRecordFactsPrivateCache.rawBase decode bytes).run state := by
  unfold raw PqxdhRecordFactsPrivateCache.rawBase
  cases parsed : decode bytes
  · simp only [StateT.run, map_pure]
  · simp only [StateT.run, map_pure, noMatch _ parsed]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.project_idempotent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.project_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.raw_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.raw_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.uniform_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.uniform_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.public_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.public_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.query_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.program_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.raw_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute.raw_agrees
