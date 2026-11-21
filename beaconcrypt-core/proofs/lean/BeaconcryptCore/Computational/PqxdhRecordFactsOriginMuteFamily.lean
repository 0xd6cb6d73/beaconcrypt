-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMute
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheSource

/-! Selected-coordinate muted continuation lifted through the full shared-cache family. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily
open CtxRomAuth AdaptiveCtxReceive LazyOracleDiscard
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec materialAt)
open PqxdhRecordFactsPrivateCacheFamily (localLens erasedKeyed)
variable {n : Nat}

/-- Remove only the chosen coordinate's seal dictionary and private suffix cache. All other private state is retained. -/
noncomputable def project (target : Label n) (state : CtxPrivate n) : CtxPrivate n :=
  (localLens target).set state (PqxdhRecordFactsOriginMute.project ((localLens target).get state))

/-- The selected one-key projection changes no base field. -/
theorem project_base (target : Label n) (state : CtxPrivate n) :
    (project target state).base = state.base := rfl

/-- The selected local endpoint sees exactly its local muted-state projection. -/
theorem project_get (target : Label n) (state : CtxPrivate n) :
    (localLens target).get (project target state) =
      PqxdhRecordFactsOriginMute.project ((localLens target).get state) :=
  (localLens target).get_set state _

/-- The selected family projection is idempotent. -/
theorem project_idempotent (target : Label n) (state : CtxPrivate n) :
    project target (project target state) = project target state := by
  unfold project
  rw [(localLens target).get_set, PqxdhRecordFactsOriginMute.project_idempotent,
    (localLens target).set_set]

/-- A projected local step lifts through its actual coordinate lens without losing the surrounding family state. -/
theorem local_project {X : Type} (target : Label n)
    (step : StateT PqxdhRecordFactsPrivateCache.State ProbComp X)
    (blind : ∀ state, Prod.map id PqxdhRecordFactsOriginMute.project <$> step.run state =
      Prod.map id PqxdhRecordFactsOriginMute.project <$> step.run (PqxdhRecordFactsOriginMute.project state))
    (state : CtxPrivate n) :
    Prod.map id (project target) <$> ((localLens target).lift step).run state =
      Prod.map id (project target) <$> ((localLens target).lift step).run (project target state) := by
  have exactLocal := congrArg (fun work => (fun result => (result.1, (localLens target).set state result.2)) <$> work)
    (blind ((localLens target).get state))
  simpa only [StateLens.lift, StateT.run, Functor.map_map, project, Prod.map, id_eq,
    (localLens target).get_set, (localLens target).set_set] using exactLocal

/-- Any local step on another coordinate commutes with forgetting the target copies, including its actual shared-cache updates. -/
theorem other_project {X : Type} (target other : Label n) (different : other ≠ target)
    (step : StateT PqxdhRecordFactsPrivateCache.State ProbComp X) (state : CtxPrivate n) :
    Prod.map id (project target) <$> ((localLens other).lift step).run state =
      Prod.map id (project target) <$> ((localLens other).lift step).run (project target state) := by
  simp only [StateLens.lift, StateT.run, localLens, project, PqxdhRecordFactsOriginMute.project,
    Function.update_of_ne different, Functor.map_map]
  simp only [Prod.map, id_eq, project, localLens, PqxdhRecordFactsOriginMute.project,
    Function.update_of_ne (Ne.symm different), Function.update_self, Function.update_comm different,
    Function.update_idem]

/-- The target sealing-query predicate uses the actual queried coordinate. -/
def IsTargetSeal (target : Label n) (query : (KeyedSpec n).Domain) : Prop :=
  query.1 = target ∧ AdaptiveCtxQueryBounds.SourceSeal query.2

instance (target : Label n) : DecidablePred (IsTargetSeal target) :=
  fun query => inferInstanceAs (Decidable (query.1 = target ∧ AdaptiveCtxQueryBounds.SourceSeal query.2))

/-- Use muted raw replies only at the selected coordinate; every other coordinate uses its unchanged erased endpoint. -/
noncomputable def keyed (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) :
    QueryImpl (KeyedSpec n) (StateT (CtxPrivate n) ProbComp) := fun query state =>
  if query.1 = target then
    ((localLens query.1).lift (PqxdhRecordFactsOriginMute.impl (modes query.1) decode crypto
      (materialAt state.base.chain query.1).1 query.2)).run state
  else (erasedKeyed modes decode crypto query).run state

/-- Every family query except a later target seal commutes with the selected private-copy projection. -/
theorem keyed_project (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain)
    (state : CtxPrivate n) (noSeal : ¬IsTargetSeal target query) :
    Prod.map id (project target) <$> (keyed target modes decode crypto query).run state =
      Prod.map id (project target) <$> (keyed target modes decode crypto query).run (project target state) := by
  rcases query with ⟨label, query⟩
  by_cases selected : label = target
  · subst label
    simp only [keyed, StateT.run, ite_true, project_base]
    exact local_project target _ (fun before => PqxdhRecordFactsOriginMute.query_project
      (modes target) decode crypto (materialAt state.base.chain target).1 query before (fun sealing => noSeal ⟨rfl, sealing⟩)) state
  · simp only [keyed, StateT.run, selected, ite_false]
    change Prod.map id (project target) <$> (erasedKeyed modes decode crypto (label, query)).run state =
      Prod.map id (project target) <$> (erasedKeyed modes decode crypto (label, query)).run (project target state)
    rw [PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run, PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run]
    simpa only [PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run, StateLens.lift, StateT.run,
      localLens, project_base] using other_project target label selected
        (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto (materialAt state.base.chain label).1
          (modes label) query) state

/-- Any adaptive family continuation without another target seal is independent of the selected private copies, while every other coordinate remains real to this erased ideal experiment. -/
theorem program_project {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (work : OracleComp (KeyedSpec n) X)
    (noSeal : work.IsQueryBoundP (IsTargetSeal target) 0) (state : CtxPrivate n) :
    Prod.map id (project target) <$> (simulateQ (keyed target modes decode crypto) work).run state =
      Prod.map id (project target) <$> (simulateQ (keyed target modes decode crypto) work).run (project target state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq, project_idempotent]
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noSeal
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have factor (start : CtxPrivate n) :
        (do let result ← (keyed target modes decode crypto query).run start
            Prod.map id (project target) <$> (simulateQ (keyed target modes decode crypto) (next result.1)).run result.2) =
          (do let result ← Prod.map id (project target) <$> (keyed target modes decode crypto query).run start
              Prod.map id (project target) <$> (simulateQ (keyed target modes decode crypto) (next result.1)).run result.2) := by
      rw [bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 (noSeal.2 result.1) result.2
    rw [factor state, factor (project target state)]
    exact congrArg (fun work => work >>= fun result =>
      Prod.map id (project target) <$> (simulateQ (keyed target modes decode crypto) (next result.1)).run result.2)
      (keyed_project target modes decode crypto query state noSeal.1)

/-- A nonraw selected request is exactly the original cache-erased local endpoint, including sealing when considered in isolation. -/
theorem local_nonraw (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (request : (unifSpec + CtxAdversarySpec).Domain) (state : PqxdhRecordFactsPrivateCache.State) :
    (PqxdhRecordFactsOriginMute.impl mode decode crypto key (.inl request)).run state =
      (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inl request)).run state := by
  simp only [PqxdhRecordFactsPrivateCacheRandom.erased, PqxdhRecordFactsPrivateCacheRandom.modePointed,
    StateT.run_map, Functor.map_map]
  change _ = id <$> (PqxdhRecordFactsPrivateCacheRandom.linked decode crypto key mode (.inl request)).run state
  rw [id_map]
  rfl

/-- Before a selected replay match, the local muted endpoint equals the actual erased endpoint on every retained field. -/
theorem local_raw (mode : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (bytes : Pqxdh.Bytes) (state : PqxdhRecordFactsPrivateCache.State)
    (noMatch : ∀ target, decode bytes = some target →
      AdaptiveCtxReplayDictionary.replayPlaintext (AdaptiveCtxSharedReplay.install state.1 ∅).ctx target = none) :
    (PqxdhRecordFactsOriginMute.impl mode decode crypto key (.inr bytes)).run state =
      (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inr bytes)).run state := by
  change (PqxdhRecordFactsOriginMute.raw decode bytes).run state = _
  rw [PqxdhRecordFactsOriginMute.raw_agrees decode bytes state noMatch]
  simp only [PqxdhRecordFactsPrivateCacheRandom.erased, PqxdhRecordFactsPrivateCacheRandom.modePointed,
    StateT.run_map]
  rfl


/-- The actual erased family request is its complete local endpoint installed through the source coordinate lens. -/
theorem erased_lens (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    (erasedKeyed modes decode crypto query).run state =
      ((localLens query.1).lift (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto
        (materialAt state.base.chain query.1).1 (modes query.1) query.2)).run state := by
  rw [PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run]
  rfl

/-- The exact failure condition before a selected-coordinate raw query can distinguish the two family handlers. -/
def NoReplay (decode : RawDecoder) (target : Label n) (query : (KeyedSpec n).Domain)
    (state : CtxPrivate n) : Prop :=
  ∀ bytes, query = (target, .inr bytes) → ∀ parsed, decode bytes = some parsed →
    AdaptiveCtxReplayDictionary.replayPlaintext (AdaptiveCtxSharedReplay.install (state.keys target) ∅).ctx parsed = none

/-- The muted family handler preserves the complete actual erased step until a selected replay match. -/
theorem keyed_agrees (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain)
    (state : CtxPrivate n) (noMatch : NoReplay decode target query state) :
    (keyed target modes decode crypto query).run state = (erasedKeyed modes decode crypto query).run state := by
  rcases query with ⟨label, query⟩
  by_cases selected : label = target
  · subst label
    simp only [keyed, StateT.run, ite_true]
    have localSame :
        (PqxdhRecordFactsOriginMute.impl (modes target) decode crypto
          (materialAt state.base.chain target).1 query).run ((localLens target).get state) =
        (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto
          (materialAt state.base.chain target).1 (modes target) query).run ((localLens target).get state) := by
      cases query with
      | inl request => exact local_nonraw (modes target) decode crypto _ request _
      | inr bytes => exact local_raw (modes target) decode crypto _ bytes _ (noMatch bytes rfl)
    have lifted := congrArg (fun work =>
      (fun result => (result.1, (localLens target).set state result.2)) <$> work) localSame
    exact lifted.trans (erased_lens modes decode crypto (target, query) state).symm
  · simp only [keyed, StateT.run, selected, ite_false]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.project_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.project_base

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.project_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.project_get

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.project_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.project_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.local_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.local_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.other_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.other_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.keyed_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.keyed_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.local_nonraw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.local_nonraw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.local_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.local_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.erased_lens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.erased_lens

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.keyed_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily.keyed_agrees
