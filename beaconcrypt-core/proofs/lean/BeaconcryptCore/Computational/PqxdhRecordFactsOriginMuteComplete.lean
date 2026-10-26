-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFresh
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginLogs

/-! Full source-service projection of selected private copies and unused writer logs. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec hiddenOpening hiddenSealing)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsOriginLogs (clearPrivate clearCtx)
open PqxdhRecordFactsOriginMuteServices (interpreter IsTargetSealing)
open PqxdhRecordFactsOriginMuteFamily (keyed)
open PqxdhRecordFactsPrivateCacheFamily (localLens)
open CtxRomAuth AdaptiveCtxReceive LazyOracleDiscard
variable {n : Nat}

/-- The two projections commute because one changes only selected key copies and the other only source logs. -/
theorem project_commute (target : Label n) (state : CtxPrivate n) :
    clearCtx (PqxdhRecordFactsOriginMuteFamily.project target state) =
      PqxdhRecordFactsOriginMuteFamily.project target (clearCtx state) := rfl

/-- Remove selected dictionary/cache copies and both unused private frame logs, retaining every other field. -/
noncomputable def project (target : Label n) (state : CtxPrivate n) : CtxPrivate n :=
  clearCtx (PqxdhRecordFactsOriginMuteFamily.project target state)

/-- The complete projection is idempotent. -/
theorem project_idempotent (target : Label n) (state : CtxPrivate n) :
    project target (project target state) = project target state := by
  simp only [project, ← project_commute, PqxdhRecordFactsOriginMuteFamily.project_idempotent,
    PqxdhRecordFactsOriginLogs.clearCtx_idempotent]

/-- An arbitrary actual coordinate-local endpoint commutes with removing unused base frame logs. -/
theorem local_clear {X : Type} (label : Label n)
    (step : StateT PqxdhRecordFactsPrivateCache.State ProbComp X) (state : CtxPrivate n) :
    Prod.map id clearCtx <$> ((localLens label).lift step).run state =
      Prod.map id clearCtx <$> ((localLens label).lift step).run (clearCtx state) := by
  simp only [StateLens.lift, StateT.run, localLens, clearCtx, clearPrivate, Functor.map_map, Prod.map, id_eq]

/-- Every keyed callback, including the selected muted raw callback, retains all effects under log projection. -/
theorem keyed_clear (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (query : (KeyedSpec n).Domain)
    (state : CtxPrivate n) :
    Prod.map id clearCtx <$> (keyed target modes decode crypto query).run state =
      Prod.map id clearCtx <$> (keyed target modes decode crypto query).run (clearCtx state) := by
  by_cases selected : query.1 = target
  · simp only [keyed, StateT.run, selected, ite_true]
    exact local_clear target _ state
  · simp only [keyed, StateT.run, selected, ite_false]
    change Prod.map id clearCtx <$> (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto query).run state =
      Prod.map id clearCtx <$> (PqxdhRecordFactsPrivateCacheFamily.erasedKeyed modes decode crypto query).run (clearCtx state)
    rw [PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run, PqxdhRecordFactsPrivateCacheSource.erasedKeyed_run]
    simpa only [
      StateLens.lift, StateT.run, localLens, clearCtx, clearPrivate] using
      local_clear query.1 (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto
        (PqxdhRecordLiftIdeal.materialAt state.base.chain query.1).1 (modes query.1) query.2) state

/-- Exact adaptive projection from an idempotent state observation and literal per-query equality. -/
theorem program_projection {ι S X : Type} {spec : OracleSpec ι}
    (observe : S → S) (stable : ∀ state, observe (observe state) = observe state)
    (impl : QueryImpl spec (StateT S ProbComp))
    (step : ∀ query state, Prod.map id observe <$> (impl query).run state =
      Prod.map id observe <$> (impl query).run (observe state))
    (client : OracleComp spec X) (state : S) :
    Prod.map id observe <$> (simulateQ impl client).run state =
      Prod.map id observe <$> (simulateQ impl client).run (observe state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq, stable]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have factor (start : S) :
        (do let result ← (impl query).run start
            Prod.map id observe <$> (simulateQ impl (next result.1)).run result.2) =
          (do let result ← Prod.map id observe <$> (impl query).run start
              Prod.map id observe <$> (simulateQ impl (next result.1)).run result.2) := by
      rw [bind_map_left]
      exact bind_congr fun result => ih result.1 result.2
    rw [factor state, factor (observe state), step query state]

/-- Every adaptive coordinate program retains its actual result after removing unused base logs. -/
theorem keyed_program_clear {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp (KeyedSpec n) X)
    (state : CtxPrivate n) :
    Prod.map id clearCtx <$> (simulateQ (keyed target modes decode crypto) client).run state =
      Prod.map id clearCtx <$> (simulateQ (keyed target modes decode crypto) client).run (clearCtx state) :=
  program_projection clearCtx PqxdhRecordFactsOriginLogs.clearCtx_idempotent
    (keyed target modes decode crypto) (keyed_clear target modes decode crypto) client state

/-- The literal hidden-seal writer reply is independent of its prior write-only frame buffer. -/
theorem hidden_sealing_forget (writer : RawCtxMixedShared.Writer)
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    Prod.fst <$> (hiddenSealing writer table replace pending).run frames =
      Prod.fst <$> (hiddenSealing writer table replace pending).run [] := by
  unfold hiddenSealing
  split
  · simp only [StateT.run, map_bind]
    apply bind_congr
    intro reply
    cases reply <;> rfl
  · rfl

/-- After log projection, the hidden sealing service keeps exactly its operational writer reply and full remaining state. -/
theorem sealing_reduced (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n) :
    Prod.map id clearCtx <$> (interpreter target modes decode crypto base writer replace (.sealing pending)).run state =
      Prod.map id clearCtx <$> (simulateQ (keyed target modes decode crypto)
        (Prod.fst <$> (hiddenSealing writer state.base.chain replace pending).run [])).run state := by
  have same := congrArg (fun client => Prod.map id clearCtx <$>
    (simulateQ (keyed target modes decode crypto) client).run state)
    (hidden_sealing_forget writer state.base.chain replace pending state.base.pending)
  simp only [simulateQ_map, StateT.run_map] at same ⊢
  simpa only [interpreter, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, clearCtx, clearPrivate] using same

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual muted source service, including all native callbacks, is insensitive to unused base logs. -/
theorem service_clear (target : Label n) (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (state : CtxPrivate n) :
    Prod.map id clearCtx <$> (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace query).run state =
    Prod.map id clearCtx <$> (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace query).run (clearCtx state) := by
  cases query with
  | opening pending => exact keyed_program_clear target modes _ _ _ state
  | sealing pending =>
      rw [sealing_reduced, sealing_reduced]
      exact keyed_program_clear target modes _ _ _ state
  | _ =>
      exact PqxdhRecordFactsOriginLogs.base_clear (fun _ => true) setup codec _
        (by intros; simp) (by intros; simp) state

/-- All adaptive muted source continuations retain their actual replies after forgetting only unused base logs. -/
theorem program_clear {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (client : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) :
    Prod.map id clearCtx <$> (simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace) client).run state =
    Prod.map id clearCtx <$> (simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace) client).run (clearCtx state) :=
  program_projection clearCtx PqxdhRecordFactsOriginLogs.clearCtx_idempotent _
    (service_clear target modes setup codec replace) client state

/-- The complete adaptive source continuation is blind to both selected private copies and unused writer logs after the selected sealing request. -/
theorem program_project {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (client : OracleComp (ServiceSpec n) X) (noSeal : client.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) :
    Prod.map id (project target) <$> (simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace) client).run state =
    Prod.map id (project target) <$> (simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace) client).run (project target state) := by
  have keyLaw := congrArg (fun work => Prod.map id clearCtx <$> work)
    (PqxdhRecordFactsOriginMuteServices.program_project target modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace client noSeal state)
  have logLaw := congrArg (fun work => Prod.map id (PqxdhRecordFactsOriginMuteFamily.project target) <$> work)
    (program_clear target modes setup codec replace client (PqxdhRecordFactsOriginMuteFamily.project target state))
  simp only [Functor.map_map, Prod.map, id_eq, ← project_commute] at keyLaw logLaw
  exact keyLaw.trans logLaw

/-- Two actual initial states with identical retained fields induce the same entire projected adaptive continuation. -/
theorem program_congr {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (client : OracleComp (ServiceSpec n) X) (noSeal : client.IsQueryBoundP (IsTargetSealing target) 0)
    (left right : CtxPrivate n) (same : project target left = project target right) :
    Prod.map id (project target) <$> (simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace) client).run left =
    Prod.map id (project target) <$> (simulateQ (interpreter target modes (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec)
      codec.frameWrite replace) client).run right := by
  rw [program_project target modes setup codec replace client noSeal left,
    program_project target modes setup codec replace client noSeal right, same]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.project_commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.project_commute

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.project_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.project_idempotent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.local_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.local_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.keyed_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.keyed_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_projection' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.keyed_program_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.keyed_program_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.hidden_sealing_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.hidden_sealing_forget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.sealing_reduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.sealing_reduced

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.service_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.service_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_clear' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_clear

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteComplete.program_congr
