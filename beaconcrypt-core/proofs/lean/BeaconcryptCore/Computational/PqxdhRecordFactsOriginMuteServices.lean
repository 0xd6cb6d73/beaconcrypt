-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteFamily
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler

/-! Selected muted coordinate through the literal hidden services and arbitrary base-only work. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode KeyedSpec onBase hiddenOpening hiddenSealing)
open PqxdhRecordLiftProtocol (Private Service ServiceSpec)
open PqxdhRecordFactsOriginMuteFamily (project keyed IsTargetSeal)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat}

/-- Arbitrary base-only work keeps its actual reply and complete effects under the selected-key projection. -/
theorem onBase_project {X : Type} (target : Label n)
    (work : StateT (Private n) ProbComp X) (state : CtxPrivate n) :
    Prod.map id (project target) <$> (onBase work).run state =
      Prod.map id (project target) <$> (onBase work).run (project target state) := by
  simp only [onBase, StateT.run, Functor.map_map, Prod.map, id_eq,
    project, PqxdhRecordFactsPrivateCacheFamily.localLens, PqxdhRecordFactsOriginMute.project,
    Function.update_self, Function.update_idem]

/-- Hidden openings never invoke any sealing endpoint, including the selected coordinate. -/
theorem opening_noSeal (target : Label n)
    (seeds : PqxdhRecordLiftChainTable.Seeds (PqxdhRecordLiftInterface.Slot n))
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (pending : PqxdhRecordLiftProtocol.Opening n) :
    (hiddenOpening seeds table pending).IsQueryBoundP (IsTargetSeal target) 0 := by
  simp only [hiddenOpening]
  split
  · exact OracleComp.isQueryBoundP_pure _ _ _
  · split
    · exact OracleComp.isQueryBoundP_pure _ _ _
    · split
      · simp only [OracleComp.isQueryBoundP_map_iff, OracleComp.isQueryBoundP_query_iff,
          IsTargetSeal, AdaptiveCtxQueryBounds.SourceSeal, and_false, false_implies]
      · exact OracleComp.isQueryBoundP_pure _ _ _

/-- A hidden seal at another material coordinate cannot query the selected sealing endpoint. -/
theorem sealing_noSeal (target : Label n) (writer : RawCtxMixedShared.Writer)
    (table : PqxdhRecordLiftChainTable.Table (PqxdhRecordLiftInterface.Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (different : pending.material ≠ target) (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    ((hiddenSealing writer table replace pending).run frames).IsQueryBoundP (IsTargetSeal target) 0 := by
  simp only [hiddenSealing, StateT.run]
  split
  · simp only [OracleComp.isQueryBoundP_query_bind_iff, IsTargetSeal, different, false_and,
      not_false_eq_true, true_or, Nat.zero_sub, ite_self, true_and]
    intro reply
    cases reply <;> exact OracleComp.isQueryBoundP_pure _ _ _
  · exact OracleComp.isQueryBoundP_pure _ _ _

/-- Execute the unchanged service wiring, substituting only the selected muted family endpoint. -/
noncomputable def interpreter (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp)
  | .opening pending => fun state =>
      (simulateQ (keyed target modes decode crypto)
        (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run state
  | .sealing pending => fun state => do
      let result ← (simulateQ (keyed target modes decode crypto)
        ((hiddenSealing writer state.base.chain replace pending).run state.base.pending)).run state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })
  | query => onBase (base query)

/-- Only a hidden seal at the selected coordinate is excluded from the post-selection continuation. -/
def IsTargetSealing (target : Label n) : Service n → Prop
  | .sealing pending => pending.material = target
  | _ => False

noncomputable instance (target : Label n) : DecidablePred (IsTargetSealing target) := Classical.decPred _

/-- Exact projected opening law with the actual getters, optional reply, and complete remaining state. -/
theorem opening_project (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n) :
    Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace (.opening pending)).run state =
      Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace (.opening pending)).run (project target state) := by
  exact PqxdhRecordFactsOriginMuteFamily.program_project target modes decode crypto
    (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)
    (opening_noSeal target _ _ pending) state

/-- Buffer reinstallation commutes with projection of the selected private coordinate. -/
theorem pending_project (target : Label n) (state : CtxPrivate n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    project target { state with base := { state.base with pending := frames } } =
      { project target state with base := { (project target state).base with pending := frames } } := rfl

/-- A seal on another coordinate retains its literal writer reply and buffer under target projection. -/
theorem sealing_project (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (different : pending.material ≠ target)
    (state : CtxPrivate n) :
    Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace (.sealing pending)).run state =
      Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace (.sealing pending)).run (project target state) := by
  have whole := PqxdhRecordFactsOriginMuteFamily.program_project target modes decode crypto
    ((hiddenSealing writer state.base.chain replace pending).run state.base.pending)
    (sealing_noSeal target writer state.base.chain replace pending different state.base.pending) state
  have reinstall := congrArg (fun work =>
    (fun result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftLoggedAdapters.Frames) × CtxPrivate n =>
      (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) <$> work) whole
  simpa only [interpreter, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq,
    PqxdhRecordFactsOriginMuteFamily.project_base, pending_project] using reinstall

/-- Every source service except a later selected seal commutes with selected private-copy projection. -/
theorem service_project (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (query : Service n) (noSeal : ¬IsTargetSealing target query) (state : CtxPrivate n) :
    Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace query).run state =
      Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace query).run (project target state) := by
  cases query with
  | opening pending => exact opening_project target modes decode crypto base writer replace pending state
  | sealing pending => exact sealing_project target modes decode crypto base writer replace pending noSeal state
  | _ => exact onBase_project target _ state

/-- Arbitrary adaptive source-service continuations are blind to the selected private copies when they make no later selected sealing call. -/
theorem program_project {X : Type} (target : Label n) (modes : Label n → KeyMode)
    (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (base : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (writer : RawCtxMixedShared.Writer) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (work : OracleComp (ServiceSpec n) X) (noSeal : work.IsQueryBoundP (IsTargetSealing target) 0)
    (state : CtxPrivate n) :
    Prod.map id (project target) <$> (simulateQ (interpreter target modes decode crypto base writer replace) work).run state =
      Prod.map id (project target) <$> (simulateQ (interpreter target modes decode crypto base writer replace) work).run (project target state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply, id_eq,
      PqxdhRecordFactsOriginMuteFamily.project_idempotent]
  | query_bind query next ih =>
    simp only [OracleComp.isQueryBoundP_query_bind_iff, Nat.lt_irrefl, or_false,
      Nat.zero_sub, ite_self] at noSeal
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    have factor (start : CtxPrivate n) :
        (do let result ← (interpreter target modes decode crypto base writer replace query).run start
            Prod.map id (project target) <$> (simulateQ (interpreter target modes decode crypto base writer replace) (next result.1)).run result.2) =
          (do let result ← Prod.map id (project target) <$> (interpreter target modes decode crypto base writer replace query).run start
              Prod.map id (project target) <$> (simulateQ (interpreter target modes decode crypto base writer replace) (next result.1)).run result.2) := by
      rw [bind_map_left]
      apply bind_congr
      exact fun result => ih result.1 (noSeal.2 result.1) result.2
    rw [factor state, factor (project target state)]
    exact congrArg (fun work => work >>= fun result =>
      Prod.map id (project target) <$> (simulateQ (interpreter target modes decode crypto base writer replace) (next result.1)).run result.2)
      (service_project target modes decode crypto base writer replace query noSeal.1 state)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.onBase_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.onBase_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.opening_noSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.opening_noSeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.sealing_noSeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.sealing_noSeal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.opening_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.opening_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.pending_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.pending_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.sealing_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.sealing_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.service_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.service_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteServices.program_project
