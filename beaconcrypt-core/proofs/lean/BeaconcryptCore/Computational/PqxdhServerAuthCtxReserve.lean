import BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler
import BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds
import BeaconcryptCore.Computational.PqxdhServerAuthStopBudget
import BeaconcryptCore.Computational.RawCtxSelectedSendLedger

/-! The actual pending-token reservation supplies the unused selected seal endpoint throughout the complete stopped compiler. Full source state and optional adaptive replies are preserved; no additional security or honesty premise is introduced. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthPendingBudget
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {KemSK Result : Type}

abbrev Monitored (KemSK : Type) := (Local KemSK × Option Nat) × Component

/-- The actual pending-token reservation implies the selected seal endpoint is still unused. -/
def Valid (state : Monitored KemSK) : Prop :=
  ControlValid (fun localState : Local KemSK => localState.1) state.1 ∧
    (buildReserve state.1.1.1.1 state.1.2 = 1 → state.2.selected.1.usedNonces = [])

/-- The source comparison condition follows from the actual unique marked pending token and remaining reservation. -/
theorem valid_ready (query : ServerAuthSpec.Domain) (state : Monitored KemSK) (valid : Valid state) :
    PqxdhServerAuthCtxHandler.Ready query (state.1.1, state.2) := by
  cases query with
  | inl coin => trivial
  | inr query =>
      cases query with
      | build session payload =>
          intro marked pending
          apply valid.2
          rw [valid.1.1.unique session marked]
          cases found : state.1.1.1.1.pending session <;>
            simp_all only [buildReserve, slotWeight, Option.isSome_none, Bool.false_eq_true]
      | _ => trivial

/-- Every actually interpreted reply and complete local poststate is supported by the concrete executable with arbitrary component replies. -/
theorem evaluate_support (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Program KemSK Result) (state : State KemSK)
    (result : Result × State KemSK)
    (supported : result ∈ support ((evaluate source key read work).run state)) :
    (result.1, result.2.1) ∈ support (work.run state.1) := by
  simp only [evaluate, PqxdhServerAuthCtxNative.evaluate, PqxdhSelectedStateInterpreter.evaluate,
    StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  apply support_simulateQ_run'_subset
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
    (work.run state.1) state.2
  simp only [StateT.run'_eq, support_map, Set.mem_image]
  exact ⟨inner, reached, rfl⟩

/-- All actual nonsealing component work preserves the selected nonce ledger while retaining every local, cache and component effect. -/
theorem evaluate_nonseal (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : Program KemSK Result) (state : State KemSK)
    (bounded : (work.run state.1).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (result : Result × State KemSK)
    (supported : result ∈ support ((evaluate source key read work).run state)) :
    result.2.2.selected.1.usedNonces = state.2.selected.1.usedNonces := by
  simp only [evaluate, PqxdhServerAuthCtxNative.evaluate, PqxdhSelectedStateInterpreter.evaluate,
    StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RawCtxSelectedSendLedger.program_nonseal (RawCtxUniversalDecoder.decoder read) source.crypto key
    (work.run state.1) bounded state.2 inner reached

/-- A continuing actual checkpoint preserves an unused endpoint whenever a future selected build is still reserved. The operational bill and footprint are kept explicit for the concrete handler consumer. -/
theorem checkpoint_valid (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (query : ServerAuthSpec.Domain)
    (work : Program KemSK (Option (ServerAuthSpec.Range query))) (before : Monitored KemSK)
    (valid : Valid before)
    (bounded : (work.run before.1.1).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (buildBill query before.1.1.1))
    (result : Option (ServerAuthSpec.Range query) × State KemSK)
    (supported : result ∈ support ((evaluate source key read work).run (before.1.1, before.2)))
    (resources : ResourceStep query before.1.1.1.1 result.2.1.1.1)
    (marks : MarkStep query before.1.1.1 result.2.1.1)
    (reply answer : ServerAuthSpec.Range query)
    (continues : (checkpoint query before.1.1.1.1.sessions result.2.1.1.2.1 before.1.2 reply).1 = some answer) :
    Valid ((result.2.1,
      (checkpoint query before.1.1.1.1.sessions result.2.1.1.2.1 before.1.2 reply).2), result.2.2) := by
  have paid := checkpoint_budget false query before.1.1.1 result.2.1.1 before.1.2
    valid.1.1 valid.1.2 resources marks reply answer continues
  refine ⟨⟨paid.1, paid.2.1⟩, ?_⟩
  intro future
  have cap := buildReserve_le_one before.1.1.1.1 before.1.2
  have zero : buildBill query before.1.1.1 = 0 := by
    have bill := paid.2.2
    simp only [callbackBill, callbackReserve, Bool.false_eq_true, ite_false, future] at bill
    omega
  have preserved := evaluate_nonseal source key read work (before.1.1, before.2)
    (by simpa only [zero] using bounded) result supported
  rw [preserved]
  apply valid.2
  have bill := paid.2.2
  simp only [callbackBill, callbackReserve, Bool.false_eq_true, ite_false, future] at bill
  omega

/-- Reinstall the actual component cache without dropping the source monitor. -/
def project (state : Monitored KemSK) : HiddenState KemSK × Option Nat :=
  (PqxdhServerAuthCtxState.project (state.1.1, state.2), state.1.2)

/-- The original checkpoint observes the exact completed local callback, retaining the full component poststate even on refusal. -/
def observe (query : ServerAuthSpec.Domain) (before : Monitored KemSK)
    (result : Option (ServerAuthSpec.Range query) × State KemSK) :
    Option (ServerAuthSpec.Range query) × Monitored KemSK :=
  let after := PqxdhServerAuthCtxStop.observe
    (fun localState : Local KemSK => localState.1.1.sessions)
    (fun localState : Local KemSK => localState.1.2.1) query before.1 (result.1, result.2.1)
  (after.1, after.2, result.2.2)

/-- The literal stopped compiler executes the full callback before deciding whether its actual marks require stopping. -/
noncomputable def stopped (compiler : QueryImpl ServerAuthSpec (PqxdhServerAuthCtxBuild.Compiler KemSK)) :=
  PqxdhServerAuthCtxStop.stopped
    (fun localState : Local KemSK => localState.1.1.sessions)
    (fun localState : Local KemSK => localState.1.2.1) compiler

/-- Evaluating the executable monitor preserves the full underlying component transition and checkpoint, with no extra oracle work. -/
theorem stopped_evaluate (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (compiler : QueryImpl ServerAuthSpec (PqxdhServerAuthCtxBuild.Compiler KemSK))
    (query : ServerAuthSpec.Domain) (before : Monitored KemSK) :
    (PqxdhServerAuthCtxNative.evaluate source key read ((stopped compiler query).run)).run before =
      observe query before <$>
        (evaluate source key read (compiler query).run).run (before.1.1, before.2) := by
  change PqxdhSelectedStateInterpreter.pair <$> (simulateQ
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      ((stopped compiler query).run before.1)).run before.2 = _
  rw [stopped, stopped_step, simulateQ_map, StateT.run_map]
  simp only [evaluate, PqxdhServerAuthCtxNative.evaluate, StateT.run,
    PqxdhSelectedStateInterpreter.evaluate, Functor.map_map, PqxdhSelectedStateInterpreter.pair, observe]

/-- Restoring the shared cache commutes with the actual post-callback monitor, including outer component refusal. -/
theorem observe_project (query : ServerAuthSpec.Domain) (before : Monitored KemSK)
    (result : Option (ServerAuthSpec.Range query) × State KemSK) :
    Prod.map id project (observe query before result) =
      PqxdhServerAuthCtxStop.observe (fun state => state.1.1.sessions) (fun state => state.1.2.1)
        query (project before) (result.1, PqxdhServerAuthCtxState.project result.2) := by
  rcases result with ⟨_ | reply, after⟩ <;> rfl

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}

/-- The actual complete stopped handler has the original full source transition. Its unused-endpoint condition is discharged from the operational reservation invariant. -/
theorem stopped_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (key : RootOutput)
    (before : Monitored KemSK) (valid : Valid before) :
    Prod.map id project <$>
      (PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
        (stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run).run before =
      (sourceStopped setup codec checks context Q j
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query).run
          (project before) := by
  rw [stopped_evaluate]
  calc
    _ = PqxdhServerAuthCtxStop.observe (fun state => state.1.1.sessions) (fun state => state.1.2.1)
          query (project before) <$>
        Prod.map id PqxdhServerAuthCtxState.project <$>
          (evaluate setup.source key codec.frameRead
            (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run).run
              (before.1.1, before.2) := by
      simp only [Functor.map_map]
      congr 1
      funext result
      exact observe_project query before result
    _ = _ := by
      rw [PqxdhServerAuthCtxHandler.handler_source setup codec checks context rest Q j query key
        (before.1.1, before.2) (valid_ready query before valid)]
      simp only [project, sourceStopped_step, Functor.map_map, PqxdhServerAuthCtxStop.observe]
      rfl

/-- Full optional adaptive state projection needs its operational invariant only on continuing replies; rejected poststates are still projected exactly. -/
theorem optional_projection {Left Right : Type}
    (left : QueryImpl ServerAuthSpec (OptionT (StateT Left ProbComp)))
    (right : QueryImpl ServerAuthSpec (OptionT (StateT Right ProbComp)))
    (invariant : Left → Prop) (projection : Left → Right)
    (preserves : ∀ query state, invariant state →
      ∀ result ∈ support ((left query).run.run state), ∀ reply, result.1 = some reply → invariant result.2)
    (step : ∀ query state, invariant state →
      Prod.map id projection <$> (left query).run.run state = (right query).run.run (projection state))
    (client : OracleComp ServerAuthSpec Result) (state : Left) (valid : invariant state) :
    Prod.map id projection <$> (simulateQ left client).run.run state =
      (simulateQ right client).run.run (projection state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, map_bind]
      rw [← step query state valid, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result supported
      cases returned : result.1 with
      | none => simp only [returned, Option.elim_none, StateT.run_pure, map_pure, Prod.map, id_eq]
      | some reply =>
          simp only [returned, Prod.map, id_eq, Option.elim_some]
          exact ih reply result.2 (preserves query state valid result supported reply returned)

/-- Every continuing interpreted monitor step preserves the actual nonce reservation, using only executable footprints and attempted-seal bills. -/
theorem normal_valid (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (compiler : QueryImpl ServerAuthSpec (PqxdhServerAuthCtxBuild.Compiler KemSK))
    (normal : ∀ query state, ∀ result ∈ support ((compiler query).run.run state),
      ∀ reply, result.1 = some reply →
        ResourceStep query state.1.1 result.2.1.1 ∧ MarkStep query state.1 result.2.1)
    (calls : ∀ query state, ((compiler query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
      (buildBill query state.1))
    (query : ServerAuthSpec.Domain) (before : Monitored KemSK) (valid : Valid before)
    (result : Option (ServerAuthSpec.Range query) × Monitored KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxNative.evaluate source key read
      (stopped compiler query).run).run before))
    (answer : ServerAuthSpec.Range query) (continues : result.1 = some answer) : Valid result.2 := by
  rw [stopped_evaluate] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  cases returned : inner.1 with
  | none =>
      simp only [observe, PqxdhServerAuthCtxStop.observe, returned] at continues
      cases continues
  | some reply =>
      have actual := evaluate_support source key read (compiler query).run (before.1.1, before.2) inner reached
      obtain ⟨resources, marks⟩ := normal query before.1.1 (inner.1, inner.2.1) actual reply returned
      simpa only [observe, PqxdhServerAuthCtxStop.observe, returned] using
        checkpoint_valid source key read query (compiler query).run before valid (calls query before.1.1)
          inner reached resources marks reply answer
          (by simpa only [observe, PqxdhServerAuthCtxStop.observe, returned] using continues)

/-- Evaluation preserves the complete optional stopped continuation and both retained states. -/
theorem optional_evaluate {Aux : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder)
    (compiler : QueryImpl ServerAuthSpec (OptionT (PqxdhServerAuthCtxNative.Local Aux)))
    (client : OracleComp ServerAuthSpec Result) :
    PqxdhServerAuthCtxNative.evaluate source key read (simulateQ compiler client).run =
      (simulateQ (fun query => OptionT.mk
        (PqxdhServerAuthCtxNative.evaluate source key read (compiler query).run)) client).run := by
  rw [← RawCtxSelectedFamilyNonceCoupling.optional_client compiler client]
  rw [← RawCtxSelectedFamilyNonceCoupling.optional_client
    (fun query => OptionT.mk (PqxdhServerAuthCtxNative.evaluate source key read (compiler query).run)) client]
  exact PqxdhSelectedStateInterpreter.program _ _ _

/-- The complete actual stopped adaptive compiler preserves the original source reply and private state, with the unused-endpoint condition established by its own operational budget. -/
theorem program_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (key : RootOutput) (client : OracleComp ServerAuthSpec Result)
    (before : Monitored KemSK) (valid : Valid before) :
    Prod.map id project <$>
      (PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
        (simulateQ (stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) client).run).run before =
      ((simulateQ (sourceStopped setup codec checks context Q j
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))) client).run).run
          (project before) := by
  rw [optional_evaluate]
  apply optional_projection _ _ Valid project _ _ client before valid
  · exact normal_valid setup.source key codec.frameRead
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
      (PqxdhServerAuthCtxHandlerBounds.handler_footprint setup codec checks context rest Q j)
      (fun query state => (PqxdhServerAuthCtxHandlerBounds.handler_record_bills setup codec checks context rest Q j query state).1)
  · exact fun query state invariant => stopped_source setup codec checks context rest Q j query key state invariant

/-- The literal starting state retains the sampled context and gives the component its actual empty cache and ledgers. -/
def initial (setup : Setup baseSpec KemSK) (context : Context KemSK) : Monitored KemSK :=
  ((((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none),
    AdaptiveCtxDynamicKnownKeys.initialSource)

/-- Empty source annotations and the real component's initial ledger discharge the entire operational invariant. -/
theorem initial_valid (setup : Setup baseSpec KemSK) (context : Context KemSK) :
    Valid (initial setup context) := by
  exact ⟨PqxdhServerAuthCtxHandlerBounds.initial_control setup context, fun _ => rfl⟩

/-- Every original adaptive adversary starts the complete source comparison without a caller-supplied state, honesty or unused-endpoint premise. -/
theorem initial_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (key : RootOutput) (adversary : Adversary) :
    Prod.map id project <$>
      (PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
        (simulateQ (stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (adversary (contextInput setup false context))).run).run (initial setup context) =
      ((simulateQ (sourceStopped setup codec checks context Q j
        (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)))
        (adversary (contextInput setup false context))).run).run
          (((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false), none) := by
  exact program_source setup codec checks context rest Q j key
    (adversary (contextInput setup false context)) (initial setup context) (initial_valid setup context)

/-- The complete interpreted compiler has exactly the original stopped entry decision, including terminal refusal and the actual joint factor output. -/
theorem entry_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (key : RootOutput) (adversary : Adversary) :
    (fun result => stoppedDecision setup context Q j (Prod.map id project result)) <$>
      (PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
        (simulateQ (stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (adversary (contextInput setup false context))).run).run (initial setup context) =
      stoppedEntryDistinguisher setup codec checks adversary false Q j context
        (PqxdhServerAuthCtxMaterial.output key rest) := by
  rw [← Functor.map_map, initial_source]
  rfl

/-- The original unrestricted factor-side source and this complete stopped compiler have the same original authentication decision distribution. -/
theorem entry_event (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (key : RootOutput) (adversary : Adversary) :
    𝒟[entryDistinguisher setup codec checks adversary false Q j context
      (PqxdhServerAuthCtxMaterial.output key rest)] =
    𝒟[(fun result => stoppedDecision setup context Q j (Prod.map id project result)) <$>
      (PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
        (simulateQ (stopped (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (adversary (contextInput setup false context))).run).run (initial setup context)] := by
  rw [entry_source]
  exact PqxdhServerAuthCtxStop.entry_event setup codec checks adversary false Q j context _

end BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.valid_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.valid_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.evaluate_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.evaluate_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.evaluate_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.evaluate_nonseal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.checkpoint_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.checkpoint_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.stopped_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.stopped_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.observe_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.observe_project

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.stopped_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.stopped_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.optional_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.optional_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.normal_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.normal_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.optional_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.optional_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.initial_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.initial_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.initial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.initial_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.entry_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.entry_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.entry_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve.entry_event
