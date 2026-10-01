import BeaconcryptCore.Computational.PqxdhServerAuthPublicationResponseRecord
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationSingleBuild

/-! The actual one-build reservation also reserves an empty selected-record history. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthCtxState
open PqxdhServerAuthCtxStop PqxdhServerAuthPendingBudget PqxdhJointKdfGame PqxdhSecretInputKdf
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

abbrev Observed := RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState
abbrev Local (KemSK : Type) := PqxdhServerAuthCtxState.Local KemSK × Option Nat

/-- A still-available selected builder has no earlier selected record. Full observer and component states remain unchanged by this predicate. -/
def Reserved (state : Local KemSK) (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) state ∧
    (buildReserve state.1.1.1 state.2 = 1 → observer.seals = [])

/-- Every normal actual callback spends its immediate build bill and retains the literal remaining reservation. -/
theorem stopped_paid (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (before : Local KemSK) (valid : ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) before)
    (result : Option (ServerAuthSpec.Range query) × Local KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run before))
    (answer : ServerAuthSpec.Range query) (normal : result.1 = some answer) :
    ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) result.2 ∧
      buildBill query before.1.1 + buildReserve result.2.1.1.1 result.2.2 ≤ buildReserve before.1.1.1 before.2 := by
  simp only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped, OptionT.run_mk, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  cases reply : actual.1 with
  | none => simp only [observe, reply, reduceCtorEq] at normal
  | some value =>
      have footprint := PqxdhServerAuthCtxHandlerBounds.handler_footprint setup codec checks context rest Q j
        query before.1 actual reached value reply
      have paid := checkpoint_budget false query before.1.1 actual.2.1 before.2
        valid.1 valid.2 footprint.1 footprint.2 value answer
          (by simpa only [observe, reply] using normal)
      simpa only [ControlValid, observe, reply, callbackBill, callbackReserve, Bool.false_eq_true, ite_false] using
        (show (Tracked actual.2.1.2.1 (checkpoint query before.1.1.1.sessions actual.2.1.2.1 before.2 value).2 ∧
          Below actual.2.1) ∧ _ from ⟨⟨paid.1, paid.2.1⟩, paid.2.2⟩)

/-- The complete stopped callback makes at most its actual immediate selected-build bill, including work before component refusal. -/
theorem stopped_seal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain) (state : Local KemSK) :
    ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (buildBill query state.1.1) := by
  simpa only [PqxdhServerAuthCtxReserve.stopped, PqxdhServerAuthCtxStop.stopped, OptionT.run_mk, StateT.run, bind_pure_comp, isQueryBoundP_map_iff] using
    (PqxdhServerAuthCtxHandlerBounds.handler_record_bills setup codec checks context rest Q j query state.1).1

/-- Interpreting every actual component reply retains support in the unchanged executable callback. -/
theorem observed_support (source : FixedHkdfSha512NoSaltSource) (read : RawCtxReceive.FrameDecoder)
    (key : RootOutput) (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (before : Observed) (result : Result × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      work).run before)) : result.1 ∈ support work := by
  apply support_simulateQ_run'_subset
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder read) source.crypto key) work before
  simp only [StateT.run'_eq, support_map, Set.mem_image]
  exact ⟨result, supported, rfl⟩

/-- Any normal callback leaving a future selected build available has made no selected seal, so it preserves the empty reserved history. -/
theorem stopped_reserved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : Local KemSK) (before : Observed) (reserved : Reserved state before.1)
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)).run before))
    (answer : ServerAuthSpec.Range query) (normal : result.1.1 = some answer) :
    Reserved result.1.2 result.2.1 := by
  have paid := stopped_paid setup codec checks context rest Q j query state reserved.1 result.1
    (observed_support setup.source codec.frameRead key _ before result supported) answer normal
  refine ⟨paid.1, ?_⟩
  intro future
  have cap := buildReserve_le_one state.1.1.1 state.2
  have zero : buildBill query state.1.1 = 0 := by omega
  have same := PqxdhFirstBeaconRecordCanonical.observed_seals _ _ _ _
    (by simpa only [zero] using stopped_seal setup codec checks context rest Q j query state)
    before result supported
  rw [same]
  apply reserved.2
  omega

/-- Complete optional adaptive source execution preserves the empty-history reservation on every normal outcome. Refused paths retain their effects but have no normal continuation. -/
theorem program_reserved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : Local KemSK) (before : Observed) (reserved : Reserved state before.1)
    (result : (Option Result × Local KemSK) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state)).run before))
    (answer : Result) (normal : result.1.1 = some answer) : Reserved result.1.2 result.2.1 := by
  induction work using OracleComp.inductionOn generalizing state before with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact reserved
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      cases reply : middle.1.1 with
      | none =>
          simp only [reply, Option.elim_none, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at continued
          subst result
          cases normal
      | some value =>
          simp only [reply, Option.elim_some] at continued
          exact ih value middle.1.2 middle.2
            (stopped_reserved setup codec checks context rest key Q j query state before reserved middle reached value reply)
            continued

/-- The literal empty source state establishes the reservation for every sampled context. -/
theorem initial_reserved (setup : Setup baseSpec KemSK) (context : Context KemSK) :
    Reserved (PqxdhServerAuthCtxReserve.initial setup context).1 RawCtxSelectedAuthenticationObserver.initialState :=
  ⟨PqxdhServerAuthCtxHandlerBounds.initial_control setup context, fun _ => rfl⟩

/-- A reached present marked token is the unique reserved builder, so its actual earlier selected-record history is empty. -/
theorem selected_empty (state : Local KemSK) (observer : RawCtxSelectedAuthenticationObserver.State)
    (reserved : Reserved state observer) (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (marked : state.1.1.2.1 index = true) (present : state.1.1.1.pending index = some token) :
    observer.seals = [] := by
  apply reserved.2
  rw [reserved.1.1.unique index marked]
  simp only [buildReserve, present, slotWeight]

/-- A continuing selected build spends the entire one-build reservation, regardless of its native response or writer failures. -/
theorem selected_closed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (index : Nat) (payload : Option Pqxdh.Bytes)
    (state : Local KemSK)
    (valid : ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) state)
    (token : PqxdhServerRelatedRootConsumer.Returned) (marked : state.1.1.2.1 index = true)
    (present : state.1.1.1.pending index = some token)
    (result : Option (Option PqxdhServerRegistrationPublication.Response) × Local KemSK)
    (supported : result ∈ support ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
        (.inr (.build index payload))).run.run state))
    (answer : Option PqxdhServerRegistrationPublication.Response) (normal : result.1 = some answer) :
    ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) result.2 ∧
      buildReserve result.2.1.1.1 result.2.2 = 0 := by
  have paid := stopped_paid setup codec checks context rest Q j (.inr (.build index payload)) state valid
    result supported answer normal
  have cap := buildReserve_le_one state.1.1.1 state.2
  simp only [buildBill, marked, ite_true, present, slotWeight] at paid
  exact ⟨paid.1, by omega⟩

/-- Every adaptive suffix after the selected build has zero selected seals, including calls performed before any later refusal. -/
theorem program_nonseal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result) (state : Local KemSK)
    (valid : ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) state)
    (closed : buildReserve state.1.1.1 state.2 = 0) :
    ((simulateQ (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 := by
  have bounded := stopped_callback_bound (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1)
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
    (PqxdhServerAuthCtxHandlerBounds.handler_footprint setup codec checks context rest Q j) false
    (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal)
    (fun query state => (PqxdhServerAuthCtxHandlerBounds.handler_record_bills setup codec checks context rest Q j query state).1)
    work state valid
  simpa only [PqxdhServerAuthCtxReserve.stopped, callbackReserve, Bool.false_eq_true, ite_false, closed] using bounded

/-- The complete later source continuation preserves the exact selected-record list after the reservation is spent. No normal-return premise is needed for this suffix statement. -/
theorem suffix_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (state : Local KemSK) (before : Observed)
    (valid : ControlValid (fun localState : PqxdhServerAuthCtxState.Local KemSK => localState.1) state)
    (closed : buildReserve state.1.1.1 state.2 = 0)
    (result : (Option Result × Local KemSK) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run state)).run before)) :
    result.2.1.seals = before.1.seals :=
  PqxdhFirstBeaconRecordCanonical.observed_seals _ _ _ _
    (program_nonseal setup codec checks context rest Q j work state valid closed) before result supported

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.stopped_paid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.stopped_paid
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.stopped_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.stopped_seal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.observed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.observed_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.stopped_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.stopped_reserved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.program_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.program_reserved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.initial_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.initial_reserved
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.selected_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.selected_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.selected_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.selected_closed
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.program_nonseal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.program_nonseal
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.suffix_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationRecordReserve.suffix_records
