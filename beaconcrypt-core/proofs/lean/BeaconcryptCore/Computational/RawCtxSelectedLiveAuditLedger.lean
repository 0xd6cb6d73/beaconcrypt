import BeaconcryptCore.Computational.RawCtxSelectedRoleAuditLedger
import BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling

/-!
The same augmented source execution used for the selected-nonce comparison carries a chronological source-send ledger. Its complete roles, live disclosure history and component state are retained; private instrumentation changes no query or public reply.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedDriverAudit RawCtxSelectedRoleAuditLedger
open RawCtxSelectedFamilyNonceCoupling (Full Optional)
variable {A M P I D K Result : Type} {S B : Nat}

noncomputable def events (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B) : List (Event (RawCtxProtocolReveals.Owner S B)) :=
  match query with
  | .inl request => familyEvents prior parent target nonce next sender request entry.1
  | .inr _ => []

/-- Every new nonce in the actual augmented source callback belongs to its original source send trailer; the explicit refused branch retains the previous nonce ledger while executing the real source callback. -/
theorem step_used (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain)
    (before : Full M P I D K A S B)
    (result : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Range query × Full M P I D K A S B)
    (supported : result ∈ support ((RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read query).run before)) :
    UsedBy (events prior parent target nonce next sender query before.1) before.2.2 result.2.2.2 := by
  classical
  by_cases stopped : RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query before.1 before.2.2
  · simp only [RawCtxSelectedFamilyNonceCoupling.augmented, StateT.run, stopped, ite_true, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact fun _ used => Or.inl used
  · simp only [RawCtxSelectedFamilyNonceCoupling.augmented, StateT.run, stopped, ite_false] at supported
    cases query with
    | inl request =>
        simp only [RawCtxSelectedFamilyNonceCoupling.compiled, RawCtxSelectedFamilyLiveCompiler.impl,
          OptionT.run_mk, StateT.run, RawCtxSelectedReceiveCompiler.evaluated, simulateQ_map,
          Functor.map_map, support_map] at supported
        obtain ⟨reply, reached, rfl⟩ := supported
        change reply ∈ support ((RawCtxSelectedFamilyLiveCompiler.publish before.1 <$>
          simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
            (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read request before.1.1)).run before.2.2) at reached
        simp only [StateT.run_map, support_map] at reached
        obtain ⟨actual, original, equal⟩ := reached
        have state := congrArg Prod.snd equal
        dsimp only at state
        rw [← state]
        exact family_used source writer prior parent key target nonce next sender route read request before.1.1
          before.2.2 actual.2 actual.1 original
    | inr request =>
        simp only [RawCtxSelectedFamilyNonceCoupling.compiled, RawCtxSelectedFamilyLiveCompiler.impl,
          OptionT.run_mk, StateT.run, RawCtxSelectedReceiveCompiler.evaluated, simulateQ_pure] at supported
        subst result
        exact fun _ used => Or.inl used

abbrev State (M P I D K A : Type) (S B : Nat) :=
  List (Event (RawCtxProtocolReveals.Owner S B)) × Full M P I D K A S B

noncomputable def observed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (RawCtxProtocolReveals.SourceSpec S B)) (StateT (State M P I D K A S B) ProbComp) :=
  fun query before => (fun result => (result.1,
      (before.1 ++ events prior parent target nonce next sender query before.2.1, result.2))) <$>
    (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read query).run before.2

/-- The source event ledger changes no optional reply, role, disclosure history, primitive cache or component bookkeeping. -/
theorem erased_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain) (before : State M P I D K A S B) :
    Prod.map id Prod.snd <$> (observed source writer prior parent key target nonce next sender route read query).run before =
      (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read query).run before.2 := by
  simp only [observed, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  exact id_map _

/-- Every complete adaptive optional-interface program retains the exact augmented source execution after erasing only its source event ledger. -/
theorem erased_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Optional (RawCtxProtocolReveals.SourceSpec S B)) Result) (before : State M P I D K A S B) :
    Prod.map id Prod.snd <$> (simulateQ (observed source writer prior parent key target nonce next sender route read) client).run before =
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read) client).run before.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (erased_step source writer prior parent key target nonce next sender route read) client before

def Tracked (state : State M P I D K A S B) : Prop :=
  RawCtxSelectedSendTrace.Tracked state.2.2.2 (RawCtxSourceEventRecorder.seals state.1)

/-- The concrete augmented callback, including its refusal and hidden-disclosure paths, preserves actual nonce provenance in the retained source ledger. -/
theorem step_tracked (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain) (before : State M P I D K A S B)
    (result : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Range query × State M P I D K A S B)
    (supported : result ∈ support ((observed source writer prior parent key target nonce next sender route read query).run before))
    (previous : Tracked before) : Tracked result.2 := by
  simp only [observed, StateT.run, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact tracked _ before.1 before.2.2.2 reply.2.2.2
    (step_used source writer prior parent key target nonce next sender route read query before.2 reply reached) previous

/-- The full adaptive original source schedule retains a previous actual source occurrence for every selected nonce in its reached component ledger. -/
theorem program_tracked (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Optional (RawCtxProtocolReveals.SourceSpec S B)) Result) (before : State M P I D K A S B)
    (result : Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (observed source writer prior parent key target nonce next sender route read) client).run before))
    (previous : Tracked before) : Tracked result.2 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact previous
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact ih reply.1 reply.2 result tail
        (step_tracked source writer prior parent key target nonce next sender route read query before reply reached previous)

/-- Projecting this exact event-ledger run recovers the complete original hidden-disclosure-stopped source schedule used by the nonce comparison. -/
theorem source_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (before : State M P I D K A S B) :
    (fun result => (result.1, RawCtxSelectedFamilyNonceCoupling.project result.2.2)) <$>
      (simulateQ (observed source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient client)).run before =
      ((simulateQ (RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run
          (RawCtxSelectedFamilyNonceCoupling.project before.2) := by
  have same := congrArg (fun work => Prod.map id RawCtxSelectedFamilyNonceCoupling.project <$> work)
    (erased_program source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client) before)
  rw [RawCtxSelectedFamilyNonceCoupling.augmented_client] at same
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same

/-- The ordinary empty selected-nonce ledger supplies the invariant directly, under arbitrary existing source roles, private state and shared cache. -/
theorem initial_tracked (before : Full M P I D K A S B)
    (empty : before.2.2.selected.1.usedNonces = []) : Tracked ([], before) :=
  RawCtxSelectedSendTrace.tracked_empty before.2.2 empty

/-- Every retained selected nonce after the complete adaptive source program has an actual earlier source send occurrence, starting from the empty selected ledger. -/
theorem initial_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (before : Full M P I D K A S B)
    (empty : before.2.2.selected.1.usedNonces = [])
    (result : Option Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (observed source writer prior parent key target nonce next sender route read)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client)).run ([], before))) :
    ∀ value ∈ result.2.2.2.2.selected.1.usedNonces,
      ∃ occurrence, Event.sealing occurrence ∈ result.2.1 ∧ RawCtxSelectedSendTrace.nonce occurrence.pending = some value := by
  have retained := program_tracked source writer prior parent key target nonce next sender route read
    (RawCtxSelectedFamilyNonceCoupling.optionalClient client) ([], before) result supported (initial_tracked before empty)
  intro value used
  obtain ⟨occurrence, found, same⟩ := retained value used
  exact ⟨occurrence, (RawCtxSourceEventRecorder.mem_seals _ _).mp found, same⟩

/-- The full source-event instrumentation preserves the exact uniform-query allowance of the same augmented adaptive run. -/
theorem uniform_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : State M P I D K A S B) (budget : Nat) :
    ((simulateQ (observed source writer prior parent key target nonce next sender route read) client).run before).IsTotalQueryBound budget ↔
      ((simulateQ (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read) client).run before.2).IsTotalQueryBound budget := by
  rw [← erased_program source writer prior parent key target nonce next sender route read client before]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

/-- An actual nonce refusal in the live source has an earlier recorded send and the current original send with the same selected nonce. No equality of their public IDs or distinctness of event values is assumed. -/
theorem stopped_pair (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : State M P I D K A S B) (previous : Tracked before)
    (stopped : RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query before.2.1 before.2.2.2) :
    ∃ value earlier current, Event.sealing earlier ∈ before.1 ∧
      Event.sealing current ∈ events prior parent target nonce next sender query before.2.1 ∧
      RawCtxSelectedSendTrace.nonce earlier.pending = some value ∧
      RawCtxSelectedSendTrace.nonce current.pending = some value := by
  cases query with
  | inr request => exact False.elim stopped
  | inl request =>
      obtain ⟨value, current, found, selected, used⟩ := family_stopped prior parent target nonce next sender request before.2.1.1 before.2.2.2 stopped
      obtain ⟨earlier, old, same⟩ := previous value used
      exact ⟨value, earlier, current, (RawCtxSourceEventRecorder.mem_seals _ _).mp old, found, same, selected⟩

/-- After any actually executed original source prefix, its next nonce-refusing request has a matching pair of source send occurrences from the same retained run. -/
theorem reached_pair (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (before : Full M P I D K A S B)
    (empty : before.2.2.selected.1.usedNonces = []) (result : Option Result × State M P I D K A S B)
    (supported : result ∈ support ((simulateQ (observed source writer prior parent key target nonce next sender route read)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client)).run ([], before)))
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (stopped : RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender query result.2.2.1 result.2.2.2.2) :
    ∃ value earlier current, Event.sealing earlier ∈ result.2.1 ∧
      Event.sealing current ∈ events prior parent target nonce next sender query result.2.2.1 ∧
      RawCtxSelectedSendTrace.nonce earlier.pending = some value ∧
      RawCtxSelectedSendTrace.nonce current.pending = some value := by
  exact stopped_pair prior parent target nonce next sender query result.2
    (program_tracked source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client) ([], before) result supported (initial_tracked before empty)) stopped

end BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.step_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.step_used
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.erased_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.erased_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.erased_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.erased_program
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.step_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.step_tracked
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.program_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.program_tracked
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.source_program
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.initial_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.initial_tracked
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.initial_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.initial_program
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.uniform_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.uniform_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.stopped_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.stopped_pair
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.reached_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger.reached_pair
