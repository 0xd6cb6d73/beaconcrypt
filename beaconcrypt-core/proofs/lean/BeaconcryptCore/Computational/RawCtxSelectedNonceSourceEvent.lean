import BeaconcryptCore.Computational.RawCtxSelectedLiveAuditLedger

/-!
The actual selected-nonce refusal event is charged to two positions in the same chronological source send history. Equal event values are retained as separate occurrences; nonce equality under unrelated keys is not included.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedDriverAudit
open RawCtxSelectedLiveAuditLedger
open RawCtxSelectedFamilyNonceCoupling (Full Optional marked nonceBad)
variable {Owner A M P I D K Result : Type} {S B : Nat}

noncomputable def values (history : List (Event Owner)) : List NonceOutput :=
  (RawCtxSourceEventRecorder.seals history).filterMap (fun occurrence => RawCtxSelectedSendTrace.nonce occurrence.pending)

def Repeated (history : List (Event Owner)) : Prop := ¬ (values history).Nodup

/-- Nonce membership is attributed to a sealing occurrence in the literal source history, including its pending material. -/
theorem mem_values (history : List (Event Owner)) (value : NonceOutput) :
    value ∈ values history ↔ ∃ occurrence, Event.sealing occurrence ∈ history ∧
      RawCtxSelectedSendTrace.nonce occurrence.pending = some value := by
  simp only [values, List.mem_filterMap, RawCtxSourceEventRecorder.mem_seals]

/-- Appending source events preserves their chronological nonce multiplicity. -/
theorem values_append (earlier later : List (Event Owner)) :
    values (earlier ++ later) = values earlier ++ values later := by
  simp only [values, RawCtxSourceEventRecorder.seals, List.filterMap_append]

/-- A shared selected nonce in an earlier history and the current source trailer gives two positions in their concatenation, even if the occurrence values are equal. -/
theorem repeated_pair (earlier later : List (Event Owner)) (value : NonceOutput)
    (old current : RawCtxSelectedSendTrace.Occurrence Owner)
    (oldFound : Event.sealing old ∈ earlier) (currentFound : Event.sealing current ∈ later)
    (oldNonce : RawCtxSelectedSendTrace.nonce old.pending = some value)
    (currentNonce : RawCtxSelectedSendTrace.nonce current.pending = some value) :
    Repeated (earlier ++ later) := by
  intro unique
  rw [values_append, List.nodup_append] at unique
  exact unique.2.2 value ((mem_values earlier value).mpr ⟨old, oldFound, oldNonce⟩)
    value ((mem_values later value).mpr ⟨current, currentFound, currentNonce⟩) rfl

/-- Later callbacks cannot remove a repeated selected nonce from the chronological source history. -/
theorem repeated_append (earlier later : List (Event Owner)) (repeated : Repeated earlier) :
    Repeated (earlier ++ later) := by
  intro unique
  rw [values_append, List.nodup_append] at unique
  exact repeated unique.1

/-- An actual refusing request, or an already repeated history, leaves a repeated source nonce in the same callback's complete poststate. -/
theorem step_repeated (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain)
    (before : State M P I D K A S B)
    (result : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Range query × State M P I D K A S B)
    (supported : result ∈ support ((observed source writer prior parent key target nonce next sender route read query).run before))
    (previous : Tracked before)
    (hit : Repeated before.1 ∨ nonceBad prior parent target nonce next sender query before.2) :
    Repeated result.2.1 := by
  simp only [RawCtxSelectedLiveAuditLedger.observed, StateT.run, support_map] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rcases hit with old | current
  · exact repeated_append _ _ old
  · obtain ⟨value, earlier, current, oldFound, currentFound, oldNonce, currentNonce⟩ :=
      stopped_pair prior parent target nonce next sender query before previous current
    exact repeated_pair _ _ value earlier current oldFound currentFound oldNonce currentNonce

noncomputable def observedBad (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain) (state : State M P I D K A S B) : Prop :=
  nonceBad prior parent target nonce next sender query state.2

def Consistent (state : State M P I D K A S B × Bool) : Prop :=
  Tracked state.1 ∧ (state.2 = true → Repeated state.1.1)

/-- The actual sticky refusal flag implies repeated selected source nonce occurrences, while preserving the complete provenance invariant. -/
theorem marked_step_consistent (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain)
    (before : State M P I D K A S B × Bool)
    (result : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Range query × (State M P I D K A S B × Bool))
    (supported : result ∈ support ((marked (observed source writer prior parent key target nonce next sender route read)
      (observedBad prior parent target nonce next sender) query).run before))
    (previous : Consistent before) : Consistent result.2 := by
  classical
  simp only [marked, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  refine ⟨step_tracked source writer prior parent key target nonce next sender route read query before.1 reply reached previous.1, ?_⟩
  intro flagged
  apply step_repeated source writer prior parent key target nonce next sender route read query before.1 reply reached previous.1
  rcases Bool.or_eq_true_iff.mp flagged with old | current
  · exact Or.inl (previous.2 old)
  · exact Or.inr (of_decide_eq_true current)

/-- Every adaptive source continuation retains the refusal-to-source-event implication, including optional rejection and arbitrary final decisions. -/
theorem marked_program_consistent (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : State M P I D K A S B × Bool) (result : Result × (State M P I D K A S B × Bool))
    (supported : result ∈ support ((simulateQ
      (marked (observed source writer prior parent key target nonce next sender route read)
        (observedBad prior parent target nonce next sender)) client).run before))
    (previous : Consistent before) : Consistent result.2 := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact previous
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, reached, tail⟩ := supported
      exact ih reply.1 reply.2 result tail
        (marked_step_consistent source writer prior parent key target nonce next sender route read query before reply reached previous)

def forgetHistory (state : State M P I D K A S B × Bool) : Full M P I D K A S B × Bool :=
  (state.1.2, state.2)

/-- Erasing only the source event history preserves the actual marked callback, including its complete source state and refusal flag. -/
theorem marked_step_erased (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (RawCtxProtocolReveals.SourceSpec S B)).Domain)
    (before : State M P I D K A S B × Bool) :
    Prod.map id forgetHistory <$> (marked (observed source writer prior parent key target nonce next sender route read)
      (observedBad prior parent target nonce next sender) query).run before =
      (marked (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read)
        (nonceBad prior parent target nonce next sender) query).run (forgetHistory before) := by
  simp only [marked, RawCtxSelectedLiveAuditLedger.observed, observedBad, forgetHistory, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

/-- The exact original nonce game is recovered after erasing the event history from the complete adaptive marked execution. -/
theorem marked_program_erased (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : State M P I D K A S B × Bool) :
    Prod.map id forgetHistory <$> (simulateQ
      (marked (observed source writer prior parent key target nonce next sender route read)
        (observedBad prior parent target nonce next sender)) client).run before =
      (simulateQ
        (marked (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read)
          (nonceBad prior parent target nonce next sender)) client).run (forgetHistory before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ forgetHistory
    (marked_step_erased source writer prior parent key target nonce next sender route read) client before

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The original selected-nonce refusal probability is bounded with coefficient one by repeated selected nonce occurrences in the same source execution. No nonce uniqueness or independence premise is added. -/
theorem nonce_event_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Optional (RawCtxProtocolReveals.SourceSpec S B)) Result)
    (before : Full M P I D K A S B) (empty : before.2.2.selected.1.usedNonces = []) :
    𝒟[(fun result => result.2.2) <$> (simulateQ
      (marked (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read)
        (nonceBad prior parent target nonce next sender)) client).run (before, false)] {true} ≤
      𝒟[(fun result => decide (Repeated result.2.1)) <$>
        (simulateQ (observed source writer prior parent key target nonce next sender route read) client).run ([], before)] {true} := by
  have flags := congrArg (fun work => (fun result => result.2.2) <$> work)
    (marked_program_erased source writer prior parent key target nonce next sender route read client (([], before), false))
  simp only [Functor.map_map, Prod.map_def, id_eq, forgetHistory] at flags
  rw [← flags]
  have histories := congrArg (fun work => (fun result => decide (Repeated result.2.1)) <$> work)
    (RawCtxSelectedFamilyNonceCoupling.marked_client
      (observed source writer prior parent key target nonce next sender route read)
      (observedBad prior parent target nonce next sender) client (([], before), false))
  simp only [Functor.map_map, Prod.map_def, id_eq] at histories
  rw [← histories]
  repeat rw [← prEvent_eq_evalDist_singleton _ true]
  simp only [prEvent_map, decide_eq_true_eq]
  apply prEvent_mono_of_support
  intro result supported flagged
  exact (marked_program_consistent source writer prior parent key target nonce next sender route read client
    (([], before), false) result supported ⟨initial_tracked before empty, fun impossible => False.elim (Bool.false_ne_true impossible)⟩).2 flagged

/-- The complete native source-to-executable CTX comparison charges this actual chronological source event once. Its probability remains to be bounded using source origins and chain derivations. -/
theorem executable_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (before : Full M P I D K A S B) (empty : before.2.2.selected.1.usedNonces = []) :
    discreteDistance
      (((simulateQ (RawCtxSelectedMessageStopping.stopping
        (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run
        (RawCtxSelectedFamilyNonceCoupling.project before))
      ((fun result => (result.1.1, RawCtxSelectedFamilyNonceCoupling.project (result.1.2, result.2))) <$>
        (RawCtxSelectedReceiveCompiler.evaluated source key read
          (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before.1)).run before.2) ≤
      (𝒟[(fun result => decide (Repeated result.2.1)) <$>
        (simulateQ (observed source writer prior parent key target nonce next sender route read)
          (RawCtxSelectedFamilyNonceCoupling.optionalClient client)).run ([], before)] {true}).toReal := by
  apply (RawCtxSelectedFamilyNonceCoupling.executable_distance source writer prior parent key target nonce next sender route read client before).trans
  apply ENNReal.toReal_mono
  · rw [← prEvent_eq_evalDist_singleton _ true]
    exact prEvent_ne_top _
  · exact nonce_event_bound source writer prior parent key target nonce next sender route read
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client) before empty

end BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.mem_values' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.mem_values
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.values_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.values_append
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.repeated_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.repeated_pair
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.repeated_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.repeated_append
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.step_repeated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.step_repeated
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_step_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_step_consistent
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_program_consistent
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_step_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_step_erased
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_program_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.marked_program_erased
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.nonce_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.nonce_event_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.executable_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNonceSourceEvent.executable_distance
