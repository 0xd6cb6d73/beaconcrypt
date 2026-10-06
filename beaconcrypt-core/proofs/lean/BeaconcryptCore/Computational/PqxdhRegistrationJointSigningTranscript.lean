-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptTrace

/-! Actual successful signing replies determine the ordinary message history. The projection keeps repeated signatures in chronological source order and ignores only non-signing observations; failed requests never become issued messages. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhDynamicIdentityPool
open PqxdhJointIdentityFamily PqxdhJointIdentityFreshness PqxdhDynamicIdentityRouting

/-- An ordinary source transcript observation issues a message only after an actual signing reply at this exact index. -/
def messageAt (index : Nat) (observation : Observation) : Option Pqxdh.Bytes :=
  match observation with
  | ⟨.inr (.service selected (.sign message)), some _⟩ => if selected = index then some message else none
  | _ => none

def messagesAt (index : Nat) (transcript : List Observation) : List Pqxdh.Bytes :=
  transcript.filterMap (messageAt index)

/-- Every chronological append preserves the entire prior signing history. -/
theorem append (index : Nat) (before after : List Observation) :
    messagesAt index (before ++ after) = messagesAt index before ++ messagesAt index after := by
  simp [messagesAt]

/-- A complete source signing block appends exactly prekey, one-time, PQ at its actual index; other identities' signing histories are unchanged. -/
theorem signed (primitives : Primitives) (seed : IdentitySeed) (index selected : Nat)
    (keys : Phase1KeyTuple) (state : SourceState) :
    messagesAt selected (PqxdhJointPhase1SourceWriter.signedState primitives seed index keys state).transcript =
      messagesAt selected state.transcript ++
        (if index = selected then PqxdhRegistrationJointIssuedAttempts.messages keys else []) := by
  rw [PqxdhJointPhase1SourceWriter.signedState_transcript, append]
  by_cases same : index = selected <;> simp [messagesAt, messageAt, same, PqxdhRegistrationJointIssuedAttempts.messages]

/-- The ordinary weak-EUF history and actual source transcript count the same successful signing reply, at the exact creation index. -/
theorem history_step {count : Nat} (target : Fin count) (query : DynamicSpec.Domain)
    (answer : DynamicSpec.Range query) (history : GlobalState count) :
    signedMessages ((historyUpdate count query answer history).histories target) =
      signedMessages (history.histories target) ++ (messageAt target.val ⟨query, answer⟩).toList := by
  rcases query with coin | request
  case inl => simp [historyUpdate, messageAt]
  case inr =>
    cases request
    case create => simp [historyUpdate, messageAt]
    case service index request =>
      by_cases valid : index < count
      · by_cases same : index = target.val <;> cases request <;> cases answer <;>
          simp [historyUpdate, valid, PqxdhJointIdentityEvents.publicUpdate, requestEvent,
            signedMessages, messageAt, Fin.ext_iff, same, eq_comm]
      · have different : index ≠ target.val := fun equal => valid (equal ▸ target.isLt)
        cases request <;> cases answer <;> simp [historyUpdate, valid, messageAt, different]
    case reveal index =>
      by_cases valid : index < count <;> cases answer <;>
        simp [historyUpdate, valid, PqxdhJointIdentityEvents.publicUpdate, messageAt]

/-- Every actual ordinary source query maintains equality between the weak-EUF message history and its retained successful signing replies. -/
theorem source_step (primitives : Primitives) {count : Nat} (target : Fin count)
    (query : DynamicSpec.Domain) (state : GlobalState count × SourceState)
    (result : DynamicSpec.Range query × (GlobalState count × SourceState))
    (exactLog : signedMessages (state.1.histories target) = messagesAt target.val state.2.transcript)
    (supported : result ∈ support ((sourceWithHistory count (lazyImpl primitives) query).run state)) :
    signedMessages (result.2.1.histories target) = messagesAt target.val result.2.2.transcript := by
  rw [sourceWithHistory_run] at supported
  obtain ⟨reply, member, returned⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ returned
  simp [history_step, exactLog, lazyImpl_transcript primitives query state.2 reply member, messagesAt]
  cases observed : messageAt target.val ⟨query, reply.1⟩ <;> simp [observed]

/-- Every complete adaptive ordinary program retains the same chronological message-history projection, including signing failures and later compromise. -/
theorem source_program {Result : Type} (primitives : Primitives) {count : Nat} (target : Fin count)
    (program : OracleComp DynamicSpec Result) (state : GlobalState count × SourceState)
    (result : Result × (GlobalState count × SourceState))
    (exactLog : signedMessages (state.1.histories target) = messagesAt target.val state.2.transcript)
    (supported : result ∈ support ((simulateQ (sourceWithHistory count (lazyImpl primitives)) program).run state)) :
    signedMessages (result.2.1.histories target) = messagesAt target.val result.2.2.transcript := by
  exact (PqxdhServerAuthExperiment.run_rel (sourceWithHistory count (lazyImpl primitives))
    (fun before after =>
      signedMessages (before.1.histories target) = messagesAt target.val before.2.transcript →
        signedMessages (after.1.histories target) = messagesAt target.val after.2.transcript)
    (fun _ previous => previous) (fun _ _ _ first second previous => second (first previous))
    (fun query before after member previous => source_step primitives target query before after previous member)
    program state result supported) exactLog

/-- The actual optional writer result and the chronological tuple ledger have exactly the same source-ordered signing-message extension. -/
theorem attempt_after {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option PqxdhJointGapDh.ScalarBytes)
    (pool : SourceState) (attempts : List Phase1KeyTuple)
    (exactLog : messagesAt index pool.transcript = PqxdhRegistrationJointIssuedAttempts.history attempts) :
    messagesAt index (PqxdhRegistrationJointAttemptTrace.after setup codec index owner generated pool attempts).1.2.transcript =
      PqxdhRegistrationJointIssuedAttempts.history
        (PqxdhRegistrationJointAttemptTrace.after setup codec index owner generated pool attempts).2 := by
  cases ready : PqxdhBeaconPhase1Publication.prepare owner generated
  case some prepared =>
    rw [(PqxdhRegistrationJointAttemptTrace.after_history setup codec index owner generated pool attempts prepared ready).1,
      (PqxdhRegistrationJointAttemptTrace.after_history setup codec index owner generated pool attempts prepared ready).2,
      signed, ite_eq_left rfl, exactLog, PqxdhRegistrationJointIssuedAttempts.history_append]
  case none =>
    simpa [PqxdhRegistrationJointAttemptTrace.after, PqxdhRegistrationJointBundle.after,
      PqxdhRegistrationJointAttemptTrace.issued, ready] using exactLog

/-- Source signing changes no other creation index's message history, even when public keys or signatures have equal bytes. -/
theorem attempt_other {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (index selected : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option PqxdhJointGapDh.ScalarBytes)
    (pool : SourceState) (different : index ≠ selected) :
    messagesAt selected (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).2.transcript =
      messagesAt selected pool.transcript := by
  cases ready : PqxdhBeaconPhase1Publication.prepare owner generated
  case some prepared =>
    simp only [PqxdhRegistrationJointBundle.after_history setup codec index owner generated pool prepared ready,
      signed, ite_eq_right different, List.append_nil]
  case none => simp only [PqxdhRegistrationJointBundle.after, ready]

end BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.append

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.signed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.signed

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.history_step' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.history_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.source_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.attempt_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.attempt_after

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.attempt_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointSigningTranscript.attempt_other
