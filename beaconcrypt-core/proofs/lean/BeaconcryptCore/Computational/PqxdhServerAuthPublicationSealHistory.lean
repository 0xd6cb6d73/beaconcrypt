import BeaconcryptCore.Computational.PqxdhServerAuthPublicationHandler

/-! The publication journal retains the exact ordinary selected-seal history in chronological occurrence order. This is a functional observer comparison, not an output secrecy assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory
open CtxRomAuth PqxdhJointKdfGame PqxdhFullSecretInputKdf
open RawCtxSelectedMessageSealing
open PqxdhServerAuthPublicationTrace (AnnotatedSpec erase)
open PqxdhServerAuthPublicationCutoff (Journal Observation journalImpl)

/-- Only a returned selected CTX record enters the ordinary seal history; writer results and annotation bytes do not reconstruct records. -/
def add (event : Observation) (before : List CtxSuccessfulSeal) : List CtxSuccessfulSeal :=
  match event with
  | .selectedSeal input (some record) => ⟨input, record⟩ :: before
  | _ => before

/-- Convert the chronological journal to the ordinary observer's newest-first record history, preserving repeated identical occurrences. -/
def produced (history : Journal) : List CtxSuccessfulSeal :=
  history.foldl (fun before event => add event before) []

/-- Appending a literal journal observation updates exactly the corresponding ordinary seal-history projection. -/
theorem produced_append (history : Journal) (event : Observation) :
    produced (history ++ [event]) = add event (produced history) := by
  simp only [produced, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Projecting the journal retains the exact ordinary selected-seal history through every adaptive annotated query. Actual optional replies are unchanged; the ordinary attempt history may be arbitrary. -/
theorem journal_monitor {Result : Type} (client : OracleComp AnnotatedSpec Result)
    (history : Journal) (observer : RawCtxSelectedAuthenticationObserver.State)
    (aligned : observer.seals = produced history) :
    (fun result => (result.1, produced result.2)) <$> (simulateQ journalImpl client).run history =
      (fun result => (result.1, result.2.seals)) <$>
        RawCtxSelectedAuthenticationObserver.monitor (simulateQ erase client) observer := by
  induction client using OracleComp.inductionOn generalizing history observer with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure,
        RawCtxSelectedAuthenticationObserver.monitor, aligned]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rcases query with ((((coin | (hash | input)) | raw) | known) | event)
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, erase]
        simp only [RawCtxSelectedAuthenticationObserver.monitor, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind]
        simp only [StateT.run, RawCtxSelectedAuthenticationObserver.handler, bind_assoc, pure_bind, map_bind]
        exact bind_congr fun reply => ih reply history _ aligned
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, erase]
        simp only [RawCtxSelectedAuthenticationObserver.monitor, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind]
        simp only [StateT.run, RawCtxSelectedAuthenticationObserver.handler, bind_assoc, pure_bind, map_bind]
        exact bind_congr fun reply => ih reply history _ aligned
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, erase]
        simp only [RawCtxSelectedAuthenticationObserver.monitor, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind]
        simp only [StateT.run, RawCtxSelectedAuthenticationObserver.handler, bind_assoc, pure_bind, map_bind]
        refine bind_congr fun reply => ?_
        apply ih reply (history ++ [Observation.selectedSeal input reply])
          (RawCtxSelectedAuthenticationObserver.step (.inl (.inl (.inr (.inr input)))) reply observer)
        cases reply <;> simp only [RawCtxSelectedAuthenticationObserver.step,
          produced_append, add, aligned]
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, erase]
        simp only [RawCtxSelectedAuthenticationObserver.monitor, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind]
        simp only [StateT.run, RawCtxSelectedAuthenticationObserver.handler, bind_assoc, pure_bind, map_bind]
        exact bind_congr fun reply => ih reply history _ aligned
      · simp only [journalImpl, StateT.run, bind_assoc, pure_bind, erase]
        simp only [RawCtxSelectedAuthenticationObserver.monitor, simulateQ_bind,
          simulateQ_spec_query, StateT.run_bind]
        simp only [StateT.run, RawCtxSelectedAuthenticationObserver.handler, bind_assoc, pure_bind, map_bind]
        exact bind_congr fun reply => ih reply history _ aligned
      · simp only [journalImpl, StateT.run, pure_bind, erase]
        exact ih () (history ++ [.annotation event]) observer
          (by simp only [produced_append, add, aligned])

/-- A lifted original component program has the same exact record history in the private journal and the ordinary all-attempt authentication observer. -/
theorem lifted_monitor {Result : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (history : Journal) (observer : RawCtxSelectedAuthenticationObserver.State)
    (aligned : observer.seals = produced history) :
    (fun result => (result.1, produced result.2)) <$>
      (simulateQ journalImpl (simulateQ PqxdhServerAuthPublicationTrace.liftDynamic work)).run history =
      (fun result => (result.1, result.2.seals)) <$>
        RawCtxSelectedAuthenticationObserver.monitor work observer := by
  simpa only [PqxdhServerAuthPublicationTrace.erase_lift] using
    journal_monitor (simulateQ PqxdhServerAuthPublicationTrace.liftDynamic work) history observer aligned

/-- Every new returned CTX record in the concrete sealing journal is from that same source pending request and its actual optional frame writer. Repeated identical earlier records remain an explicit alternative. -/
theorem sealing_provenance (crypto : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (pending : PqxdhServerAuthCtxSend.Pending) (before after : Journal)
    (result : Option (Option RawCtxSourceSend.Encrypted))
    (supported : (result, after) ∈ support ((simulateQ journalImpl
      (simulateQ PqxdhServerAuthPublicationTrace.liftDynamic
        (RawCtxSelectedSealConsumer.sealing crypto writer (PqxdhServerAuthCtxSend.sealing pending)))).run before))
    (entry : CtxSuccessfulSeal) (found : entry ∈ produced after) :
    entry ∈ produced before ∨
      ∃ (nonce : NonceOutput) (width : pending.context.associatedData.length = 281) (record : CtxRomRecord),
        pending.material = .hidden nonce ∧
        entry = ⟨selectedInput nonce pending.sequence pending.context width, record⟩ ∧
        result = some ((writer ⟨pending.sequence, pending.context.senderId, record.encode⟩).map
          (RawCtxInterpretedArguments.encrypted
            (RawCtxInterpretedArguments.sealArguments (PqxdhServerAuthCtxSend.sealing pending)))) := by
  let observer : RawCtxSelectedAuthenticationObserver.State := ⟨produced before, []⟩
  have projected : (result, produced after) ∈ support
      ((fun reply => (reply.1, produced reply.2)) <$>
        (simulateQ journalImpl (simulateQ PqxdhServerAuthPublicationTrace.liftDynamic
          (RawCtxSelectedSealConsumer.sealing crypto writer (PqxdhServerAuthCtxSend.sealing pending)))).run before) := by
    rw [support_map]
    exact ⟨(result, after), supported, rfl⟩
  rw [lifted_monitor _ before observer rfl, support_map] at projected
  obtain ⟨actual, reached, same⟩ := projected
  have replySame : actual.1 = result := congrArg Prod.fst same
  have sealsSame : actual.2.seals = produced after := congrArg Prod.snd same
  have origin := RawCtxSelectedSealReceipt.sealing_provenance crypto writer
    (PqxdhServerAuthCtxSend.sealing pending) observer actual.2 actual.1 reached entry
      (by rw [sealsSame]; exact found)
  rcases origin with earlier | ⟨nonce, width, record, hidden, receipt, returned, _⟩
  · exact Or.inl earlier
  · exact Or.inr ⟨nonce, width, record, hidden, receipt, replySame ▸ returned⟩

open PqxdhServerAuthExperiment (Codec Checks)
variable {Reader WireResponse Metadata PeerMetadata Consumed : Type}

/-- The completed actual annotated builder supplies every newly journaled record's source binding and frame origin. Existing journal records remain separate, including repeated equal tuples. The original optional result and complete old source log are retained. -/
theorem annotated_receipts (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader WireResponse)
    (checks : Checks) (rest : PqxdhServerAuthCtxCalls.Residual) (coordinate : Nat)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (beforeLog afterLog : PqxdhServerAuthBuildProgram.Log) (before after : Journal)
    (result : Option (RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)))
    (supported : ((result, afterLog), after) ∈ support ((simulateQ journalImpl
      (PqxdhServerAuthPublicationTrace.annotated source codec checks rest coordinate pending data metadata state beforeLog)).run before)) :
    beforeLog.IsPrefix afterLog ∧
      ∀ entry ∈ produced after, entry ∈ produced before ∨ ∃ context sequence,
        PqxdhPhase2LocalMatching.KeyIdBound context ∧
        PqxdhServerAuthBuildReceipt.FrameOrigin codec.frameWrite afterLog context sequence entry := by
  let observer : RawCtxSelectedAuthenticationObserver.State := ⟨produced before, []⟩
  have projected : ((result, afterLog), produced after) ∈ support
      ((fun reply => (reply.1, produced reply.2)) <$> (simulateQ journalImpl
        (PqxdhServerAuthPublicationTrace.annotated source codec checks rest coordinate pending data metadata state beforeLog)).run before) := by
    rw [support_map]
    exact ⟨((result, afterLog), after), supported, rfl⟩
  rw [journal_monitor _ before observer rfl, PqxdhServerAuthPublicationTrace.annotated_erase,
    support_map] at projected
  obtain ⟨actual, reached, same⟩ := projected
  have replySame : actual.1 = (result, afterLog) := congrArg Prod.fst same
  have sealsSame : actual.2.seals = produced after := congrArg Prod.snd same
  have receipts := PqxdhServerAuthBuildReceipt.compiled_receipts source codec checks rest
    pending data metadata state beforeLog actual.1.2 observer actual.2 actual.1.1 reached
  rw [replySame] at receipts
  exact ⟨receipts.1, fun entry found => receipts.2 entry (by rw [sealsSame]; exact found)⟩

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.produced_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.produced_append
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.journal_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.journal_monitor
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.lifted_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.lifted_monitor
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.sealing_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.sealing_provenance
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.annotated_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationSealHistory.annotated_receipts
