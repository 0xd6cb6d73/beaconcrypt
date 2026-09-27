import BeaconcryptCore.Computational.LiveDecodedRecordEvents

/-!
The live source API is interpreted under two explicit receive capabilities. `openRaw` returns the actual optional source plaintext together with its original source metadata. `deliver` exposes only the success bit of that same source result; it is a separate network observation projection, not a replacement for the raw-opening capability. Both execute the original parser, ratchet, callback and publication exactly once. Sending returns the original optional encrypted record. No target plaintext is synthesized, and no successful callback is assumed.

An adaptive client is compiled to the original source calls. Equalities retain the whole source owner and primitive state and hold before evaluating any randomness. Private transcript instrumentation supplies the same chronological source requests and replies; its public projection retains the request mode. Cryptographic origin, a ProVerif process embedding and confidentiality freshness remain separate consumers. In particular, a successful `openRaw` discloses its returned plaintext and cannot be silently treated as an acceptance-only observation. No storage or restoration interface exists.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec BeaconcryptCore.Computational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.LivePublicObservation

inductive Request where
  | send (plaintext : Pqxdh.Bytes)
  | openRaw (raw : Pqxdh.Bytes)
  | deliver (raw : Pqxdh.Bytes)

def Reply : Request → Type
  | .send _ => Option RawCtxSourceSend.Encrypted
  | .openRaw _ => core.option.Option RawCtxWholeOwner.Decrypted
  | .deliver _ => Bool

abbrev PublicSpec : OracleSpec Request := Reply

def sourceRequest : Request → LiveOwnerSpec.Domain
  | .send plaintext => .inl plaintext
  | .openRaw raw => .inr raw
  | .deliver raw => .inr raw

def accepted : core.option.Option RawCtxWholeOwner.Decrypted → Bool
  | .None => false
  | .Some _ => true

def observe (request : Request) : LiveOwnerSpec.Range (sourceRequest request) → Reply request :=
  match request with
  | .send _ => id
  | .openRaw _ => id
  | .deliver _ => accepted

def lower : QueryImpl PublicSpec (OracleComp LiveOwnerSpec) := fun request =>
  observe request <$> (liftM (OracleSpec.query (sourceRequest request)) : OracleComp LiveOwnerSpec _)

def publicImpl {m : Type → Type} [Monad m] (source : QueryImpl LiveOwnerSpec m) :
    QueryImpl PublicSpec m := fun request => do
  let reply ← source (sourceRequest request)
  pure (observe request reply)

/-- The raw-opening capability retains the original optional source plaintext and metadata. -/
theorem open_reply (raw : Pqxdh.Bytes) (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    observe (.openRaw raw) reply = reply := rfl

/-- The network-only delivery capability exposes exactly success or failure of the same optional source reply. -/
theorem delivery_reply (raw : Pqxdh.Bytes) (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    observe (.deliver raw) reply = accepted reply := rfl

/-- One compiled public request performs one original call with its original bytes. -/
theorem lower_query {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : QueryImpl LiveOwnerSpec m) (request : Request) :
    simulateQ source (lower request) = publicImpl source request := by
  simp [lower, publicImpl]

/-- Every adaptive continuation sees precisely its declared response capability, while all source effects are retained. -/
theorem lower_client {m : Type → Type} [Monad m] [LawfulMonad m] {Result : Type}
    (source : QueryImpl LiveOwnerSpec m) (client : OracleComp PublicSpec Result) :
    simulateQ source (simulateQ lower client) = simulateQ (publicImpl source) client := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1

abbrev PrivateEntry := (request : Request) × LiveOwnerSpec.Range (sourceRequest request)
abbrev PrivateTranscript := List PrivateEntry
abbrev PublicEntry := (request : Request) × Reply request
abbrev PublicTranscript := List PublicEntry

def sourceTranscript (history : PrivateTranscript) : LiveOwnerTranscript :=
  history.map (fun entry => ⟨sourceRequest entry.1, entry.2⟩)

def publicTranscript (history : PrivateTranscript) : PublicTranscript :=
  history.map (fun entry => ⟨entry.1, observe entry.1 entry.2⟩)

def privateImpl {State ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base))) :
    QueryImpl PublicSpec (StateT (State × PrivateTranscript) (OracleComp base)) :=
  fun request state => do
    let result ← (source (sourceRequest request)).run state.1
    pure (observe request result.1, (result.2, state.2 ++ [⟨request, result.1⟩]))

def loggedPublicImpl {State ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base))) :
    QueryImpl PublicSpec (StateT (State × PublicTranscript) (OracleComp base)) :=
  fun request state => do
    let result ← (publicImpl source request).run state.1
    pure (result.1, (result.2, state.2 ++ [⟨request, result.1⟩]))

def project {State : Type} (state : State × PrivateTranscript) : State × PublicTranscript :=
  (state.1, publicTranscript state.2)

/-- Projecting a private source transcript preserves the exact public request/reply transcript and whole original state. -/
theorem private_query_projection {State ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (request : Request) (state : State × PrivateTranscript) :
    Prod.map id project <$> (privateImpl source request).run state =
      (loggedPublicImpl source request).run (project state) := by
  change Prod.map id project <$> (do
    let result ← source (sourceRequest request) state.1
    pure (observe request result.1, result.2, state.2 ++ [(⟨request, result.1⟩ : PrivateEntry)])) = (do
    let result ← (do
      let reply ← source (sourceRequest request) state.1
      pure (observe request reply.1, reply.2))
    pure (result.1, result.2, publicTranscript state.2 ++ [(⟨request, result.1⟩ : PublicEntry)]))
  simp [project, publicTranscript]

/-- The exact projection equation holds for every adaptive client before probabilistic evaluation. -/
theorem private_client_projection {State Result ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (client : OracleComp PublicSpec Result) (state : State × PrivateTranscript) :
    Prod.map id project <$> (simulateQ (privateImpl source) client).run state =
      (simulateQ (loggedPublicImpl source) client).run (project state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (private_query_projection source) client state

/-- Erasing private instrumentation preserves the full original source execution and every actual public reply. -/
theorem private_query_erasure {State ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (request : Request) (state : State × PrivateTranscript) :
    Prod.map id Prod.fst <$> (privateImpl source request).run state =
      (publicImpl source request).run state.1 := by
  change Prod.map id Prod.fst <$> (do
    let result ← source (sourceRequest request) state.1
    pure (observe request result.1, result.2, state.2 ++ [(⟨request, result.1⟩ : PrivateEntry)])) = (do
    let result ← source (sourceRequest request) state.1
    pure (observe request result.1, result.2))
  simp

/-- Private instrumentation erasure retains the complete adaptive decision and source poststate. -/
theorem private_client_erasure {State Result ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (client : OracleComp PublicSpec Result) (state : State × PrivateTranscript) :
    Prod.map id Prod.fst <$> (simulateQ (privateImpl source) client).run state =
      (simulateQ (publicImpl source) client).run state.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (private_query_erasure source) client state


/-- A private public-service run records exactly one complete source trace, in original order and with every actual optional reply. -/
theorem private_source_trace {Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp PublicSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) (history : PrivateTranscript)
    (result : Result × ((RawCtxWholeOwner.OwnerState Metadata × PrimitiveState) × PrivateTranscript))
    (actual : result ∈ support ((simulateQ
      (privateImpl (liveOwnerSourceImpl execute sealing opening sender decode)) client).run (state, history))) :
    ∃ suffix, result.2.2 = history ++ suffix ∧
      LiveOwnerSourceTrace execute sealing opening sender decode state (sourceTranscript suffix) result.2.1 := by
  induction client using OracleComp.inductionOn generalizing state history result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure] at actual
      cases actual
      exact ⟨[], by simp, .nil _⟩
  | query_bind request next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at actual
      obtain ⟨step, called, later⟩ := actual
      simp only [StateT.run, privateImpl, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at called
      obtain ⟨sourceStep, original, rfl⟩ := called
      obtain ⟨suffix, historyEq, trace⟩ := ih _ _ _ _ later
      refine ⟨⟨request, sourceStep.1⟩ :: suffix, ?_, .step (sourceRequest request) original trace⟩
      simpa [List.append_assoc] using historyEq


/-- Every supported public result has a private chronological source log on the same execution, with its unchanged complete source poststate. -/
theorem public_supported_private {State Result ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (client : OracleComp PublicSpec Result) (state : State) (result : Result × State)
    (actual : result ∈ support ((simulateQ (publicImpl source) client).run state)) :
    ∃ history, (result.1, (result.2, history)) ∈ support
      ((simulateQ (privateImpl source) client).run (state, [])) := by
  rw [← private_client_erasure source client (state, []), support_map, Set.mem_image] at actual
  obtain ⟨⟨value, post, history⟩, supported, rfl⟩ := actual
  exact ⟨history, supported⟩

/-- Private observation logging adds no primitive-oracle request; every underlying query class retains its actual full source bound. Local copying and projection are not runtime-free. -/
theorem private_query_bounds {State Result ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (client : OracleComp PublicSpec Result) (state : State × PrivateTranscript)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (privateImpl source) client).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (publicImpl source) client).run state.1).IsQueryBoundP predicate budget := by
  rw [← private_client_erasure source client state, isQueryBoundP_map_iff]

/-- One public adaptive source result supplies its own actual transcript and the complete existing live worker, without a hand-picked finite schedule. -/
theorem public_supported_worker {AD PT CT Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp PublicSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (token : LiveToken (LiveOwnerContext Metadata)) (represented : LiveOwnerRepresents sender state.1 token)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (actual : result ∈ support ((simulateQ
      (publicImpl (liveOwnerSourceImpl execute sealing opening sender decode)) client).run state)) :
    ∃ history after,
      (result.1, (result.2, history)) ∈ support ((simulateQ
        (privateImpl (liveOwnerSourceImpl execute sealing opening sender decode)) client).run (state, [])) ∧
      LiveOwnerSourceTrace execute sealing opening sender decode state (sourceTranscript history) result.2 ∧
      LiveOwnerRepresents sender result.2.1 after ∧
      LiveOwnerTrace (withInterpreter cr execute) sealing opening decode
        ((token, state.1.rawAttempts), state.2) (sourceTranscript history)
        ((after, result.2.1.rawAttempts), result.2.2) := by
  obtain ⟨history, supported⟩ := public_supported_private _ client state result actual
  obtain ⟨suffix, historyEq, trace⟩ := private_source_trace execute sealing opening sender decode
    client state [] (result.1, result.2, history) supported
  simp only [List.nil_append] at historyEq
  subst suffix
  obtain ⟨after, representedAfter, worker⟩ := live_owner_source_trace cr execute sealing opening sender decode trace token represented
  exact ⟨history, after, supported, trace, representedAfter, worker⟩


/-- The compiler preserves every requested source-call allowance; both raw modes count as a real receive attempt, including rejection. -/
theorem lower_budget {Result : Type} (client : OracleComp PublicSpec Result)
    (predicate : LiveOwnerSpec.Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : client.IsQueryBoundP (fun request => predicate (sourceRequest request)) budget) :
    (simulateQ lower client).IsQueryBoundP predicate budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, lower, bind_map_left]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun reply => ih _ _ (bounded.2 (observe request reply))⟩


/-- The actual fixed-source public execution yields matching private callback and request histories, decoded records and source-derived nonrepetition on that same live execution. -/
theorem source_supported_records {AD PT CT Metadata Auxiliary Result : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp PublicSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (token : LiveToken (LiveOwnerContext Metadata)) (represented : LiveOwnerRepresents sender state.1 token)
    (spent : List Nat)
    (invariant : RawCtxReceiveConsumption.ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (publicImpl (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode)) client).run state)) :
    ∃ history requests after,
      (result.1, ((result.2.1, (result.2.2, history)), requests)) ∈ support
        ((simulateQ (privateImpl (liveOwnerSourceImpl (RawCtxSourceHkdf.response source.crypto)
          (LiveRecordEvents.loggedSeal (LiveRecordEvents.sourceSealing source writer))
          (LiveRecordEvents.loggedOpen (LiveRecordEvents.sourceOpening source writer)) sender decode))
          client).run ((state.1, (state.2, [])), [])) ∧
      LiveOwnerSourceTrace (RawCtxSourceHkdf.response source.crypto)
        (LiveRecordEvents.sourceSealing source writer) (LiveRecordEvents.sourceOpening source writer)
        sender decode state (sourceTranscript requests) result.2 ∧
      LiveOwnerRepresents sender result.2.1 after ∧
      LiveOwnerTrace (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
        (LiveRecordEvents.loggedSeal (LiveRecordEvents.sourceSealing source writer))
        (LiveRecordEvents.loggedOpen (LiveRecordEvents.sourceOpening source writer)) decode
        ((token, state.1.rawAttempts), (state.2, [])) (sourceTranscript requests)
        ((after, result.2.1.rawAttempts), (result.2.2, history)) ∧
      LiveDecodedRecordEvents.decodedHistory decode history ∧
      LiveDecodedRecordEvents.openedPositions history = LiveDecodedRecordEvents.receivedPositions (sourceTranscript requests) ∧
      ((LiveDecodedRecordEvents.decodedOpenings history).map
        (fun observation => observation.record.sequence.val - 1)).Nodup ∧
      (∀ position ∈ LiveDecodedRecordEvents.openedPositions history, position ∉ spent) := by
  rw [← LiveRecordEvents.source_owner source writer sender decode, ← lower_client] at actual
  obtain ⟨history, logged⟩ := LiveRecordEvents.source_supported_history
    (RawCtxSourceHkdf.response source.crypto) (LiveRecordEvents.sourceSealing source writer)
    (LiveRecordEvents.sourceOpening source writer) sender decode (simulateQ lower client) state result actual
  rw [lower_client] at logged
  obtain ⟨requests, supported⟩ := public_supported_private _ client
    (state.1, (state.2, [])) (result.1, (result.2.1, (result.2.2, history))) logged
  obtain ⟨suffix, historyEq, trace⟩ := private_source_trace
    (RawCtxSourceHkdf.response source.crypto)
    (LiveRecordEvents.loggedSeal (LiveRecordEvents.sourceSealing source writer))
    (LiveRecordEvents.loggedOpen (LiveRecordEvents.sourceOpening source writer)) sender decode
    client (state.1, (state.2, [])) [] (result.1, ((result.2.1, (result.2.2, history)), requests)) supported
  simp only [List.nil_append] at historyEq
  subst suffix
  obtain ⟨after, representedAfter, worker⟩ := live_owner_source_trace cr
    (RawCtxSourceHkdf.response source.crypto)
    (LiveRecordEvents.loggedSeal (LiveRecordEvents.sourceSealing source writer))
    (LiveRecordEvents.loggedOpen (LiveRecordEvents.sourceOpening source writer)) sender decode trace token represented
  have original := LiveRecordEvents.source_trace_erasure (RawCtxSourceHkdf.response source.crypto)
    (LiveRecordEvents.sourceSealing source writer) (LiveRecordEvents.sourceOpening source writer) sender decode trace
  have consumed := LiveRecordEvents.source_trace_consumed source writer sendOrigin receiveOrigin sender decode
    original spent invariant
  refine ⟨history, requests, after, supported, original, representedAfter, worker, ?_, ?_, ?_, ?_⟩
  · exact LiveDecodedRecordEvents.worker_trace_decoded
      (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (LiveRecordEvents.sourceSealing source writer) (LiveRecordEvents.sourceOpening source writer)
      decode (by simp [LiveDecodedRecordEvents.decodedHistory]) worker
  · simpa [LiveDecodedRecordEvents.openedPositions] using LiveDecodedRecordEvents.worker_trace_positions
      (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (LiveRecordEvents.sourceSealing source writer) (LiveRecordEvents.sourceOpening source writer) decode worker
  · rw [LiveDecodedRecordEvents.decoded_openings_positions]
    exact LiveDecodedRecordEvents.worker_opened_nodup
      (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (LiveRecordEvents.sourceSealing source writer) (LiveRecordEvents.sourceOpening source writer)
      decode spent worker rfl consumed.spent_nodup
  · exact LiveDecodedRecordEvents.worker_opened_fresh
      (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (LiveRecordEvents.sourceSealing source writer) (LiveRecordEvents.sourceOpening source writer)
      decode spent worker rfl consumed.spent_nodup


/-- The same supported instrumented run has exactly its projected public request/reply transcript, including actual optional raw plaintext replies. -/
theorem private_supported_public {State Result ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (client : OracleComp PublicSpec Result) (state : State × PrivateTranscript)
    (result : Result × (State × PrivateTranscript))
    (actual : result ∈ support ((simulateQ (privateImpl source) client).run state)) :
    (result.1, project result.2) ∈ support
      ((simulateQ (loggedPublicImpl source) client).run (project state)) := by
  rw [← private_client_projection source client state, support_map, Set.mem_image]
  exact ⟨result, actual, rfl⟩

/-- Public observers receive the original adaptive result and public transcript, never the final private owner, chain, cache or primitive state. The equation holds before evaluating the underlying randomness. -/
theorem public_observation_eq {State Result ι : Type} {base : OracleSpec ι}
    (source : QueryImpl LiveOwnerSpec (StateT State (OracleComp base)))
    (client : OracleComp PublicSpec Result) (state : State) :
    (fun result => (result.1, publicTranscript result.2.2)) <$>
      (simulateQ (privateImpl source) client).run (state, []) =
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (loggedPublicImpl source) client).run (state, []) := by
  simpa [project, publicTranscript, Function.comp_def] using
    congrArg (fun program => (fun result => (result.1, result.2.2)) <$> program)
      (private_client_projection source client (state, []))

end BeaconcryptCore.Computational.LivePublicObservation

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.open_reply' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.open_reply

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.delivery_reply' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.delivery_reply

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.lower_query' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.lower_query

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.lower_client' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.lower_client

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.private_query_projection' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_query_projection

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.private_client_projection' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_client_projection

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.private_query_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_query_erasure

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.private_client_erasure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_client_erasure

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.private_source_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_source_trace

/-- info: 'BeaconcryptCore.Computational.LivePublicObservation.public_supported_private' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.public_supported_private

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.private_query_bounds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_query_bounds

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.public_supported_worker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.public_supported_worker

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.lower_budget' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.lower_budget

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.source_supported_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.source_supported_records

/-- info: 'BeaconcryptCore.Computational.LivePublicObservation.private_supported_public' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.private_supported_public

/--
info: 'BeaconcryptCore.Computational.LivePublicObservation.public_observation_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LivePublicObservation.public_observation_eq
