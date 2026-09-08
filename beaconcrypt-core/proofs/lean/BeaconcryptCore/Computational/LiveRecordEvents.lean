import BeaconcryptCore.Refinement.LiveSequenceOneOwner
import BeaconcryptCore.Computational.RawCtxReceiveConsumption

/-!
Private instrumentation of the actual source frame callbacks records the exact argument/reply pair after its complete original effects. These records retain native raw byte strings separately from their decoded frame context. Exact symbolic crypto_frame origin does not establish equality of arbitrary native wire encodings. A whole-frame None result may follow real inner AEAD/hash effects; its absence of a successful frame event does not erase those effects. These records are an input to the separately checked ideal primitive event projection; recording them establishes no primitive origin or source-to-ideal distribution law. Live source state and all optional failures remain unchanged. No storage or restoration service is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec BeaconcryptCore.Computational
open BeaconcryptCore.Refinement.RepresentationBridge
set_option autoImplicit false

namespace BeaconcryptCore.Computational.LiveRecordEvents

structure Record where
  key : Pqxdh.Bytes
  nonce : Pqxdh.Bytes
  associatedData : Pqxdh.Bytes
  sequence : Std.U64
  sender : Std.U64
  plaintext : Pqxdh.Bytes
  raw : Pqxdh.Bytes

inductive Call where
  | seal (input : RawCtxSourceSend.SealInput) (reply : Option Pqxdh.Bytes)
  | openFrame (input : RawCtxWholeOwner.OpenInput) (reply : core.option.Option Pqxdh.Bytes)

abbrev History := List Call

def sealed (input : RawCtxSourceSend.SealInput) (raw : Pqxdh.Bytes) : Record :=
  ⟨(absMaterial input.material).1, (absMaterial input.material).2, input.context.associatedData,
    input.sequence, input.context.senderId, input.context.plaintext, raw⟩

def opened (input : RawCtxWholeOwner.OpenInput) (plaintext : Pqxdh.Bytes) : Record :=
  ⟨(absMaterial input.material).1, (absMaterial input.material).2, input.context.associatedData,
    input.sequence, input.context.frame.sender, plaintext, input.context.raw⟩

inductive Event where
  | sealed (record : Record)
  | opened (record : Record)

def event : Call → Option Event
  | .seal input (.some raw) => some (.sealed (sealed input raw))
  | .openFrame input (.Some plaintext) => some (.opened (opened input plaintext))
  | _ => none

def loggedSeal {PrimitiveState ι : Type} {base : OracleSpec ι}
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (input : RawCtxSourceSend.SealInput) : StateT (PrimitiveState × History) (OracleComp base) (Option Pqxdh.Bytes) :=
  fun state => do
    let result ← sealing input state.1
    pure (result.1, (result.2, state.2 ++ [.seal input result.1]))

def loggedOpen {PrimitiveState ι : Type} {base : OracleSpec ι}
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (input : RawCtxWholeOwner.OpenInput) : StateT (PrimitiveState × History) (OracleComp base) (core.option.Option Pqxdh.Bytes) :=
  fun state => do
    let result ← opening input state.1
    pure (result.1, (result.2, state.2 ++ [.openFrame input result.1]))

def ownerProjection {Metadata PrimitiveState : Type}
    (state : RawCtxWholeOwner.OwnerState Metadata × (PrimitiveState × History)) :
    RawCtxWholeOwner.OwnerState Metadata × PrimitiveState := (state.1, state.2.1)

/-- Private seal-history erasure preserves every send-driver reply and complete original primitive state. -/
theorem send_program_erasure {PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (client : OracleComp RawCtxSourceSend.PrimitiveSpec Result) (state : PrimitiveState × History) :
    Prod.map id Prod.fst <$> (simulateQ (liveOwnerSendPrimitive execute (loggedSeal sealing)) client).run state =
      (simulateQ (liveOwnerSendPrimitive execute sealing) client).run state.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  cases query with
  | inl request =>
    change Prod.map id Prod.fst <$> (pure (execute request, current) : OracleComp base _) =
      pure (execute request, current.1)
    simp
  | inr input => simp [liveOwnerSendPrimitive, loggedSeal, StateT.run]

/-- Private open-history erasure preserves every receive-driver reply, including rejection effects. -/
theorem open_program_erasure {PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (client : OracleComp RawCtxWholeOwner.PrimitiveSpec Result) (state : PrimitiveState × History) :
    Prod.map id Prod.fst <$> (simulateQ (liveOwnerReceivePrimitive execute (loggedOpen opening)) client).run state =
      (simulateQ (liveOwnerReceivePrimitive execute opening) client).run state.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  cases query with
  | inl request =>
    change Prod.map id Prod.fst <$> (pure (execute request, current) : OracleComp base _) =
      pure (execute request, current.1)
    simp
  | inr input => simp [liveOwnerReceivePrimitive, loggedOpen, StateT.run]

/-- The original owner step changes neither API reply nor complete owner/primitive state when its private history is erased. -/
theorem owner_step_erasure {Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : LiveOwnerSpec.Domain)
    (state : RawCtxWholeOwner.OwnerState Metadata × (PrimitiveState × History)) :
    Prod.map id ownerProjection <$> (liveOwnerSourceImpl execute (loggedSeal sealing) (loggedOpen opening)
      sender decode query).run state =
      (liveOwnerSourceImpl execute sealing opening sender decode query).run (ownerProjection state) := by
  cases query with
  | inl plaintext =>
    simpa [liveOwnerSourceImpl, RawCtxSourceSend.ownerImpl, RawCtxSourceSend.sendGame,
      ownerProjection, StateT.run, Function.comp_def, bind_pure_comp] using
      congrArg (fun computation => (fun result => (result.1.1, result.1.2, result.2)) <$> computation)
        (send_program_erasure execute sealing ((RawCtxSourceSend.sendOwner sender plaintext).run state.1) state.2)
  | inr raw =>
    simpa [liveOwnerSourceImpl, RawCtxWholeOwner.ownerImpl, RawCtxWholeOwner.rawGame,
      ownerProjection, StateT.run, Function.comp_def, bind_pure_comp] using
      congrArg (fun computation => (fun result => (result.1.1, result.1.2, result.2)) <$> computation)
        (open_program_erasure execute opening ((RawCtxWholeOwner.rawReceive decode raw).run state.1) state.2)


/-- Erasure preserves the complete adaptive source client, including its original final result. -/
theorem owner_erasure {Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × (PrimitiveState × History)) :
    Prod.map id ownerProjection <$> (simulateQ
      (liveOwnerSourceImpl execute (loggedSeal sealing) (loggedOpen opening) sender decode) client).run state =
      (simulateQ (liveOwnerSourceImpl execute sealing opening sender decode) client).run (ownerProjection state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ ownerProjection
    (owner_step_erasure execute sealing opening sender decode) client state


/-- Every original supported result supplies an actual callback-history execution with the identical final states. -/
theorem source_supported_history {Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (actual : result ∈ support ((simulateQ (liveOwnerSourceImpl execute sealing opening sender decode) client).run state)) :
    ∃ history, (result.1, (result.2.1, (result.2.2, history))) ∈ support
      ((simulateQ (liveOwnerSourceImpl execute (loggedSeal sealing) (loggedOpen opening) sender decode)
        client).run (state.1, (state.2, []))) := by
  have erased := owner_erasure execute sealing opening sender decode client (state.1, (state.2, []))
  simp only [ownerProjection, Prod.mk.eta] at erased
  rw [← erased, support_map, Set.mem_image] at actual
  obtain ⟨⟨value, owner, primitive, history⟩, present, rfl⟩ := actual
  exact ⟨history, present⟩


/-- The recorded source trace projects to the same original typed transcript, not an independently selected witness. -/
theorem source_trace_erasure {Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    {initial final : RawCtxWholeOwner.OwnerState Metadata × (PrimitiveState × History)}
    {transcript : LiveOwnerTranscript}
    (trace : LiveOwnerSourceTrace execute (loggedSeal sealing) (loggedOpen opening) sender decode initial transcript final) :
    LiveOwnerSourceTrace execute sealing opening sender decode (ownerProjection initial) transcript (ownerProjection final) := by
  induction trace with
  | nil state => exact .nil _
  | @step state final query result rest actual tail ih =>
    refine .step query (result := Prod.map id ownerProjection result) ?_ ih
    rw [← owner_step_erasure execute sealing opening sender decode query state, support_map, Set.mem_image]
    exact ⟨result, actual, rfl⟩

/-- One original execution supplies both actual callback history and the matching source-derived Live40 trace. -/
theorem source_supported_live_history {AD PT CT Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
    (token : LiveToken (LiveOwnerContext Metadata)) (represented : LiveOwnerRepresents sender state.1 token)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState))
    (actual : result ∈ support ((simulateQ (liveOwnerSourceImpl execute sealing opening sender decode) client).run state)) :
    ∃ history transcript after,
      (result.1, (result.2.1, (result.2.2, history))) ∈ support
        ((simulateQ (liveOwnerSourceImpl execute (loggedSeal sealing) (loggedOpen opening) sender decode)
          client).run (state.1, (state.2, []))) ∧
      LiveOwnerSourceTrace execute (loggedSeal sealing) (loggedOpen opening) sender decode
        (state.1, (state.2, [])) transcript (result.2.1, (result.2.2, history)) ∧
      LiveOwnerSourceTrace execute sealing opening sender decode state transcript result.2 ∧
      LiveOwnerRepresents sender result.2.1 after ∧
      LiveOwnerTrace (withInterpreter cr execute) (loggedSeal sealing) (loggedOpen opening) decode
        ((token, state.1.rawAttempts), (state.2, [])) transcript
        ((after, result.2.1.rawAttempts), (result.2.2, history)) := by
  obtain ⟨history, supported⟩ := source_supported_history execute sealing opening sender decode client state result actual
  obtain ⟨transcript, after, trace, related, live⟩ := live_owner_supported_client cr execute
    (loggedSeal sealing) (loggedOpen opening) sender decode client (state.1, (state.2, []))
    token represented (result.1, (result.2.1, (result.2.2, history))) supported
  refine ⟨history, transcript, after, supported, trace, ?_, related, live⟩
  simpa only [ownerProjection, Prod.mk.eta] using
    source_trace_erasure execute sealing opening sender decode trace


/-- A recorded seal is exactly one original optional reply with its actual primitive poststate and chronological history extension. -/
theorem logged_seal_support {PrimitiveState ι : Type} {base : OracleSpec ι}
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (input : RawCtxSourceSend.SealInput) (state : PrimitiveState × History)
    (result : Option Pqxdh.Bytes × (PrimitiveState × History)) :
    result ∈ support ((loggedSeal sealing input).run state) ↔
      ∃ reply post, (reply, post) ∈ support ((sealing input).run state.1) ∧
        result = (reply, (post, state.2 ++ [.seal input reply])) := by
  simp [loggedSeal, StateT.run, eq_comm]

/-- A recorded open is exactly one original optional reply with its actual primitive poststate and chronological history extension. -/
theorem logged_open_support {PrimitiveState ι : Type} {base : OracleSpec ι}
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (input : RawCtxWholeOwner.OpenInput) (state : PrimitiveState × History)
    (result : core.option.Option Pqxdh.Bytes × (PrimitiveState × History)) :
    result ∈ support ((loggedOpen opening input).run state) ↔
      ∃ reply post, (reply, post) ∈ support ((opening input).run state.1) ∧
        result = (reply, (post, state.2 ++ [.openFrame input reply])) := by
  simp [loggedOpen, StateT.run, eq_comm]



/-- Every selected underlying query budget is unchanged; private history and byte processing remain local work. -/
theorem owner_query_bounds {Metadata PrimitiveState Result ι : Type} {base : OracleSpec ι}
    (execute : KdfInterpreter)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × (PrimitiveState × History))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ (liveOwnerSourceImpl execute (loggedSeal sealing) (loggedOpen opening) sender decode) client).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ (liveOwnerSourceImpl execute sealing opening sender decode) client).run (ownerProjection state)).IsQueryBoundP predicate budget := by
  rw [← owner_erasure execute sealing opening sender decode client state, isQueryBoundP_map_iff]


noncomputable def sourceSealing {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (Option Pqxdh.Bytes) :=
  (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxMixedOwner.sendAdapter) (.inr input)

noncomputable def sourceOpening {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxWholeOwner.OpenInput) : StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp (core.option.Option Pqxdh.Bytes) :=
  (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ
    RawCtxMixedOwner.receiveAdapter) (.inr input)

/-- The fixed-source send interpretation is the original shared native adapter, including its optional writer. -/
theorem source_send_primitive {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    liveOwnerSendPrimitive (RawCtxSourceHkdf.response source.crypto) (sourceSealing (Auxiliary := Auxiliary) source writer) =
      RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ RawCtxMixedOwner.sendAdapter := by
  funext query
  cases query with
  | inr input => rfl
  | inl request =>
    simp [liveOwnerSendPrimitive, QueryImpl.compose, RawCtxMixedOwner.sendAdapter,
      RawCtxSourceSeal.nativeAdapter, RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedImpl,
      RawCtxMixedShared.sharedAdapter]
    rfl


/-- The fixed-source receive interpretation is the original shared native adapter with the same CTX cache. -/
theorem source_open_primitive {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    liveOwnerReceivePrimitive (RawCtxSourceHkdf.response source.crypto) (sourceOpening (Auxiliary := Auxiliary) source writer) =
      RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) ∘ₛ RawCtxMixedOwner.receiveAdapter := by
  funext query
  cases query with
  | inr input => rfl
  | inl request =>
    simp [liveOwnerReceivePrimitive, QueryImpl.compose, RawCtxMixedOwner.receiveAdapter,
      RawCtxSourceOpen.nativeAdapter, RawCtxMixedOwner.receiveLift, RawCtxMixedShared.sharedImpl,
      RawCtxMixedShared.sharedAdapter]
    rfl

/-- Both original concrete callbacks discharge the full mixed-owner source equations internally. -/
theorem source_owner {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) :
    liveOwnerSourceImpl (Metadata := Metadata) (RawCtxSourceHkdf.response source.crypto)
      (sourceSealing (Auxiliary := Auxiliary) source writer) (sourceOpening source writer) sender decode =
      RawCtxMixedOwner.sourceImpl
        (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode := by
  funext query
  cases query <;> simp only [liveOwnerSourceImpl, RawCtxMixedOwner.sourceImpl, source_send_primitive, source_open_primitive]


def spentAfter : LiveOwnerTranscript → List Nat → List Nat
  | [], spent => spent
  | request :: rest, spent =>
      spentAfter rest (RawCtxReceiveConsumption.recordSource request.1 request.2 spent)

/-- The same actual typed transcript updates the previously proved source consumed-position invariant. -/
theorem source_trace_consumed {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    {initial final : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary}
    {transcript : LiveOwnerTranscript}
    (trace : LiveOwnerSourceTrace (RawCtxSourceHkdf.response source.crypto)
      (sourceSealing source writer) (sourceOpening source writer) sender decode initial transcript final)
    (spent : List Nat)
    (invariant : RawCtxReceiveConsumption.ConsumedRefines source.crypto sendOrigin receiveOrigin initial.1.owner.kernel spent) :
    RawCtxReceiveConsumption.ConsumedRefines source.crypto sendOrigin receiveOrigin final.1.owner.kernel
      (spentAfter transcript spent) := by
  induction trace generalizing spent with
  | nil state => exact invariant
  | @step state final query result rest actual tail ih =>
    rw [source_owner] at actual
    have recorded : (result.1, (result.2, RawCtxReceiveConsumption.recordSource query result.1 spent)) ∈ support
        ((RawCtxReceiveConsumption.trackedImpl source writer sender decode query).run (state, spent)) := by
      change _ ∈ support (do
        let next ← (RawCtxMixedOwner.sourceImpl
          (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode query).run state
        pure (next.1, (next.2, RawCtxReceiveConsumption.recordSource query next.1 spent)))
      rw [mem_support_bind_iff]
      exact ⟨result, actual, by simp⟩
    exact ih _ (RawCtxReceiveConsumption.tracked_step_spent source writer sendOrigin receiveOrigin
      sender decode query (state, spent) invariant _ recorded)


/-- One concrete source execution retains its callback history, Live40 transcript and source no-repeat invariant together. -/
theorem source_supported_consumption {AD PT CT Metadata Auxiliary Result : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (token : LiveToken (LiveOwnerContext Metadata)) (represented : LiveOwnerRepresents sender state.1 token)
    (spent : List Nat)
    (invariant : RawCtxReceiveConsumption.ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state)) :
    ∃ history transcript after,
      (result.1, (result.2.1, (result.2.2, history))) ∈ support
        ((simulateQ (liveOwnerSourceImpl (RawCtxSourceHkdf.response source.crypto)
          (loggedSeal (sourceSealing source writer)) (loggedOpen (sourceOpening source writer)) sender decode)
          client).run (state.1, (state.2, []))) ∧
      LiveOwnerSourceTrace (RawCtxSourceHkdf.response source.crypto)
        (sourceSealing source writer) (sourceOpening source writer) sender decode state transcript result.2 ∧
      LiveOwnerRepresents sender result.2.1 after ∧
      LiveOwnerTrace (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
        (loggedSeal (sourceSealing source writer)) (loggedOpen (sourceOpening source writer)) decode
        ((token, state.1.rawAttempts), (state.2, [])) transcript
        ((after, result.2.1.rawAttempts), (result.2.2, history)) ∧
      RawCtxReceiveConsumption.ConsumedRefines source.crypto sendOrigin receiveOrigin result.2.1.owner.kernel
        (spentAfter transcript spent) ∧ (spentAfter transcript spent).Nodup := by
  rw [← source_owner source writer sender decode] at actual
  obtain ⟨history, transcript, after, supported, _, trace, related, live⟩ :=
    source_supported_live_history cr (RawCtxSourceHkdf.response source.crypto)
      (sourceSealing source writer) (sourceOpening source writer) sender decode client state token represented result actual
  have consumed := source_trace_consumed source writer sendOrigin receiveOrigin sender decode trace spent invariant
  exact ⟨history, transcript, after, supported, trace, related, live, consumed, consumed.spent_nodup⟩


/-- Actual initialization and a real successful opening at one derive consumed position zero at the actual poststate. -/
theorem sequence_one_consumed {Metadata Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (root : Std.Array Std.U8 32#usize) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes)
    (state post : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (initialized : BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root (RawCtxSourceHkdf.initialResponse source.crypto) = ok state.1.owner.kernel)
    (message : RawCtxWholeOwner.Decrypted) (sequence : message.sequence = 1#u64)
    (actual : (.Some message, post) ∈ support ((RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
      sender decode (.inr raw)).run state)) :
    RawCtxReceiveConsumption.ConsumedRefines source.crypto state.1.owner.kernel.refined.send_chain
      state.1.owner.kernel.refined.receive_chain post.1.owner.kernel [0] := by
  rw [← source_owner source writer sender decode] at actual
  have trace : LiveOwnerSourceTrace (RawCtxSourceHkdf.response source.crypto)
      (sourceSealing source writer) (sourceOpening source writer) sender decode state
      [⟨.inr raw, .Some message⟩] post := .step (.inr raw) actual (.nil _)
  have consumed := source_trace_consumed source writer _ _ sender decode trace []
    (RawCtxReceiveConsumption.initialized_spent source.crypto root state.1.owner.kernel (.inl initialized))
  simpa [spentAfter, RawCtxReceiveConsumption.recordSource, RawCtxReceiveConsumption.recordReply, sequence] using consumed

end BeaconcryptCore.Computational.LiveRecordEvents

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.send_program_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.send_program_erasure

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.open_program_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.open_program_erasure

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.owner_step_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.owner_step_erasure

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.owner_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.owner_erasure

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_supported_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_supported_history

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_trace_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_trace_erasure

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_supported_live_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_supported_live_history

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.logged_seal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.logged_seal_support

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.logged_open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.logged_open_support

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.owner_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.owner_query_bounds

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_send_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_send_primitive

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_open_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_open_primitive

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_owner

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_trace_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_trace_consumed

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.source_supported_consumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.source_supported_consumption

/-- info: 'BeaconcryptCore.Computational.LiveRecordEvents.sequence_one_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveRecordEvents.sequence_one_consumed
