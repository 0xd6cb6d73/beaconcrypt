import BeaconcryptCore.Computational.RawCtxSourceSeal

/-!
# Source frame builder, optional serialization and conditional field provenance

The source sets ciphertext, sequence and sender in that order before its actual optional write-message callback. Ordinary functional setter and codec-library laws connect successful serialization to exact fields when the actual complete-input reader succeeds. Framing, root and payload access may reject, including resource limits; successful writing does not promise reader availability. No canonical wire encoding, byte injectivity, authentication or crypto property is assumed.

The builder expansion changes only the final writer argument in the native source interface. Complete adaptive send interpretation retains the actual optional API result, whole owner and full primitive state, with four separate qSend call caps. Actual source success then derives the pending/response-selected advanced kernel and decoded frame, keeping the same writer poststate. No active or honest-selected key premise is added. Local allocation/setter/serialization work is not free.

Builder memory, native Cap'n Proto setters/reader/serializer implementations, traversal and allocation behavior, compiler, slot/ownership and deployment correspondence remain explicit external or unfinished library boundaries. The functional outcome laws do not prove equal native parser-work/timing traces.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxFrameWriting

/-- Ordinary functional builder operations; allocation, native pointer representation and execution costs stay at the library boundary. -/
structure BuilderOps (Builder : Type) where
  newRoot : Builder
  setPayload : Builder → Pqxdh.Bytes → Builder
  setSequence : Builder → Std.U64 → Builder
  setSender : Builder → Std.U64 → Builder
  fields : Builder → RawCtxReceive.DecodedFrame

/-- Ordinary setter behavior on the builder's decoded fields, independent of any protocol security conclusion. -/
structure BuilderLaws {Builder : Type} (ops : BuilderOps Builder) : Prop where
  payload : ∀ builder bytes, ops.fields (ops.setPayload builder bytes) = { ops.fields builder with payload := bytes }
  sequence : ∀ builder value, ops.fields (ops.setSequence builder value) = { ops.fields builder with sequence := value }
  sender : ∀ builder value, ops.fields (ops.setSender builder value) = { ops.fields builder with sender := value }

/-- The protocol sets ciphertext, then sequence, then sender, in the exact native source order. -/
def build {Builder : Type} (ops : BuilderOps Builder) (frame : RawCtxReceive.DecodedFrame) : Builder :=
  let builder := ops.setPayload ops.newRoot frame.payload
  let builder := ops.setSequence builder frame.sequence
  ops.setSender builder frame.sender

/-- Source overwrite order determines all decoded fields regardless of initial builder contents. -/
theorem build_fields {Builder : Type} (ops : BuilderOps Builder) (laws : BuilderLaws ops)
    (frame : RawCtxReceive.DecodedFrame) : ops.fields (build ops frame) = frame := by
  simp only [build, laws.sender, laws.sequence, laws.payload]

/-- One actual serializer callback may fail and retains its full interpreter state. -/
abbrev SerializeSpec (Builder : Type) := Builder →ₒ Option Pqxdh.Bytes

def writeFrame {Builder : Type} (ops : BuilderOps Builder) (frame : RawCtxReceive.DecodedFrame) :
    OracleComp (SerializeSpec Builder) (Option Pqxdh.Bytes) :=
  (SerializeSpec Builder).query (build ops frame)

/-- Complete-input/getter compatibility permits parser, root and payload resource rejection. -/
def ReadableFields {Message Root : Type} (reader : RawCtxFrameDecoding.Reader Message Root)
    (fields : RawCtxReceive.DecodedFrame) (raw : Pqxdh.Bytes) : Prop :=
  ∀ message remaining, reader.readMessage raw = some (message, remaining) →
    remaining = [] ∧ ∀ root, reader.root message = some root →
      reader.sequence root = fields.sequence ∧ reader.keyId root = fields.sender ∧
      ∀ payload, reader.payload root = some payload → payload = fields.payload

/-- Ordinary codec compatibility on actual optional serializer replies; it does not assert reader availability or authenticity. -/
def SerializationContract {Builder Message Root PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι} (ops : BuilderOps Builder)
    (reader : RawCtxFrameDecoding.Reader Message Root)
    (impl : QueryImpl (SerializeSpec Builder) (StateT PrimitiveState (OracleComp base))) : Prop :=
  ∀ builder primitive raw finalState,
    (some raw, finalState) ∈ support ((impl builder).run primitive) →
      ReadableFields reader (ops.fields builder) raw

/-- The source writer forwards the actual fully populated builder and retains every optional result and complete state. -/
theorem writeFrame_run {Builder PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (ops : BuilderOps Builder)
    (impl : QueryImpl (SerializeSpec Builder) (StateT PrimitiveState (OracleComp base)))
    (frame : RawCtxReceive.DecodedFrame) (primitive : PrimitiveState) :
    (simulateQ impl (writeFrame ops frame)).run primitive = (impl (build ops frame)).run primitive := by
  simp [writeFrame, OracleSpec.query]

/-- Source setter order transports the generic codec law to the exact frame supplied by the protocol. -/
theorem writeFrame_readable {Builder Message Root PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι} (ops : BuilderOps Builder) (laws : BuilderLaws ops)
    (reader : RawCtxFrameDecoding.Reader Message Root)
    (impl : QueryImpl (SerializeSpec Builder) (StateT PrimitiveState (OracleComp base)))
    (contract : SerializationContract ops reader impl)
    (frame : RawCtxReceive.DecodedFrame) (primitive finalState : PrimitiveState) (raw : Pqxdh.Bytes)
    (hsupport : (some raw, finalState) ∈ support ((simulateQ impl (writeFrame ops frame)).run primitive)) :
    ReadableFields reader frame raw := by
  rw [writeFrame_run] at hsupport
  have readable := contract (build ops frame) primitive raw finalState hsupport
  simpa only [build_fields ops laws frame] using readable

/-- Successful full reading recovers the built fields without assuming that every written buffer is readable. -/
theorem readable_decode {Message Root : Type} (reader : RawCtxFrameDecoding.Reader Message Root)
    (fields actual : RawCtxReceive.DecodedFrame) (raw : Pqxdh.Bytes)
    (readable : ReadableFields reader fields raw)
    (hdecode : RawCtxFrameDecoding.decode reader raw = some actual) : actual = fields := by
  obtain ⟨message, root, hread, hroot, hpayload, hsender, hsequence⟩ :=
    RawCtxFrameDecoding.decode_success reader raw actual hdecode
  obtain ⟨hseq, hsid, hbytes⟩ := (readable message [] hread).2 root hroot
  have seq := hsequence.trans hseq
  have sid := hsender.trans hsid
  have payload := hbytes actual.payload hpayload
  cases actual
  cases fields
  simp only [RawCtxReceive.DecodedFrame.mk.injEq]
  exact ⟨seq, sid, payload⟩

/-- A successfully decoded output of the actual source writer has exactly its supplied protocol fields. -/
theorem writeFrame_decode {Builder Message Root PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι} (ops : BuilderOps Builder) (laws : BuilderLaws ops)
    (reader : RawCtxFrameDecoding.Reader Message Root)
    (impl : QueryImpl (SerializeSpec Builder) (StateT PrimitiveState (OracleComp base)))
    (contract : SerializationContract ops reader impl)
    (frame actual : RawCtxReceive.DecodedFrame) (primitive finalState : PrimitiveState) (raw : Pqxdh.Bytes)
    (hsupport : (some raw, finalState) ∈ support ((simulateQ impl (writeFrame ops frame)).run primitive))
    (hdecode : RawCtxFrameDecoding.decode reader raw = some actual) : actual = frame :=
  readable_decode reader frame actual raw
    (writeFrame_readable ops laws reader impl contract frame primitive finalState raw hsupport) hdecode

/-- The source wrapper invokes the actual serializer once; local builder/setter work remains separate. -/
theorem writeFrame_bound {Builder : Type} (ops : BuilderOps Builder) (frame : RawCtxReceive.DecodedFrame) :
    (writeFrame ops frame).IsTotalQueryBound 1 := by
  exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩

/-- The native interfaces keep KDF/AEAD/hash arguments unchanged and replace only the final frame view by its built message. -/
abbrev NativeSpec (Builder : Type) :=
  (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) +
    ((RawCtxSourceSeal.AeadInput →ₒ Option (Pqxdh.Bytes × Pqxdh.Bytes)) +
      ((Pqxdh.Bytes →ₒ Option Pqxdh.Bytes) + SerializeSpec Builder))

def nativeLift {Builder : Type} (ops : BuilderOps Builder) :
    QueryImpl RawCtxSourceSeal.NativeSpec (OracleComp (NativeSpec Builder))
  | .inl request => (NativeSpec Builder).query (.inl request)
  | .inr (.inl input) => (NativeSpec Builder).query (.inr (.inl input))
  | .inr (.inr (.inl bytes)) => (NativeSpec Builder).query (.inr (.inr (.inl bytes)))
  | .inr (.inr (.inr frame)) => (NativeSpec Builder).query (.inr (.inr (.inr (build ops frame))))

/-- None denotes the unchanged KDF service; Some names the three concrete sealing services. -/
def sourceKind : RawCtxSourceSeal.NativeSpec.Domain → Option RawCtxSourceSeal.CallKind
  | .inl _ => none
  | .inr query => some (RawCtxSourceSeal.callKind query)

def nativeKind {Builder : Type} : (NativeSpec Builder).Domain → Option RawCtxSourceSeal.CallKind
  | .inl _ => none
  | .inr (.inl _) => some .aead
  | .inr (.inr (.inl _)) => some .hash
  | .inr (.inr (.inr _)) => some .writer

/-- Expanding the source writer preserves every native query category and its count under all optional replies. -/
theorem nativeLift_bound {Builder Result : Type} (ops : BuilderOps Builder)
    (source : OracleComp RawCtxSourceSeal.NativeSpec Result) (kind : Option RawCtxSourceSeal.CallKind)
    (bound : Nat) (hbound : source.IsQueryBoundP (fun query => sourceKind query = kind) bound) :
    (simulateQ (nativeLift ops) source).IsQueryBoundP (fun query => nativeKind query = kind) bound := by
  apply RawCtxSourceOpen.simulate_bound (nativeLift ops) _ _ source bound hbound
  rintro (request | (input | (bytes | frame)))
  all_goals apply (isQueryBoundP_query_iff (spec := NativeSpec Builder)
    (p := fun query => nativeKind query = kind) _ _).2
  all_goals simp only [nativeKind, sourceKind, RawCtxSourceSeal.callKind]
  all_goals intro h
  all_goals simp [h]

/-- Exact builder expansion retains four separate qSend caps through every adaptive application continuation. -/
theorem nativeSchedule_bounds {Builder Metadata Result : Type} (ops : BuilderOps Builder)
    (senderId : Std.U64) (client : OracleComp RawCtxSourceSend.ApplicationSpec Result)
    (qSend : Nat) (hbound : client.IsTotalQueryBound qSend)
    (state : RawCtxWholeOwner.OwnerState Metadata) (kind : Option RawCtxSourceSeal.CallKind) :
    (simulateQ (nativeLift ops)
      ((simulateQ (RawCtxSourceSeal.nativeApplicationImpl senderId) client).run state)).IsQueryBoundP
        (fun query => nativeKind query = kind) qSend := by
  apply nativeLift_bound
  have hb := RawCtxSourceSeal.nativeSchedule_bounds senderId client qSend hbound state
  cases kind with
  | none =>
    convert hb.1 using 1
    funext query
    cases query <;> simp [sourceKind]
  | some kind =>
    convert hb.2 kind using 1
    funext query
    cases query <;> simp [sourceKind, RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate]

/-- Builder expansion and source scheduling share the same complete primitive interpreter and actual optional API replies. -/
theorem nativeSchedule_interpretation {Builder Metadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι} (ops : BuilderOps Builder)
    (impl : QueryImpl (NativeSpec Builder) (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (client : OracleComp RawCtxSourceSend.ApplicationSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    (simulateQ impl (simulateQ (nativeLift ops)
      ((simulateQ (RawCtxSourceSeal.nativeApplicationImpl senderId) client).run state))).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (RawCtxSourceSend.ownerImpl
          ((impl ∘ₛ nativeLift ops) ∘ₛ RawCtxSourceSeal.nativeAdapter) senderId) client).run
            (state, primitive) := by
  rw [← QueryImpl.simulateQ_compose, RawCtxSourceSeal.nativeSchedule_interpretation]

/-- The serializer is the actual final branch of the same native interpreter. -/
def serializerImpl {Builder PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl (NativeSpec Builder) (StateT PrimitiveState (OracleComp base))) :
    QueryImpl (SerializeSpec Builder) (StateT PrimitiveState (OracleComp base)) :=
  fun builder => impl (.inr (.inr (.inr builder)))

/-- The native source writer forwards the populated message into the same stateful serialization callback. -/
theorem nativeWriter_apply {Builder PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (ops : BuilderOps Builder)
    (impl : QueryImpl (NativeSpec Builder) (StateT PrimitiveState (OracleComp base)))
    (frame : RawCtxReceive.DecodedFrame) :
    (impl ∘ₛ nativeLift ops) (.inr (.inr (.inr frame))) =
      serializerImpl impl (build ops frame) := by
  simp [QueryImpl.compose, nativeLift, serializerImpl, OracleSpec.query]

/-- Actual successful source sending identifies the fields of every successfully decoded writer output and its final primitive state. -/
theorem sourceSend_decode {Builder Message Root PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι} (ops : BuilderOps Builder) (laws : BuilderLaws ops)
    (reader : RawCtxFrameDecoding.Reader Message Root)
    (impl : QueryImpl (NativeSpec Builder) (StateT PrimitiveState (OracleComp base)))
    (contract : SerializationContract ops reader (serializerImpl impl))
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (primitive : PrimitiveState)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ
      ((impl ∘ₛ nativeLift ops) ∘ₛ RawCtxSourceSeal.nativeAdapter ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send kernel context)).run primitive))
    (message : RawCtxSourceSend.Encrypted) (hsuccess : result.1.2 = some message)
    (actual : RawCtxReceive.DecodedFrame)
    (hdecode : RawCtxFrameDecoding.decode reader message.ciphertext = some actual) :
    ∃ pending response body tag commitment afterHash,
      pending.entry = kernel ∧ pending.context = context ∧
      result.1.1 = (RawCtxSourceSend.resumeSend pending response).advanced ∧
      let input := RawCtxSourceSend.arguments (RawCtxSourceSend.resumeSend pending response)
      message = RawCtxSourceSend.encrypted input message.ciphertext ∧
      actual = RawCtxSourceSeal.frame input body tag commitment ∧
      (some message.ciphertext, result.2) ∈ support
        ((serializerImpl impl (build ops (RawCtxSourceSeal.frame input body tag commitment))).run afterHash) := by
  obtain ⟨pending, response, afterKdf, hentry, hcontext, hinput, hinfo, hkdf, hadvance,
    body, tag, afterAead, commitment, afterHash, hmessage, haead, had, htag, hhash, hwriter⟩ :=
    RawCtxSourceSeal.send_success_primitives (impl ∘ₛ nativeLift ops) kernel context primitive result
      hsupport message hsuccess
  rw [nativeWriter_apply] at hwriter
  refine ⟨pending, response, body, tag, commitment, afterHash, hentry, hcontext, hadvance, hmessage, ?_, hwriter⟩
  apply readable_decode reader _ actual message.ciphertext _ hdecode
  simpa only [build_fields ops laws] using contract _ afterHash message.ciphertext result.2 hwriter

end BeaconcryptCore.Computational.RawCtxFrameWriting

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.build_fields' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.build_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_run' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_run

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_readable' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_readable

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.readable_decode' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.readable_decode

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_decode' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_decode

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_bound' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.writeFrame_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.nativeLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.nativeLift_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.nativeSchedule_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.nativeSchedule_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.nativeSchedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.nativeSchedule_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.nativeWriter_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.nativeWriter_apply

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameWriting.sourceSend_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameWriting.sourceSend_decode
