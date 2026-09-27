import BeaconcryptCore.Computational.RawCtxCanonicalSeal
import BeaconcryptCore.Computational.RawCtxFrameWriting
import BeaconcryptCore.Computational.LiveRecordEvents

/-!
The actual frame writer targets an in-memory Vec. Its ordinary library contract has no normal error after bounded builder construction. This module consumes that contract on source-produced protected payloads, retaining the actual shared hash cache and the exact returned bytes. Native allocation/panic behavior and codec implementation remain external. Reader availability is deliberately not assumed: successfully decoded publication recovers the supplied fields under the existing conditional getter contract.

These are operational publication results, not cryptographic origin assumptions. The source-selected material may alias other material. No frame is inserted into a receive target, no inner seal is silently renamed as an API send, and no wire canonicalization or source-to-ProVerif theorem is asserted.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec BeaconcryptCore.Refinement.RepresentationBridge
open BeaconcryptCore.Refinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSourcePublication
open CtxRomAuth RawCtxCanonicalSeal

/-- Cap'n Proto Data lists contain fewer than 2^29 byte elements. This is a codec size bound, not an application admission check. -/
def dataLimit : Nat := 2 ^ 29

/-- Ordinary detached ChaCha20-Poly1305 preserves the plaintext's byte length in its body. -/
def BodyLength (c : Pqxdh.Crypto) : Prop :=
  ∀ key nonce ad plaintext, (c.aeadSeal key nonce ad plaintext).1.length = plaintext.length

/-- The actual normal-return writer returns its actual encoded bytes on bounded Data fields. Allocation/panic behavior is outside this contract. -/
def WritesOn (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) : Prop :=
  ∀ frame, frame.payload.length < dataLimit → writer frame = some (encode frame)

/-- Ordinary conditional codec field preservation on bounded encodings. The reader may still reject the buffer. -/
def ReadsOn {Message Root : Type} (reader : RawCtxFrameDecoding.Reader Message Root)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) : Prop :=
  ∀ frame, frame.payload.length < dataLimit →
    RawCtxFrameWriting.ReadableFields reader frame (encode frame)

/-- The source payload contains its unchanged body, tag16 and commitment64. -/
def admitted (input : RawCtxSourceSend.SealInput) : Prop :=
  input.context.plaintext.length + 80 < dataLimit

/-- On a bounded source input the actual optional writer cannot hide a completed inner CTX seal. The full shared cache and all auxiliary state are identical. -/
theorem shared_publication {Auxiliary : Type} (c : Pqxdh.Crypto)
    (lengths : BodyLength c) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (bounded : admitted input) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (sharedImpl c writer kdf) (RawCtxSourceSeal.sealInput input)).run (auxiliary, cache) = (do
      let result ← (simulateQ ctxRandomOracle
        (ctxSeal c (sourceKey input) (sourceInput input had))).run cache
      pure (some (encode (recordFrame input result.1)), (auxiliary, result.2))) := by
  rw [shared_seal c writer kdf input had auxiliary cache]
  simp only [ctxSeal, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  apply bind_congr
  intro result
  rw [writes]
  change ∀ key nonce ad plaintext, _ at lengths
  simpa [admitted, recordFrame, CtxRomRecord.encode, CtxRomRecord.toRecordCipher,
    Pqxdh.RecordCipher.encode, lengths, c.aeadSeal_tag_length, sourceInput, Nat.add_assoc] using bounded

/-- The actual source callback is the existing canonical shared interpreter on every input, including invalid width. -/
theorem source_shared {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (LiveRecordEvents.sourceSealing source writer input).run state =
      (simulateQ (sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
        (RawCtxSourceSeal.sealInput input)).run state := by
  simp only [LiveRecordEvents.sourceSealing, RawCtxMixedOwner.sendAdapter,
    RawCtxSourceSeal.nativeAdapter, sharedImpl, QueryImpl.compose, QueryImpl.simulateQ_compose]

/-- The same theorem consumes the actual source callback used by the public live service. -/
theorem source_publication {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (lengths : BodyLength source.crypto) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (bounded : admitted input) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (LiveRecordEvents.sourceSealing source writer input).run (auxiliary, cache) = (do
      let result ← (simulateQ ctxRandomOracle
        (ctxSeal source.crypto (sourceKey input) (sourceInput input had))).run cache
      pure (some (encode (recordFrame input result.1)), (auxiliary, result.2))) := by
  rw [source_shared]
  exact shared_publication source.crypto lengths writer encode writes
    (RawCtxSourceHkdf.kdfImpl source) input had bounded auxiliary cache

/-- Every actual callback outcome has its real inner record, actual published bytes and identical complete primitive poststate. -/
theorem source_supported {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (lengths : BodyLength source.crypto) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (bounded : admitted input) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache)
    (result : Option Pqxdh.Bytes × RawCtxSharedPrimitive.SharedState Auxiliary) :
    result ∈ support ((LiveRecordEvents.sourceSealing source writer input).run (auxiliary, cache)) ↔
      ∃ record afterCache,
        (record, afterCache) ∈ support ((simulateQ ctxRandomOracle
          (ctxSeal source.crypto (sourceKey input) (sourceInput input had))).run cache) ∧
        result = (some (encode (recordFrame input record)), (auxiliary, afterCache)) := by
  rw [source_publication source lengths writer encode writes input had bounded auxiliary cache]
  simp only [mem_support_bind_iff, Prod.exists, support_pure, Set.mem_singleton_iff]

/-- There is no supported normal-return None callback after valid, bounded source sealing. -/
theorem source_no_failure {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (lengths : BodyLength source.crypto) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (bounded : admitted input) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache)
    (after : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (none, after) ∉ support ((LiveRecordEvents.sourceSealing source writer input).run (auxiliary, cache)) := by
  rw [source_supported source lengths writer encode writes input had bounded auxiliary cache]
  simp

/-- A supported source CTX record has exactly the plaintext length plus tag16 and commitment64. -/
theorem protected_length (c : Pqxdh.Crypto) (lengths : BodyLength c)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (cache after : CtxRO.QueryCache) (record : CtxRomRecord)
    (actual : (record, after) ∈ support ((simulateQ ctxRandomOracle
      (ctxSeal c (sourceKey input) (sourceInput input had))).run cache)) :
    (recordFrame input record).payload.length = input.context.plaintext.length + 80 := by
  simp only [ctxSeal, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, mem_support_bind_iff, Prod.exists,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at actual
  obtain ⟨digest, _, _, rfl, _⟩ := actual
  simp [recordFrame, CtxRomRecord.encode, CtxRomRecord.toRecordCipher, Pqxdh.RecordCipher.encode,
    lengths _ _ _ _, c.aeadSeal_tag_length, sourceInput]

/-- Successful actual decoding of the published buffer recovers the exact inner CTX record and source metadata from that same execution. -/
theorem source_decode {Auxiliary Message Root : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (lengths : BodyLength source.crypto) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (reader : RawCtxFrameDecoding.Reader Message Root) (reads : ReadsOn reader encode)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (bounded : admitted input) (auxiliary : Auxiliary) (cache afterCache : CtxRO.QueryCache)
    (raw : Pqxdh.Bytes) (afterAuxiliary : Auxiliary)
    (actual : (some raw, (afterAuxiliary, afterCache)) ∈ support
      ((LiveRecordEvents.sourceSealing source writer input).run (auxiliary, cache)))
    (decoded : RawCtxReceive.DecodedFrame)
    (decodedRaw : RawCtxFrameDecoding.decode reader raw = some decoded) :
    ∃ record,
      (record, afterCache) ∈ support ((simulateQ ctxRandomOracle
        (ctxSeal source.crypto (sourceKey input) (sourceInput input had))).run cache) ∧
      afterAuxiliary = auxiliary ∧ raw = encode (recordFrame input record) ∧
      decoded = recordFrame input record := by
  rw [source_supported source lengths writer encode writes input had bounded auxiliary cache] at actual
  obtain ⟨record, after, supported, equality⟩ := actual
  simp only [Prod.mk.injEq, Option.some.injEq] at equality
  rcases equality with ⟨rfl, rfl, rfl⟩
  refine ⟨record, supported, rfl, rfl, ?_⟩
  apply RawCtxFrameWriting.readable_decode reader _ decoded _ (reads _ ?_) decodedRaw
  simpa only [admitted, protected_length source.crypto lengths input had cache afterCache record supported] using bounded

/-- The real prepared-send adapter returns Some with the encoded bytes, original target route and selected sequence; it does not add a publication failure after the writer. -/
theorem pending_publication {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (lengths : BodyLength source.crypto) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (pending : SendSeal RawCtxSourceSend.SealContext)
    (had : pending.context.associatedData.length = 153)
    (bounded : admitted (RawCtxSourceSend.arguments pending))
    (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    (simulateQ (liveOwnerSendPrimitive (RawCtxSourceHkdf.response source.crypto)
      (LiveRecordEvents.sourceSealing source writer))
      (RawCtxSourceSend.adapter (.inr pending))).run (auxiliary, cache) = (do
      let result ← (simulateQ ctxRandomOracle
        (ctxSeal source.crypto (sourceKey (RawCtxSourceSend.arguments pending))
          (sourceInput (RawCtxSourceSend.arguments pending) had))).run cache
      pure (some (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments pending)
        (encode (recordFrame (RawCtxSourceSend.arguments pending) result.1))), (auxiliary, result.2))) := by
  simp only [RawCtxSourceSend.adapter, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, liveOwnerSendPrimitive]
  change (do
    let p ← (LiveRecordEvents.sourceSealing source writer (RawCtxSourceSend.arguments pending)).run (auxiliary, cache)
    pure (p.1.map (RawCtxSourceSend.encrypted (RawCtxSourceSend.arguments pending)), p.2)) = _
  rw [source_publication source lengths writer encode writes (RawCtxSourceSend.arguments pending) had bounded auxiliary cache]
  simp only [bind_assoc, pure_bind, Option.map_some]

/-- Every subsequent adaptive computation receives the actual Some bytes and same complete primitive state. -/
theorem source_continued {Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (lengths : BodyLength source.crypto) (writer : RawCtxMixedShared.Writer)
    (encode : RawCtxReceive.DecodedFrame → Pqxdh.Bytes) (writes : WritesOn writer encode)
    (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 153)
    (bounded : admitted input) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache)
    (next : Option Pqxdh.Bytes → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Result) :
    ((LiveRecordEvents.sourceSealing source writer input) >>= next).run (auxiliary, cache) = (do
      let result ← (simulateQ ctxRandomOracle
        (ctxSeal source.crypto (sourceKey input) (sourceInput input had))).run cache
      (next (some (encode (recordFrame input result.1)))).run (auxiliary, result.2)) := by
  rw [StateT.run_bind, source_publication source lengths writer encode writes input had bounded auxiliary cache]
  simp only [bind_assoc, pure_bind]

/-- The original source callback still spends at most one 64-byte commitment draw; codec and deterministic primitive work remain real local work. -/
theorem source_uniform {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (auxiliary : Auxiliary) (cache : CtxRO.QueryCache) :
    ((LiveRecordEvents.sourceSealing source writer input).run (auxiliary, cache)).IsTotalQueryBound 64 := by
  rw [source_shared]
  exact shared_seal_uniform source.crypto writer (RawCtxSourceHkdf.kdfImpl source) input auxiliary cache

end BeaconcryptCore.Computational.RawCtxSourcePublication

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.shared_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.shared_publication

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_shared

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_publication

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_supported

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_no_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_no_failure

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.protected_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.protected_length

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_decode

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.pending_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.pending_publication

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_continued' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_continued

/--
info: 'BeaconcryptCore.Computational.RawCtxSourcePublication.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourcePublication.source_uniform
