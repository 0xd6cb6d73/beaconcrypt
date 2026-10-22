import BeaconcryptCore.Computational.RawCtxServerRouting
import BeaconcryptCore.Computational.RawCtxNativeSlot

/-!
This retained generic reader model includes the former Cap'n Proto partial-header reader. It is not the current CBOR decoder transcription. `CborTransport.reader` instantiates it with one complete validated frame, so its header and payload failure domains coincide; `CborProductionBoundary` is the current normalized production entry point.

This module formalizes the narrow protocol-owned CryptoFrame prelude over a functional Cap'n Proto reader interface at fixed reader options. It keeps read-message failure, exact remaining-input rejection, root failure, total scalar getters (including ordinary default values), fallible payload access and strict nonempty-body validation. Header routing and full decoding have different failure domains. Successful framing does not imply canonical encoding or injectivity of the original raw buffer.

`sourcePrepared` follows the native getter order, retaining the exact base/tag/commitment slices before source admission. Their protected-payload projection is proved against the existing record decoder. The source/normalized-decoder equations are functional outcome equalities; they do not equate codec work, traversal/allocation traces, timing or failure side effects. The Reader boundary describes the same immutable message/root for each parse. Server's header parse and receive parse each start a new native reader with the same fixed options. Native Cap'n Proto/library representation, bounds and traversal accounting remain contracts, not security assumptions or implementation proofs.

The final equations instantiate the existing whole-owner, diagnostic ready-slot and assigned-handle server games, preserving every private callback, actual optional reply, complete ratchet/map and final primitive state. The source loop receives the unchanged raw buffer and decoded fields; retained slices are uniquely recoverable from that protected payload. Native implementation/compiler ownership, crashes/CAS/storage, constant-time behavior, correlated evolving-key component routing and the global cryptographic/symbolic experiment remain separate. Existing source-rank, one-opening and raw-attempt bounds transfer along these exact games; this does not make parser or primitive work free or prove their internal security.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxFrameDecoding

/-- Functional Cap'n Proto boundary at fixed reader options; no encoding injectivity or security law. -/
structure Reader (Message Root : Type) where
  readMessage : Pqxdh.Bytes → Option (Message × Pqxdh.Bytes)
  root : Message → Option Root
  keyId : Root → Std.U64
  sequence : Root → Std.U64
  payload : Root → Option Pqxdh.Bytes

/-- Source complete-input framing checks the remaining slice before a root/getter call. -/
def complete {Message Root : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) : Option Message := do
  let (message, remaining) ← reader.readMessage raw
  if remaining.isEmpty then some message else none

def frameRoot {Message Root : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) : Option Root := do
  reader.root (← complete reader raw)

/-- Server routing reads the root key ID without accessing the ciphertext pointer. -/
def sender {Message Root : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) : Option Std.U64 := do
  return reader.keyId (← frameRoot reader raw)

/-- Full decoding additionally dereferences the payload; its failure domain may be larger. -/
def decode {Message Root : Type} (reader : Reader Message Root) : RawCtxReceive.FrameDecoder :=
  fun raw => do
    let root ← frameRoot reader raw
    let payload ← reader.payload root
    return ⟨reader.sequence root, reader.keyId root, payload⟩

/-- The native receive prelude follows key-ID validation, payload access, length validation, then sequence. -/
def sourceFrame {Message Root : Type} (reader : Reader Message Root)
    (expected : Std.U64) (raw : Pqxdh.Bytes) : Option RawCtxReceive.DecodedFrame := do
  if raw.isEmpty then none else do
    let root ← frameRoot reader raw
    let kid := reader.keyId root
    if kid ≠ expected then none else do
      let payload ← reader.payload root
      if payload.length ≤ 80 then none else
        return ⟨reader.sequence root, kid, payload⟩

/-- The established owner adapter's validation uses the same decoded fields and dynamic AD view. -/
def validated {Message Root : Type} (reader : Reader Message Root)
    (expected : Std.U64) (ad raw : Pqxdh.Bytes) : Option RawCtxReceive.DecodedFrame :=
  if raw.isEmpty then none else do
    let frame ← decode reader raw
    if RawCtxReceive.ValidFrame expected ad frame then some frame else none

/-- Pure payload access and sender validation commute, with the actual native AD width. -/
theorem sourceFrame_eq_validated {Message Root : Type} (reader : Reader Message Root)
    (expected : Std.U64) (ad raw : Pqxdh.Bytes) (had : ad.length = 153) :
    sourceFrame reader expected raw = validated reader expected ad raw := by
  unfold sourceFrame validated decode
  split <;> simp_all only
  cases hroot : frameRoot reader raw <;> simp only [Bind.bind, Option.bind, pure]
  rename_i root
  cases reader.payload root <;> simp only [RawCtxReceive.ValidFrame, had, and_true, ite_self]
  split_ifs <;> simp_all
  omega

/-- The exact three borrowed byte slices retained by native OpenFrameContext. -/
structure Slices where
  baseCiphertext : Pqxdh.Bytes
  tag : Pqxdh.Bytes
  commitment : Pqxdh.Bytes

/-- The source splits commitment first, then takes the tag suffix of the retained base. -/
def fromPayload (payload : Pqxdh.Bytes) : Option Slices :=
  if payload.length ≤ 80 then none else
    let base := payload.take (payload.length - 64)
    some ⟨base, base.drop (base.length - 16), payload.drop (payload.length - 64)⟩

/-- The native slices coincide with the already-used record fields; the body is nonempty. -/
theorem fromPayload_record (payload : Pqxdh.Bytes) (slices : Slices)
    (h : fromPayload payload = some slices) :
    ∃ record, Pqxdh.decodeRecord payload = some record ∧
      slices.baseCiphertext = record.body ++ record.tag ∧
      slices.tag = record.tag ∧ slices.commitment = record.commit ∧
      record.tag.length = 16 ∧ record.commit.length = 64 ∧
      0 < record.body.length ∧ record.encode = payload := by
  unfold fromPayload at h
  split at h
  · cases h
  · rename_i hlength
    cases Option.some.inj h
    refine ⟨⟨payload.take (payload.length - 80),
      (payload.drop (payload.length - 80)).take 16, payload.drop (payload.length - 64)⟩, ?_⟩
    simp only [Pqxdh.decodeRecord, ite_eq_left (show 80 ≤ payload.length by omega),
      true_and, List.length_take, Nat.min_eq_left (Nat.sub_le _ _),
      List.length_drop, List.drop_take]
    simp only [show payload.length - 64 - 16 = payload.length - 80 by omega,
      show payload.length - 64 - (payload.length - 80) = 16 by omega,
      show payload.length - (payload.length - 80) = 80 by omega,
      show payload.length - (payload.length - 64) = 64 by omega,
      show min 16 80 = 16 from rfl, show 0 < payload.length - 80 by omega, true_and]
    have hbase : payload.take (payload.length - 64) =
        payload.take (payload.length - 80) ++ (payload.drop (payload.length - 80)).take 16 := by
      simpa only [show payload.length - 80 + 16 = payload.length - 64 by omega] using
        (List.take_add (l := payload) (i := payload.length - 80) (j := 16))
    exact ⟨hbase, by simp only [Pqxdh.RecordCipher.encode, ← hbase, List.take_append_drop]⟩

/-- Complete-input success retains the exact parsed message and an empty remaining slice. -/
theorem complete_success {Message Root : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) (message : Message) (h : complete reader raw = some message) :
    reader.readMessage raw = some (message, []) := by
  unfold complete at h
  cases hread : reader.readMessage raw <;> simp only [hread, Bind.bind, Option.bind] at h
  · cases h
  · split at h <;> simp_all [List.isEmpty_iff, Prod.ext_iff]

/-- A successfully read nonempty tail is rejected before root/getter access. -/
theorem complete_trailing {Message Root : Type} (reader : Reader Message Root)
    (raw remaining : Pqxdh.Bytes) (message : Message)
    (hread : reader.readMessage raw = some (message, remaining)) (htail : remaining ≠ []) :
    complete reader raw = none := by
  simp [complete, hread, List.isEmpty_iff, htail]

/-- Full success exposes the same immutable reader/root and exact payload/scalar getters. -/
theorem decode_success {Message Root : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame)
    (h : decode reader raw = some frame) :
    ∃ message root, reader.readMessage raw = some (message, []) ∧
      reader.root message = some root ∧ reader.payload root = some frame.payload ∧
      frame.sender = reader.keyId root ∧ frame.sequence = reader.sequence root := by
  unfold decode frameRoot at h
  cases hcomplete : complete reader raw <;> simp only [hcomplete, Bind.bind, Option.bind] at h
  · cases h
  · rename_i message
    cases hroot : reader.root message <;> simp only [hroot] at h
    · cases h
    · rename_i root
      cases hpayload : reader.payload root <;> simp only [hpayload, pure] at h
      · cases h
      · cases Option.some.inj h
        exact ⟨message, root, complete_success reader raw message hcomplete, hroot, hpayload, rfl, rfl⟩

/-- Every successful full decode agrees with the source header route, without equating failure domains. -/
theorem decoderAgreement {Message Root : Type} (reader : Reader Message Root) :
    RawCtxServerRouting.DecoderAgreement (sender reader) (decode reader) := by
  intro raw frame h
  obtain ⟨message, root, hread, hroot, _, hsender, _⟩ := decode_success reader raw frame h
  simp [sender, frameRoot, complete, hread, hroot, hsender]

/-- A malformed payload pointer can fail full decoding after a successful header route. -/
theorem sender_payload_failure {Message Root : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) (root : Root)
    (hroot : frameRoot reader raw = some root) (hpayload : reader.payload root = none) :
    sender reader raw = some (reader.keyId root) ∧ decode reader raw = none := by
  simp [sender, decode, hroot, hpayload]

/-- The source slice construction succeeds exactly for a nonempty encrypted body. -/
theorem fromPayload_some_iff (payload : Pqxdh.Bytes) :
    (∃ slices, fromPayload payload = some slices) ↔ 80 < payload.length := by
  unfold fromPayload
  split <;> simp_all

/-- The actual pre-take order also retains the uniquely determined source payload slices. -/
def sourcePrepared {Message Root : Type} (reader : Reader Message Root)
    (expected : Std.U64) (raw : Pqxdh.Bytes) : Option (RawCtxReceive.DecodedFrame × Slices) := do
  if raw.isEmpty then none else do
    let root ← frameRoot reader raw
    let kid := reader.keyId root
    if kid ≠ expected then none else do
      let payload ← reader.payload root
      let slices ← fromPayload payload
      return (⟨reader.sequence root, kid, payload⟩, slices)

/-- Forgetting the derived slices retains exactly the accepted fields and all rejection outcomes. -/
theorem sourcePrepared_frame {Message Root : Type} (reader : Reader Message Root)
    (expected : Std.U64) (raw : Pqxdh.Bytes) :
    Prod.fst <$> sourcePrepared reader expected raw = sourceFrame reader expected raw := by
  unfold sourcePrepared sourceFrame
  split
  · rfl
  · cases frameRoot reader raw <;> simp only [Bind.bind, Option.bind, pure, Functor.map, Option.map]
    rename_i root
    cases reader.payload root <;> simp only [fromPayload]
    all_goals split_ifs <;> rfl

/-- Execute the unchanged extracted owner loop after the source framing/getter/split prelude. -/
noncomputable def sourceReceive {Message Root Metadata : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) : StateT (RawCtxWholeOwner.OwnerState Metadata)
      (OracleComp RawCtxWholeOwner.PrimitiveSpec) (core.option.Option RawCtxWholeOwner.Decrypted) :=
  fun state => match sourcePrepared reader state.owner.expectedSender raw with
    | none => pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None))
    | some (frame, _) => do
        let result ← simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive
          state.owner.kernel frame.sequence ⟨raw, frame, state.owner.associatedData⟩)
        pure (RawCtxWholeOwner.publish state result)

/-- The complete source prelude feeds exactly the existing owner program and all its private callbacks. -/
theorem sourceReceive_exact {Message Root Metadata : Type} (reader : Reader Message Root)
    (raw : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata)
    (had : state.owner.associatedData.length = 153) :
    sourceReceive reader raw state = RawCtxWholeOwner.rawReceive (decode reader) raw state := by
  have hframe := sourcePrepared_frame reader state.owner.expectedSender raw
  rw [sourceFrame_eq_validated reader state.owner.expectedSender state.owner.associatedData raw had]
    at hframe
  unfold sourceReceive RawCtxWholeOwner.rawReceive
  unfold validated at hframe
  split <;> simp_all only
  all_goals by_cases hempty : raw.isEmpty = true <;> simp_all
  all_goals cases hdecode : decode reader raw <;> simp_all

/-- The accepted native prelude retains the original decoded frame, sender pin and actual derived slices. -/
theorem sourcePrepared_success {Message Root : Type} (reader : Reader Message Root)
    (expected : Std.U64) (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) (slices : Slices)
    (h : sourcePrepared reader expected raw = some (frame, slices)) :
    raw ≠ [] ∧ frame.sender = expected ∧ decode reader raw = some frame ∧
      fromPayload frame.payload = some slices := by
  unfold sourcePrepared at h
  split at h
  · cases h
  · rename_i hempty
    simp only [Bind.bind, Option.bind] at h
    cases hroot : frameRoot reader raw <;> simp only [hroot] at h
    · cases h
    · split at h
      · cases h
      · rename_i root hkid
        cases hpayload : reader.payload root <;> simp only [hpayload] at h
        · cases h
        · rename_i payload
          cases hslices : fromPayload payload <;> simp only [hslices, pure] at h
          · cases h
          · cases Option.some.inj h
            refine ⟨by simpa only [List.isEmpty_iff] using hempty, Classical.not_not.mp hkid, ?_, hslices⟩
            simp [decode, hroot, hpayload]

/-- The functional source decoder is interpreted with the complete stateful private primitive interpreter. -/
noncomputable def sourceGame {Message Root Metadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (reader : Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :=
  (simulateQ impl (sourceReceive reader raw state)).run primitive

/-- Source decoder instantiation preserves the whole probabilistic program and final primitive state. -/
theorem sourceGame_exact {Message Root Metadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (reader : Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (had : state.owner.associatedData.length = 153) :
    sourceGame impl reader raw state primitive =
      RawCtxWholeOwner.rawGame impl (decode reader) raw state primitive := by
  simp only [sourceGame, sourceReceive_exact reader raw state had, RawCtxWholeOwner.rawGame]
  rfl

/-- The ready slot model implements this exact decoder-instantiated source game before public return. -/
theorem sourceGame_ready_slot {Message Root Metadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (reader : Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (had : state.owner.associatedData.length = 153) :
    RawCtxNativeSlot.rawGame impl (decode reader) raw (RawCtxNativeSlot.ready state) primitive =
      (fun result => ((.ok result.1.1, RawCtxNativeSlot.ready result.1.2), result.2)) <$>
        sourceGame impl reader raw state primitive := by
  rw [sourceGame_exact impl reader raw state primitive had, RawCtxNativeSlot.rawGame_ready]

/-- Server framing and lookup use the same source reader contract before the selected source receive. -/
noncomputable def sourceServerGame {Message Root Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (reader : Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) (primitive : PrimitiveState) :
    OracleComp base ((core.option.Option RawCtxWholeOwner.Decrypted ×
      RawCtxServerRouting.State Metadata PeerMetadata) × PrimitiveState) :=
  match sender reader raw with
  | none => pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive)
  | some kid =>
      match RawCtxServerRouting.peerAssociatedData state.server kid with
      | none => pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive)
      | some ad =>
          match state.server.peers kid with
          | none => pure ((.None, { state with rawAttempts := state.rawAttempts + 1 }), primitive)
          | some peer => do
              let result ← sourceGame impl reader raw
                ⟨RawCtxServerRouting.selectedOwner kid ad peer, state.rawAttempts⟩ primitive
              pure ((result.1.1,
                ⟨RawCtxServerRouting.putPeer state.server kid peer result.1.2.owner.kernel,
                  result.1.2.rawAttempts⟩), result.2)

/-- Both source parses, exact same-entry AD and full map publication instantiate the checked server game. -/
theorem sourceServerGame_exact {Message Root Metadata PeerMetadata PrimitiveState : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (reader : Reader Message Root) (raw : Pqxdh.Bytes)
    (state : RawCtxServerRouting.State Metadata PeerMetadata) (primitive : PrimitiveState) :
    sourceServerGame impl reader raw state primitive =
      RawCtxServerRouting.rawGame impl (sender reader) (decode reader) raw state primitive := by
  unfold sourceServerGame RawCtxServerRouting.rawGame
  cases sender reader raw
  · rfl
  · rename_i kid
    dsimp only
    cases had : RawCtxServerRouting.peerAssociatedData state.server kid
    · rfl
    · rename_i ad
      obtain ⟨peer, hpeer, rfl⟩ := RawCtxServerRouting.peerAssociatedData_some state.server kid ad had
      simp only [hpeer, sourceGame_exact impl reader raw
        ⟨RawCtxServerRouting.selectedOwner kid
          (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer, state.rawAttempts⟩ primitive
        (RawCtxServerRouting.associatedBytes_length state.server.identity peer.identity)]

end BeaconcryptCore.Computational.RawCtxFrameDecoding

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceFrame_eq_validated' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceFrame_eq_validated

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.fromPayload_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.fromPayload_record

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.complete_success' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.complete_success

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.complete_trailing' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.complete_trailing

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.decode_success' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.decode_success

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.decoderAgreement' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.decoderAgreement

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sender_payload_failure' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sender_payload_failure

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.fromPayload_some_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.fromPayload_some_iff

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourcePrepared_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourcePrepared_frame

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceReceive_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceReceive_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourcePrepared_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourcePrepared_success

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceGame_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceGame_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceGame_ready_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceGame_ready_slot

/--
info: 'BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceServerGame_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFrameDecoding.sourceServerGame_exact
