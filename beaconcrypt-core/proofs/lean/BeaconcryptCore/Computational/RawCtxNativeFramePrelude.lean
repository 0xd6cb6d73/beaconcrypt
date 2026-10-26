import BeaconcryptCore.Computational.RawCtxFrameDecoding
import BeaconcryptCore.Refinement.NativeRecordWrapper

/-!
The native reader exposes its actual remaining input and borrowed payload slices. The protocol-owned complete-input check and payload splitter below are the extracted production functions. Their composition supplies the existing raw computational decoder without an assumed framing or payload-splitting equation. Cap'n Proto reading, root access and scalar getters remain the explicit functional codec interface. Raw encodings need not be canonical, and no cryptographic security property is assumed here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp
open BeaconcryptCore.Refinement PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxNativeFramePrelude

def sliceBytes (slice : Slice Std.U8) : Pqxdh.Bytes := slice.val.map absByte

def contextSlices (context : record.OpenFrameContext) : RawCtxFrameDecoding.Slices :=
  ⟨sliceBytes context.base_ciphertext, absBytes context.tag, absBytes context.commitment⟩

def projectOption {α β : Type} (f : α → β) : core.option.Option α → Option β
  | .None => none
  | .Some value => some (f value)

/-- The extracted payload admission and its three retained slices equal the computational splitter on every represented payload. -/
theorem payload_exact (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (sender : Std.U64) :
    (projectOption contextSlices <$> record.OpenFrameContext.from_frame payload ad sender) =
      ok (RawCtxFrameDecoding.fromPayload (sliceBytes payload)) := by
  obtain ⟨result, execution, fields⟩ := NativeRecordWrapper.payload_views payload ad sender
  rw [execution]
  change ok (projectOption contextSlices result) = _
  cases result with
  | none =>
    simp [projectOption, RawCtxFrameDecoding.fromPayload, sliceBytes, fields]
  | some context =>
    simp only [NativeRecordWrapper.PayloadView] at fields
    simp only [projectOption, contextSlices, sliceBytes, absBytes, RawCtxFrameDecoding.fromPayload,
      List.length_map, ite_eq_right (by omega : ¬ payload.val.length ≤ 80), fields.2.1,
      fields.2.2.1, fields.2.2.2.1, List.map_take, List.map_drop, List.length_take,
      Nat.min_eq_left (Nat.sub_le _ _)]
    rw [Nat.sub_sub]

/-- Functional native codec results retain representable borrowed slices; no field injectivity or successful parsing law is required. -/
structure Reader (Message Root : Type) where
  readMessage : Pqxdh.Bytes → Option (Message × Slice Std.U8)
  root : Message → Option Root
  keyId : Root → Std.U64
  sequence : Root → Std.U64
  payload : Root → Option (Slice Std.U8)

def Reader.model {Message Root : Type} (reader : Reader Message Root) :
    RawCtxFrameDecoding.Reader Message Root where
  readMessage raw := (fun result => (result.1, sliceBytes result.2)) <$> reader.readMessage raw
  root := reader.root
  keyId := reader.keyId
  sequence := reader.sequence
  payload root := sliceBytes <$> reader.payload root

def complete {Message Root : Type} (reader : Reader Message Root) (raw : Pqxdh.Bytes) :
    RustM (Option Message) :=
  match reader.readMessage raw with
  | none => ok none
  | some (message, remaining) => record.finish_frame_read remaining message

/-- Production's extracted complete-input gate supplies exactly the computational decoder's admission. -/
theorem complete_exact {Message Root : Type} (reader : Reader Message Root) (raw : Pqxdh.Bytes) :
    complete reader raw = ok (RawCtxFrameDecoding.complete reader.model raw) := by
  cases reading : reader.readMessage raw with
  | none => simp [complete, reading, RawCtxFrameDecoding.complete, Reader.model]
  | some result =>
    simp [complete, reading, NativeRecordWrapper.complete_input, RawCtxFrameDecoding.complete,
      Reader.model, sliceBytes, List.isEmpty_iff]

structure Prepared where
  frame : RawCtxReceive.DecodedFrame
  context : record.OpenFrameContext

def Prepared.project (prepared : Prepared) : RawCtxReceive.DecodedFrame × RawCtxFrameDecoding.Slices :=
  (prepared.frame, contextSlices prepared.context)

/-- The actual adapter order: empty input, complete framing, root, sender pin, payload pointer, extracted payload admission, and sequence getter. -/
def prepare {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes) :
    RustM (Option Prepared) := do
  if raw.isEmpty then ok none else do
    let parsed ← complete reader raw
    match parsed.bind reader.root with
    | none => ok none
    | some root =>
      let sender := reader.keyId root
      if sender ≠ expected then ok none else
        match reader.payload root with
        | none => ok none
        | some payload =>
          let context ← record.OpenFrameContext.from_frame payload ad sender
          ok (projectOption (fun context => (⟨⟨reader.sequence root, sender, sliceBytes payload⟩, context⟩ : Prepared)) context)

set_option backward.isDefEq.respectTransparency false in
/-- The extracted framing and payload gates instantiate the complete computational prelude, including every rejection. -/
theorem prepare_exact {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes) :
    (Option.map Prepared.project <$> prepare reader ad expected raw) =
      ok (RawCtxFrameDecoding.sourcePrepared reader.model expected raw) := by
  unfold prepare RawCtxFrameDecoding.sourcePrepared
  split
  · rfl
  · rw [complete_exact]
    simp only [bind_tc_ok]
    cases parsed : RawCtxFrameDecoding.complete reader.model raw with
    | none => simp [RawCtxFrameDecoding.frameRoot, parsed]; rfl
    | some message =>
      simp only [RawCtxFrameDecoding.frameRoot, parsed, Bind.bind, Option.bind]
      cases rooted : reader.root message with
      | none => simp only [Reader.model, rooted]; rfl
      | some root =>
        simp only [Reader.model, rooted]
        split
        · rfl
        · cases payloadRead : reader.payload root with
          | none => rfl
          | some payload =>
            obtain ⟨result, execution, fields⟩ := NativeRecordWrapper.payload_views payload ad (reader.keyId root)
            have slices := payload_exact payload ad (reader.keyId root)
            rw [execution] at slices
            have slicesEq := RustM.ok.inj slices
            simp only [execution, Functor.map, Option.map, ← slicesEq]
            cases result <;> rfl

/-- Successful native preparation supplies exactly the same parsed frame and retained slices to the computational source. -/
theorem prepare_success {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (prepared : Prepared) (execution : prepare reader ad expected raw = ok (some prepared)) :
    RawCtxFrameDecoding.sourcePrepared reader.model expected raw = some prepared.project := by
  have projected := prepare_exact reader ad expected raw
  rw [execution] at projected
  exact (RustM.ok.inj projected).symm

/-- Native preparation always has a normal optional result; parser and admission errors remain explicit rejection. -/
theorem prepare_normal {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes) :
    ∃ result, prepare reader ad expected raw = ok result := by
  have projected := prepare_exact reader ad expected raw
  cases execution : prepare reader ad expected raw with
  | ok result => exact ⟨result, rfl⟩
  | fail error =>
    rw [execution] at projected
    cases projected
  | div =>
    rw [execution] at projected
    cases projected

/-- The normalized native result is justified by actual extraction totality, rather than a parser-success premise. -/
noncomputable def prepared {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes) : Option Prepared :=
  (prepare_normal reader ad expected raw).choose

theorem prepared_exact {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes) :
    prepare reader ad expected raw = ok (prepared reader ad expected raw) :=
  (prepare_normal reader ad expected raw).choose_spec

/-- Arbitrary complete continuations receive the identical normalized native fields and rejection outcomes. -/
theorem continuation_exact {Message Root Result : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (next : Option (RawCtxReceive.DecodedFrame × RawCtxFrameDecoding.Slices) → Result) :
    next ((prepared reader ad expected raw).map Prepared.project) =
      next (RawCtxFrameDecoding.sourcePrepared reader.model expected raw) := by
  have projected := prepare_exact reader ad expected raw
  rw [prepared_exact] at projected
  exact congrArg next (RustM.ok.inj projected)

/-- Actual successful preparation retains the source raw buffer, parsed fields, sender pin and exact borrowed payload slices. -/
theorem accepted_fields {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (value : Prepared) (execution : prepare reader ad expected raw = ok (some value)) :
    raw ≠ [] ∧ value.frame.sender = expected ∧
      RawCtxFrameDecoding.decode reader.model raw = some value.frame ∧
      RawCtxFrameDecoding.fromPayload value.frame.payload = some (contextSlices value.context) := by
  exact RawCtxFrameDecoding.sourcePrepared_success reader.model expected raw value.frame
    (contextSlices value.context) (prepare_success reader ad expected raw value execution)

/-- Execute the existing complete source receive after the extracted native prelude. The projection changes only private context representation. -/
noncomputable def receive {Message Root Metadata : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    OracleComp RawCtxWholeOwner.PrimitiveSpec
      (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) :=
  match (prepared reader ad state.owner.expectedSender raw).map Prepared.project with
  | none => pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None))
  | some (frame, _) => do
      let result ← simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive
        state.owner.kernel frame.sequence ⟨raw, frame, state.owner.associatedData⟩)
      pure (RawCtxWholeOwner.publish state result)

/-- Whole receive compilation preserves the actual optional plaintext and complete private owner state. -/
theorem receive_source {Message Root Metadata : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    receive reader ad raw state = RawCtxFrameDecoding.sourceReceive reader.model raw state := by
  unfold receive RawCtxFrameDecoding.sourceReceive
  rw [show (prepared reader ad state.owner.expectedSender raw).map Prepared.project =
      RawCtxFrameDecoding.sourcePrepared reader.model state.owner.expectedSender raw from
    continuation_exact reader ad state.owner.expectedSender raw id]
  rfl

/-- Any stateful primitive interpretation retains its entire evaluated distribution and poststate after the native prelude is installed. -/
theorem game_exact {Message Root Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (reader : Reader Message Root) (ad : Std.Array Std.U8 281#usize) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (associated : state.owner.associatedData = absBytes ad) :
    (simulateQ impl (receive reader ad raw state)).run primitive =
      RawCtxWholeOwner.rawGame impl (RawCtxFrameDecoding.decode reader.model) raw state primitive := by
  rw [receive_source]
  exact RawCtxFrameDecoding.sourceGame_exact impl reader.model raw state primitive (by simp [associated, absBytes_length])

/-- The retained native context uses the selected owner's AD and the very same decoded sender. -/
theorem prepare_context {Message Root : Type} (reader : Reader Message Root)
    (ad : Std.Array Std.U8 281#usize) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (value : Prepared) (execution : prepare reader ad expected raw = ok (some value)) :
    value.context.associated_data = ad ∧ value.context.sender_kid = value.frame.sender := by
  unfold prepare at execution
  split at execution
  · cases execution
  · rw [complete_exact] at execution
    simp only [bind_tc_ok] at execution
    split at execution
    · cases execution
    · split at execution
      · cases execution
      · split at execution
        · cases execution
        · rename_i _ root _ _ _ payload _
          obtain ⟨result, splitResult, fields⟩ := NativeRecordWrapper.payload_views payload ad (reader.keyId root)
          rw [splitResult] at execution
          cases result with
          | none => cases execution
          | some context =>
            have same := Option.some.inj (RustM.ok.inj execution)
            cases same
            exact fields.2.2.2.2

end BeaconcryptCore.Computational.RawCtxNativeFramePrelude

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.payload_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.payload_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.complete_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.complete_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_success

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_normal

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepared_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepared_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.continuation_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.continuation_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.accepted_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.accepted_fields

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.receive_source

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.game_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.game_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeFramePrelude.prepare_context
