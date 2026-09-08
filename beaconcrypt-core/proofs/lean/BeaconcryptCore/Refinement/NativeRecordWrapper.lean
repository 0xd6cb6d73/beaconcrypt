import BeaconcryptCore.Extraction
import BeaconcryptCore.Refinement.CommitmentSurface
import BeaconcryptCore.Computational.RawCtxInterpretedArguments

/-!
The production record wrapper owns complete-input admission, exact borrowed payload views and the selected opening capability. These theorems check the emitted functions on every represented input, including missing or malformed selected slots, against the original receive operation and commitment transcript.

The driver equation retains hash, unconditional transcript erasure, optional comparison, AEAD and original finish under arbitrary lawful effects. It uses the same actual optional outputs and preserves the complete underlying state. No primitive correctness or probability law is assumed. The native adapter supplies these requests; its precise source wiring is checked separately by the fidelity probes. Cap'n Proto parsing, native cryptographic execution, compiler/library contracts and outer role/slot wiring remain explicit boundaries. Arbitrary raw encodings need not be unique. Storage, snapshots and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.NativeRecordWrapper

private theorem difference_val (x y : Std.Usize) :
    (⟨BitVec.ofNat _ (x.val - y.val)⟩ : Std.Usize).val = x.val - y.val :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) x.bv.isLt)

def PayloadView (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize)
    (sender : Std.U64) (context : record.OpenFrameContext) : Prop :=
  context.base_ciphertext.val = payload.val.take (payload.val.length - 64) ∧
  context.tag.val = (payload.val.take (payload.val.length - 64)).drop (payload.val.length - 80) ∧
  context.commitment.val = payload.val.drop (payload.val.length - 64) ∧
  context.associated_data = ad ∧ context.sender_kid = sender

/-- Every payload returns normally and retains its exact original slices and metadata, or rejects at the strict length boundary. -/
theorem payload_views (payload : Slice Std.U8) (ad : Std.Array Std.U8 153#usize)
    (sender : Std.U64) :
    ∃ result, record.OpenFrameContext.from_frame payload ad sender = ok result ∧
      match result with
      | .None => payload.val.length ≤ 80
      | .Some context => 80 < payload.val.length ∧ PayloadView payload ad sender context := by
  have hadd : (64#usize + 16#usize : RustM Std.Usize) = ok 80#usize :=
    PqxdhRefinement.usize_add_eq _ _ _ (by simp)
  unfold record.OpenFrameContext.from_frame
  simp only [core.slice.Slice.len, core.slice.Slice.split_at,
    record.MESSAGE_OVERHEAD, record.COMMITMENT_SIZE, commitment.AEAD_TAG_SIZE,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_split_at,
    hadd, bind_tc_ok]
  split
  · rename_i hsmall
    exact ⟨.None, rfl, by simpa using hsmall⟩
  · rename_i hlarge
    have hlength : 80 < payload.val.length := by simpa using hlarge
    have hbaseVal : (⟨BitVec.ofNat _ (payload.len.val - (64#usize).val)⟩ : Std.Usize).val =
        payload.val.length - 64 := by
      calc
        _ = payload.len.val - (64#usize).val :=
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) payload.len.bv.isLt)
        _ = _ := by simp
    rw [PqxdhRefinement.usize_sub_eq _ _ (by simpa using (show 64 ≤ payload.val.length by omega))]
    simp only [bind_tc_ok, Aeneas.Std.core.slice.Slice.split_at,
      hbaseVal, Slice.length, Nat.sub_le, ↓reduceDIte, List.splitAt_eq]
    dsimp! only
    rw [PqxdhRefinement.usize_sub_eq _ _ (by simp only [Slice.len_val, Slice.length,
      List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]; simp; omega)]
    simp only [bind_tc_ok, core.Slice.Insts.CoreOpsIndexIndex.index,
      core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
      rust_primitives.slice.slice_length, UScalar.le_equiv, difference_val, Nat.sub_le,
      ↓reduceIte]
    simp only [rust_primitives.slice.slice_slice, Slice.subslice, difference_val, Nat.sub_le]
    simp only [Slice.len_val, le_refl, and_self, ↓reduceIte, bind_tc_ok]
    simp only [core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from,
      Aeneas.Std.core.array.TryFromSharedArraySlice.try_from]
    simp only [UScalar.eq_equiv, Slice.len_val, Slice.length, List.slice_length,
      List.length_take, Nat.min_eq_left (Nat.sub_le _ _), List.length_drop,
      Nat.min_self]
    have htag : payload.val.length - 64 - (payload.val.length - 64 - (16#usize).val) =
        (16#usize).val := by simp; omega
    have hcommit : payload.val.length - (payload.val.length - 64) = (64#usize).val := by simp; omega
    simp only [htag, hcommit, ↓reduceDIte, bind_tc_ok]
    refine ⟨_, rfl, hlength, ?_⟩
    simp only [PayloadView, true_and, and_true, List.slice]
    have hoff : payload.val.length - 64 - (16#usize).val = payload.val.length - 80 := by simp; omega
    simpa only [hoff, List.length_drop, List.length_take, Nat.min_eq_left (Nat.sub_le _ _)] using
      (List.take_length (l := (payload.val.take (payload.val.length - 64)).drop (payload.val.length - 80)))

/-- The actual reader remainder alone gates the unchanged decoded message. -/
theorem complete_input {Message : Type} (remaining : Slice Std.U8) (message : Message) :
    record.finish_frame_read remaining message =
      ok (if remaining.val.length = 0 then .Some message else .None) := by
  simp [record.finish_frame_read, core.slice.Slice.is_empty, core.slice.Slice.len,
    rust_primitives.slice.slice_length, UScalar.eq_equiv]
  split <;> simp_all

def selectedFields (opening : ReceiveOpen record.OpenFrameContext)
    (material : RatchetMaterial) (sequence : Std.U64) : CommitmentSurface.Fields :=
  ⟨material.key.bytes, material.nonce.bytes, opening.context.associated_data,
    opening.context.tag, sequence, opening.context.sender_kid⟩

/-- The original selected material and sequence determine the commitment transcript before any primitive effect. -/
theorem begin_selected (opening : ReceiveOpen record.OpenFrameContext)
    (material : RatchetMaterial) (sequence : Std.U64)
    (hmaterial : ReceiveOpen.material opening = ok (.Some material))
    (hsequence : ReceiveOpen.sequence opening = ok sequence) :
    record.begin_open opening = ok (.OpenCommitmentRequested
      ⟨opening, ⟨CommitmentSurface.productionInput (selectedFields opening material sequence)⟩⟩) := by
  simp only [record.begin_open, hmaterial, hsequence, ReceiveOpen.impl.context,
    RatchetMaterial.impl.key, RatchetMaterial.impl.nonce, RatchetKey.as_bytes,
    RatchetNonce.as_bytes, bind_tc_ok]
  simpa only [selectedFields, bind_tc_ok] using congrArg
    (fun result : RustM commitment.CommitmentTranscript => result >>= fun transcript =>
      ok (record.OpenStart.OpenCommitmentRequested ⟨opening, transcript⟩))
    (CommitmentSurface.productionInput_spec (selectedFields opening material sequence))

/-- A missing selected material recovers the original receive entry without hashing. -/
theorem begin_missing (opening : ReceiveOpen record.OpenFrameContext)
    (hmaterial : ReceiveOpen.material opening = ok .None) :
    record.begin_open opening = ok (.OpenRejected opening.entry) := by
  simp [record.begin_open, hmaterial, ReceiveOpen.reject]

/-- Every comparison result either retains the same opening or rejects to its original entry. -/
theorem resume_exact (pending : record.OpenCommitment) (matched : Bool) :
    record.OpenCommitment.resume pending matched = ok
      (if matched then .OpenAeadRequested ⟨pending.opening⟩
        else .OpenCommitmentRejected pending.opening.entry) := by
  cases matched <;> rfl

/-- The actual selected material and admitted context supply the complete AEAD request. -/
theorem request_selected (opening : record.OpenAead) (material : RatchetMaterial)
    (hmaterial : ReceiveOpen.material opening.opening = ok (.Some material)) :
    record.OpenAead.request opening = ok (.Some
      ⟨material.key.bytes, material.nonce.bytes, opening.opening.context.base_ciphertext,
        opening.opening.context.associated_data⟩) := by
  simp [record.OpenAead.request, hmaterial, ReceiveOpen.impl.context,
    RatchetMaterial.impl.key, RatchetMaterial.impl.nonce, RatchetKey.as_bytes, RatchetNonce.as_bytes]

/-- Every actual optional plaintext returns through the original receive publication with its selected metadata. -/
theorem finish_selected {Plaintext : Type} (opening : record.OpenAead)
    (sequence : Std.U64) (hsequence : ReceiveOpen.sequence opening.opening = ok sequence)
    (reply : core.option.Option Plaintext) :
    record.OpenAead.finish opening reply = ReceiveOpen.finish opening.opening
      (match reply with
       | .None => .None
       | .Some plaintext => .Some ⟨plaintext, opening.opening.context.sender_kid, sequence⟩) := by
  cases reply <;> simp [record.OpenAead.finish, ReceiveOpen.impl.context, hsequence]

/-- All represented openings, including malformed private slots, have normal material and sequence getters. -/
theorem getters_normal (opening : ReceiveOpen record.OpenFrameContext) :
    (∃ material, ReceiveOpen.material opening = ok material) ∧
    (∃ sequence, ReceiveOpen.sequence opening = ok sequence) := by
  let view : Computational.RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial
      record.OpenFrameContext := ⟨opening.entry.refined, opening.context, opening.prepared⟩
  constructor
  · simpa only [← Computational.RawCtxInterpretedOpening.native_material,
      Computational.RawCtxInterpretedOpening.toNative, view] using
      (Computational.RawCtxInterpretedArguments.material_total view)
  · simpa only [← Computational.RawCtxInterpretedOpening.native_sequence,
      Computational.RawCtxInterpretedOpening.toNative, view] using
      (Computational.RawCtxInterpretedArguments.sequence_total view)

structure Primitives (m : Type → Type) (Plaintext Digest : Type) where
  hash : Std.Array Std.U8 229#usize → m (Option Digest)
  erase : Std.Array Std.U8 229#usize → m (Std.Array Std.U8 229#usize)
  compare : Digest → Std.Array Std.U8 64#usize → m Bool
  aead : record.AeadRequest → m (core.option.Option Plaintext)

def compareReply {m : Type → Type} [Monad m] {Plaintext Digest : Type}
    (execute : Primitives m Plaintext Digest) (digest : Option Digest)
    (supplied : Std.Array Std.U8 64#usize) : m Bool :=
  match digest with
  | none => pure false
  | some digest => execute.compare digest supplied

def driverRun {m : Type → Type} [Monad m] {Plaintext Digest : Type}
    (execute : Primitives m Plaintext Digest) (opening : ReceiveOpen record.OpenFrameContext) :
    m (RustM (ConcreteRatchetKernel × core.option.Option (record.OpenedRecord Plaintext))) :=
  Computational.RawCtxInterpretedOpening.bindResult (record.begin_open opening) fun start =>
    match start with
    | .OpenRejected kernel => pure (ok (kernel, .None))
    | .OpenCommitmentRequested pending => do
      let digest ← execute.hash pending.transcript.bytes
      let erased ← execute.erase pending.transcript.bytes
      let pending := { pending with transcript := ⟨erased⟩ }
      let matched ← compareReply execute digest pending.opening.context.commitment
      Computational.RawCtxInterpretedOpening.bindResult (record.OpenCommitment.resume pending matched) fun next =>
        match next with
        | .OpenCommitmentRejected kernel => pure (ok (kernel, .None))
        | .OpenAeadRequested requested =>
          Computational.RawCtxInterpretedOpening.bindResult (record.OpenAead.request requested) fun input =>
            match input with
            | .None => pure (record.OpenAead.finish requested .None)
            | .Some input => do
              let plaintext ← execute.aead input
              pure (record.OpenAead.finish requested plaintext)

def sourceRun {m : Type → Type} [Monad m] {Plaintext Digest : Type}
    (execute : Primitives m Plaintext Digest) (opening : ReceiveOpen record.OpenFrameContext) :
    m (RustM (ConcreteRatchetKernel × core.option.Option (record.OpenedRecord Plaintext))) :=
  Computational.RawCtxInterpretedOpening.bindResult (ReceiveOpen.material opening) fun selected =>
    match selected with
    | .None => pure (ReceiveOpen.finish opening .None)
    | .Some material =>
      Computational.RawCtxInterpretedOpening.bindResult (ReceiveOpen.sequence opening) fun sequence =>
        Computational.RawCtxInterpretedOpening.bindResult
          (commitment.build_commitment_transcript material.key.bytes material.nonce.bytes
            opening.context.associated_data opening.context.tag sequence opening.context.sender_kid)
          fun transcript => do
            let digest ← execute.hash transcript.bytes
            let _ ← execute.erase transcript.bytes
            let matched ← compareReply execute digest opening.context.commitment
            if matched then do
              let plaintext ← execute.aead
                ⟨material.key.bytes, material.nonce.bytes, opening.context.base_ciphertext,
                  opening.context.associated_data⟩
              pure (ReceiveOpen.finish opening (match plaintext with
                | .None => .None
                | .Some plaintext => .Some ⟨plaintext, opening.context.sender_kid, sequence⟩))
            else pure (ReceiveOpen.finish opening .None)

/-- The extracted phase driver and original opening have identical complete effects under the same arbitrary lawful primitive interpreter. -/
theorem driver_source {m : Type → Type} [Monad m] [LawfulMonad m] {Plaintext Digest : Type}
    (execute : Primitives m Plaintext Digest) (opening : ReceiveOpen record.OpenFrameContext) :
    driverRun execute opening = sourceRun execute opening := by
  obtain ⟨⟨selected, hmaterial⟩, ⟨sequence, hsequence⟩⟩ := getters_normal opening
  cases selected with
  | none =>
    simp [driverRun, sourceRun, begin_missing opening hmaterial, hmaterial,
      Computational.RawCtxInterpretedOpening.bindResult, ReceiveOpen.finish]
  | some material =>
    simp only [driverRun, sourceRun, hmaterial, hsequence,
      begin_selected opening material sequence hmaterial hsequence,
      Computational.RawCtxInterpretedOpening.bindResult]
    have htranscript := CommitmentSurface.productionInput_spec (selectedFields opening material sequence)
    dsimp only [selectedFields] at htranscript
    rw [htranscript]
    simp only [selectedFields]
    apply congrArg (fun continuation : Option Digest →
      m (RustM (ConcreteRatchetKernel × core.option.Option (record.OpenedRecord Plaintext))) =>
      execute.hash (CommitmentSurface.productionInput (selectedFields opening material sequence)) >>= continuation)
    funext digest
    apply congrArg (fun continuation : Std.Array Std.U8 229#usize →
      m (RustM (ConcreteRatchetKernel × core.option.Option (record.OpenedRecord Plaintext))) =>
      execute.erase (CommitmentSurface.productionInput (selectedFields opening material sequence)) >>= continuation)
    funext erased
    apply congrArg (fun continuation : Bool →
      m (RustM (ConcreteRatchetKernel × core.option.Option (record.OpenedRecord Plaintext))) =>
      compareReply execute digest opening.context.commitment >>= continuation)
    funext matched
    cases matched
    · rfl
    · simp only [resume_exact, ↓reduceIte,
        request_selected ⟨opening⟩ material hmaterial,
        finish_selected ⟨opening⟩ sequence hsequence]

/-- Transcript reads, replacement and the supplied commitment retain the original opening. -/
theorem commitment_borrows (pending : record.OpenCommitment) :
    record.OpenCommitment.impl.transcript pending = ok pending.transcript ∧
    record.OpenCommitment.supplied_commitment pending = ok pending.opening.context.commitment ∧
    record.OpenCommitment.transcript_mut pending =
      ok (pending.transcript, fun updated => { pending with transcript := updated }) := by
  exact ⟨rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.NativeRecordWrapper

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.complete_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.complete_input

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.begin_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.begin_selected

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.begin_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.begin_missing

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.resume_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.resume_exact

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.request_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.request_selected

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.finish_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.finish_selected

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.getters_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.getters_normal

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.driver_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.driver_source

/--
info: 'BeaconcryptCore.Refinement.NativeRecordWrapper.commitment_borrows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.NativeRecordWrapper.commitment_borrows
