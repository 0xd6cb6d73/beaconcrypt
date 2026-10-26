-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.RecordEffects
import BeaconcryptCore.Computational.RawCtxOwnerProvenance

/-! Actual receive admission and every continuation retain the selected sequence and exact admitted payload context. These are operational invariants for arbitrary typed primitive replies, with no valid-entry premise. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open BeaconcryptCore.Computational
open BeaconcryptCore.Refinement.NativeRecordWrapper

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant

/-- Every live phase retains the original target and complete payload view; rejection publishes no metadata. -/
def RecordReceiveMetadata (sender sequence : Std.U64) (associatedData : Std.Array Std.U8 281#usize)
    (ciphertext : Slice Std.U8) : record_effects.RecordReceiveEffect → Prop
  | .Rejected _ => True
  | .KdfRequested pending => pending.pending.target = sequence ∧
      PayloadView ciphertext associatedData sender pending.pending.context
  | .CommitmentRequested pending => pending.pending.opening.sequence = ok sequence ∧
      PayloadView ciphertext associatedData sender pending.pending.opening.context
  | .AeadRequested pending => pending.pending.opening.sequence = ok sequence ∧
      PayloadView ciphertext associatedData sender pending.pending.opening.context

/-- Actual opening normalization preserves the old source target/context invariant and exact payload view. -/
theorem normalize_metadata (sender sequence : Std.U64) (associatedData : Std.Array Std.U8 281#usize)
    (ciphertext : Slice Std.U8) (context : record.OpenFrameContext)
    (effect : ratchet.concrete.ReceiveEffect record.OpenFrameContext)
    (scope : RawCtxOwnerProvenance.Scope sequence context effect)
    (view : PayloadView ciphertext associatedData sender context) :
    ∃ next, record_effects.normalize_receive effect = ok next ∧
      RecordReceiveMetadata sender sequence associatedData ciphertext next := by
  cases effect with
  | ReceiveRejected kernel _context => exact ⟨.Rejected kernel, rfl, trivial⟩
  | ReceiveKdfRequested pending =>
    exact ⟨.KdfRequested ⟨pending⟩, rfl, scope.1, scope.2.symm ▸ view⟩
  | ReceiveOpenRequested opening =>
    obtain ⟨material, materialRun⟩ := (getters_normal opening).1
    cases material with
    | none =>
      exact ⟨.Rejected opening.entry, by
        simp only [record_effects.normalize_receive, begin_missing opening materialRun, bind_tc_ok], trivial⟩
    | some material =>
      refine ⟨.CommitmentRequested ⟨⟨opening,
        ⟨CommitmentSurface.productionInput (selectedFields opening material sequence)⟩⟩⟩,
        ?_, scope.1, scope.2.symm ▸ view⟩
      simp only [record_effects.normalize_receive,
        begin_selected opening material sequence materialRun scope.1, bind_tc_ok]

/-- Every actual record admission establishes the target and exact payload metadata, including rejection paths. -/
theorem begin_metadata (kernel : ConcreteRatchetKernel) (sender sequence : Std.U64)
    (associatedData : Std.Array Std.U8 281#usize) (ciphertext : Slice Std.U8) :
    ∃ next, record_effects.begin_record_receive kernel sequence ciphertext associatedData sender = ok next ∧
      RecordReceiveMetadata sender sequence associatedData ciphertext next := by
  obtain ⟨context, admitted, view⟩ := payload_views ciphertext associatedData sender
  cases context with
  | none =>
    exact ⟨.Rejected kernel, by simp only [record_effects.begin_record_receive, admitted, bind_tc_ok], trivial⟩
  | some context =>
    obtain ⟨effect, begun, scope⟩ := RawCtxOwnerProvenance.begin_scope kernel sequence context
    obtain ⟨next, normalized, metadata⟩ :=
      normalize_metadata sender sequence associatedData ciphertext context effect scope view.2
    exact ⟨next, by
      simpa only [record_effects.begin_record_receive, admitted, begun, bind_tc_ok] using normalized, metadata⟩

/-- Every actual typed KDF reply preserves the requested target and original admitted context. -/
theorem kdf_metadata (sender sequence : Std.U64) (associatedData : Std.Array Std.U8 281#usize)
    (ciphertext : Slice Std.U8) (pending : record_effects.RecordReceiveKdf)
    (response : RatchetKdfResponse)
    (metadata : RecordReceiveMetadata sender sequence associatedData ciphertext (.KdfRequested pending)) :
    ∃ next, pending.resume response = ok next ∧
      RecordReceiveMetadata sender sequence associatedData ciphertext next := by
  obtain ⟨effect, resumed, scope⟩ := RawCtxOwnerProvenance.resume_scope pending.pending response
  obtain ⟨next, normalized, kept⟩ := normalize_metadata sender sequence associatedData ciphertext
    pending.pending.context effect (metadata.1 ▸ scope) metadata.2
  exact ⟨next, by
    simpa only [record_effects.RecordReceiveKdf.resume, resumed, bind_tc_ok] using normalized, kept⟩

/-- Both actual commitment-check outcomes preserve the complete source-selected metadata whenever a live phase remains. -/
theorem commitment_metadata (sender sequence : Std.U64)
    (associatedData : Std.Array Std.U8 281#usize) (ciphertext : Slice Std.U8)
    (pending : record_effects.RecordReceiveCommitment) (matched : Bool)
    (metadata : RecordReceiveMetadata sender sequence associatedData ciphertext
      (.CommitmentRequested pending)) :
    ∃ next, pending.resume matched = ok next ∧
      RecordReceiveMetadata sender sequence associatedData ciphertext next := by
  cases matched with
  | false =>
    exact ⟨.Rejected pending.pending.opening.entry, rfl, trivial⟩
  | true =>
    exact ⟨.AeadRequested ⟨⟨pending.pending.opening⟩⟩, rfl, metadata⟩

/-- Exposing and replacing the hash transcript never replaces the retained opening capability or its metadata. -/
theorem transcript_metadata (sender sequence : Std.U64)
    (associatedData : Std.Array Std.U8 281#usize) (ciphertext : Slice Std.U8)
    (pending : record_effects.RecordReceiveCommitment)
    (metadata : RecordReceiveMetadata sender sequence associatedData ciphertext
      (.CommitmentRequested pending)) :
    ∃ current put, pending.transcript_mut = ok (current, put) ∧
      ∀ transcript, RecordReceiveMetadata sender sequence associatedData ciphertext
        (.CommitmentRequested (put transcript)) := by
  exact ⟨pending.pending.transcript,
    fun transcript => ⟨{ pending.pending with transcript := transcript }⟩,
    rfl, fun _ => metadata⟩

/-- The final source-owned AEAD capability selects the admitted sender, full associated data and original target sequence. -/
theorem aead_metadata_fields (sender sequence : Std.U64)
    (associatedData : Std.Array Std.U8 281#usize) (ciphertext : Slice Std.U8)
    (pending : record_effects.RecordReceiveAead)
    (metadata : RecordReceiveMetadata sender sequence associatedData ciphertext
      (.AeadRequested pending)) :
    pending.pending.opening.context.sender_kid = sender ∧
      pending.pending.opening.context.associated_data = associatedData ∧
      pending.pending.opening.sequence = ok sequence := by
  exact ⟨metadata.2.2.2.2.2, metadata.2.2.2.2.1, metadata.1⟩

/--
info: 'BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.normalize_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalize_metadata
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.begin_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms begin_metadata
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.kdf_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms kdf_metadata
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.commitment_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms commitment_metadata
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.transcript_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms transcript_metadata
/--
info: 'BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant.aead_metadata_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms aead_metadata_fields

end BeaconcryptCore.Refinement.RecordEffectsReceiveInvariant
