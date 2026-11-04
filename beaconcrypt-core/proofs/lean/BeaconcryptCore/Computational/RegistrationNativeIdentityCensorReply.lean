-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationPair
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource
import BeaconcryptCore.Computational.RegistrationRawSealBridge

/-! Canonical and placeholder source service replies are packed by the actual frontend into fixed98-byte attachments. The original one-time continuation's tail checks and widths follow from that literal packing, rather than being supplied as callback premises. The complete actual failed-publication suffix then has the checked same-observation/shared-state coupling. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply
open BeaconcryptCore.Refinement
open ProtocolComposition (concreteByte)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {E Platform : Type}

def buffer (signature : Ed25519Signature) (message : Std.Array U8 34#usize) : Std.Array U8 98#usize :=
  ⟨signature.toList.map concreteByte ++ message.val, by
    simp only [List.length_append, List.length_map, List.Vector.toList_length]
    rw [message.property]
    rfl⟩

/-- The actual frontend byte packer returns the complete fixed-width signature attachment. -/
theorem packed (signature : Ed25519Signature) (message : Std.Array U8 34#usize) :
    RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ absBytes message)) =
      .Some (buffer signature message).to_slice := by
  have bytes : TranscriptAuthParts.absSlice (buffer signature message).to_slice = signature.toList ++ absBytes message := by
    simp [TranscriptAuthParts.absSlice, buffer, Std.Array.to_slice, absBytes, List.map_map, Function.comp_def]
  rw [← bytes]
  exact RegistrationRawSealBridge.opened_roundtrip _

/-- Any source service signature, including the censor's known placeholder, meets the literal actual one-time tail gate and width. -/
theorem admitted (pending : registration.BeaconEd25519Signing) (signature : Ed25519Signature)
    (stage : pending.stage = .OneTimeKey) :
    RegistrationSigning.replyTailMatches pending (.Some (buffer signature pending.state.started.message.one_time_key).to_slice) ∧
      (buffer signature pending.state.started.message.one_time_key).to_slice.val.length = 98 := by
  have size : (signature.toList.map concreteByte).length = 64 := by simp only [List.length_map, List.Vector.toList_length]
  constructor
  · change 64 ≤ (signature.toList.map concreteByte ++ pending.state.started.message.one_time_key.val).length ∧
      (signature.toList.map concreteByte ++ pending.state.started.message.one_time_key.val).drop 64 = RegistrationSigning.signingMessageValues pending
    constructor
    · simp only [List.length_append, size, Std.Array.length_eq]
      omega
    · have dropped : (signature.toList.map concreteByte ++ pending.state.started.message.one_time_key.val).drop
          (signature.toList.map concreteByte).length = pending.state.started.message.one_time_key.val := by
        rw [List.drop_append_length]
      simpa only [size, RegistrationSigning.signingMessageValues, stage] using dropped
  · exact (buffer signature pending.state.started.message.one_time_key).property

/-- Real and censored actual source replies enter the original paired suffix without any assumed tail, size or source-controller equality. -/
theorem paired (hash : Option Pqxdh.Bytes → StateT Platform ProbComp CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (ed : registration.Ed25519SigningRequest → StateT Platform ProbComp RegistrationSigningShared.SignReply)
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (other : RegistrationSerializerReachableSource.OtherBranches) (pending : registration.BeaconEd25519Signing)
    (canonical placeholder : Ed25519Signature) (stage : pending.stage = .OneTimeKey) (before : Platform) :
    ∃ nextLeft nextRight,
      pending.resume (RegistrationAuthenticationShared.openedBytes
        (some (canonical.toList ++ absBytes pending.state.started.message.one_time_key))) = .ok (.Ed25519SigningRequested nextLeft) ∧
      pending.resume (RegistrationAuthenticationShared.openedBytes
        (some (placeholder.toList ++ absBytes pending.state.started.message.one_time_key))) = .ok (.Ed25519SigningRequested nextRight) ∧
      Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (RegistrationNativeIdentityPublicationPair.callbacks hash sign ed)
          (RegistrationNativeSourceWriterFailureView.writer reserve other) nextLeft).run before =
      Prod.map RegistrationNativeIdentityReadyFailure.observe id <$>
        (RegistrationNativePlatformBeaconPublication.fromEd (RegistrationNativeIdentityPublicationPair.callbacks hash sign ed)
          (RegistrationNativeSourceWriterFailureView.writer reserve other) nextRight).run before := by
  have left := admitted pending canonical stage
  have right := admitted pending placeholder stage
  obtain ⟨nextLeft, nextRight, resumedLeft, resumedRight, coupled⟩ :=
    RegistrationNativeIdentityPublicationPair.one_time hash sign ed reserve other pending
      (buffer canonical pending.state.started.message.one_time_key).to_slice
      (buffer placeholder pending.state.started.message.one_time_key).to_slice stage left.1 right.1 left.2 right.2 before
  exact ⟨nextLeft, nextRight, (packed canonical _).symm ▸ resumedLeft,
    (packed placeholder _).symm ▸ resumedRight, coupled⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply.packed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply.packed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorReply.paired
