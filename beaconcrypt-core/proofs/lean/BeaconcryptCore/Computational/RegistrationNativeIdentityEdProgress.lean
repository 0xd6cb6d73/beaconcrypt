-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.Refinement.RegistrationSigning

/-! Positive source Ed continuation receipts use only the literal attached reply tail and fixed source width. They retain the actual copied array and original state through each of the three stages. This is a deterministic control-flow fact; no signature security or desired publication conclusion is assumed. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress
open BeaconcryptCore.Refinement
open RegistrationSigning (replyTailMatches)
open RegistrationBytePrimitives (optionalSliceValues)

def afterCopy (before : registration.BeaconEd25519Signing) (signed : Slice U8) : RustM registration.BeaconInitEffect :=
  match before.stage with
  | .PreKey => do
      let copied ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from 98#usize core.U8.Insts.CoreMarkerCopy signed
      match copied with
      | .Ok bytes => pure (.Ed25519SigningRequested ⟨{before.state with pre_key := bytes}, .OneTimeKey⟩)
      | .Err _ => pure (.Rejected before.state.original_control)
  | .OneTimeKey => do
      let copied ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from 98#usize core.U8.Insts.CoreMarkerCopy signed
      match copied with
      | .Ok bytes => pure (.Ed25519SigningRequested ⟨{before.state with one_time_key := bytes}, .PqKey⟩)
      | .Err _ => pure (.Rejected before.state.original_control)
  | .PqKey => do
      let copied ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from 1249#usize core.U8.Insts.CoreMarkerCopy signed
      match copied with
      | .Ok bytes => do
          let state := {before.state with pq_key := bytes}
          let input ← authentication.build_init_transcript
            ⟨state.started.message.identity_key, state.pre_key, state.one_time_key, state.pq_key⟩
            state.server_pin.binding.identity_key_id state.server_pin.binding.identity_public_key state.server_pin.public_key
          pure (.HashRequested ⟨state,input⟩)
      | .Err _ => pure (.Rejected before.state.original_control)

private theorem matched (before : registration.BeaconEd25519Signing) (signed : Slice U8)
    (matching : replyTailMatches before (.Some signed)) : before.resume (.Some signed) = afterCopy before signed := by
  obtain ⟨suffix, suffixRun, suffixShape⟩ := RegistrationSigning.suffix_exact signed 64#usize
  obtain ⟨request, requestRun, requestShape⟩ := RegistrationSigning.ed_request_exact before
  have tail : optionalSliceValues suffix = optionalSliceValues (.Some request.message) := by
    cases suffix with
    | none => exact False.elim ((Nat.not_lt_of_ge matching.1) suffixShape)
    | some suffix =>
      apply congrArg some
      have values : suffix.val = signed.val.drop 64 := by
        have sliced : suffix.val = (signed.val.drop 64).take (signed.val.length - 64) := by
          simpa [List.slice] using suffixShape.2
        exact sliced.trans (List.take_of_length_le (by simp))
      exact values.trans (matching.2.trans requestShape.2.2.symm)
  simp only [registration.BeaconEd25519Signing.resume, suffixRun, requestRun,
    RegistrationBytePrimitives.optional_slice_ne_exact, tail, ne_eq, not_true_eq_false,
    decide_false, bind_tc_ok, Bool.false_eq_true, ite_false, afterCopy,
    registration.BeaconInitState.fields, pqxdh.InitKex.impl.identity_key,
    session.ServerAuthenticationPin.impl.binding, session.ServerAuthenticationPin.impl.public_key]
  cases before.stage <;> rfl

private theorem copied (size : Usize) (signed : Slice U8) (width : signed.val.length = size.val) :
    ∃ bytes : Std.Array U8 size,
      core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from size core.U8.Insts.CoreMarkerCopy signed = .ok (.Ok bytes) ∧
      bytes.val = signed.val := by
  obtain ⟨result, run, facts⟩ := RegistrationInputs.copied_slice_exact size signed
  cases result with
  | Ok bytes => exact ⟨bytes, run, facts.1⟩
  | Err error => exact False.elim (facts width)

/-- A matching fixed-width prekey attachment advances the literal source to one-time signing and copies every returned byte. -/
theorem prekey (before : registration.BeaconEd25519Signing) (signed : Slice U8)
    (stage : before.stage = .PreKey) (matching : replyTailMatches before (.Some signed)) (width : signed.val.length = 98) :
    ∃ next, before.resume (.Some signed) = .ok (.Ed25519SigningRequested next) ∧ next.stage = .OneTimeKey ∧
      next.state.pre_key.val = signed.val ∧ {next.state with pre_key := before.state.pre_key} = before.state := by
  obtain ⟨bytes, run, values⟩ := copied 98#usize signed width
  refine ⟨⟨{before.state with pre_key := bytes}, .OneTimeKey⟩, ?_, rfl, values, rfl⟩
  rw [matched before signed matching]
  simp only [afterCopy, stage, run, bind_tc_ok]
  rfl

/-- The actual one-time stage copies the complete attachment before advancing to PQ signing. -/
theorem one_time (before : registration.BeaconEd25519Signing) (signed : Slice U8)
    (stage : before.stage = .OneTimeKey) (matching : replyTailMatches before (.Some signed)) (width : signed.val.length = 98) :
    ∃ next, before.resume (.Some signed) = .ok (.Ed25519SigningRequested next) ∧ next.stage = .PqKey ∧
      next.state.one_time_key.val = signed.val ∧ {next.state with one_time_key := before.state.one_time_key} = before.state := by
  obtain ⟨bytes, run, values⟩ := copied 98#usize signed width
  refine ⟨⟨{before.state with one_time_key := bytes}, .PqKey⟩, ?_, rfl, values, rfl⟩
  rw [matched before signed matching]
  simp only [afterCopy, stage, run, bind_tc_ok]
  rfl

/-- The actual PQ stage reaches the canonical request hash with all returned bytes and every other source field retained. -/
theorem pq_key (before : registration.BeaconEd25519Signing) (signed : Slice U8)
    (stage : before.stage = .PqKey) (matching : replyTailMatches before (.Some signed)) (width : signed.val.length = 1249) :
    ∃ next, before.resume (.Some signed) = .ok (.HashRequested next) ∧
      next.state.pq_key.val = signed.val ∧ {next.state with pq_key := before.state.pq_key} = before.state := by
  obtain ⟨bytes, run, values⟩ := copied 1249#usize signed width
  let state := {before.state with pq_key := bytes}
  obtain ⟨input,inputRun,_⟩ := TranscriptAuthRefinement.build_init_transcript_abs
    ⟨state.started.message.identity_key,state.pre_key,state.one_time_key,state.pq_key⟩
    state.server_pin.binding.identity_key_id state.server_pin.binding.identity_public_key state.server_pin.public_key
  refine ⟨⟨state,input⟩, ?_, values, rfl⟩
  rw [matched before signed matching]
  simp only [afterCopy, stage, run, bind_tc_ok]
  dsimp only [state] at inputRun
  rw [inputRun]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress.prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress.prekey
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress.one_time
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress.pq_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEdProgress.pq_key
