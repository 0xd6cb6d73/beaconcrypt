-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Refinement.RegistrationBytePrimitives

/-! Exact outbound signing requests and continuations. Signatures and hashes remain actual external replies; these facts prove the core's selection, admission and retention. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationBytePrimitives

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationSigning

/-- The protocol's original prekey, one-time-key, PQ-key signing order. -/
def signingMessageValues (pending : registration.BeaconEd25519Signing) : List Std.U8 :=
  match pending.stage with
  | .PreKey => pending.state.started.message.prekey.val
  | .OneTimeKey => pending.state.started.message.one_time_key.val
  | .PqKey => pending.state.started.message.pq_key.val

/-- Every attached-signature request selects the owner's key and the exact tagged public message. -/
theorem ed_request_exact (pending : registration.BeaconEd25519Signing) :
    ∃ request, pending.request = ok request ∧
      request.public_key = pending.state.beacon_identity ∧ request.role = .Beacon ∧
      request.message.val = signingMessageValues pending := by
  cases stageEq : pending.stage
  all_goals simp only [registration.BeaconEd25519Signing.request, stageEq, signingMessageValues]
  all_goals exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- A checked suffix borrow returns normally and retains every byte through the end of the signed message. -/
theorem suffix_exact (bytes : Slice Std.U8) (start : Std.Usize) :
    ∃ result, core.slice.Slice.get
      (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
      bytes ⟨start⟩ = ok result ∧
      match result with
      | .None => bytes.val.length < start.val
      | .Some suffix => start.val ≤ bytes.val.length ∧
          suffix.val = bytes.val.slice start.val bytes.val.length := by
  by_cases inside : start.val ≤ bytes.val.length
  all_goals simp [core.slice.Slice.get,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice,
    Slice.subslice, UScalar.le_equiv, Slice.length, inside]
  case pos => exact ⟨_, rfl, rfl⟩
  case neg => exact Nat.lt_of_not_ge inside

def replyValues : core.option.Option (Slice Std.U8) → List Std.U8
  | .None => []
  | .Some bytes => bytes.val

/-- The complete attached-message suffix must equal the selected signing request. -/
def replyTailMatches (before : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice Std.U8)) : Prop :=
  match reply with
  | .None => False
  | .Some bytes => 64 ≤ bytes.val.length ∧ bytes.val.drop 64 = signingMessageValues before

/-- Each accepted attached signature advances one stage, copies the actual complete reply and changes only its selected field. -/
def EdReplyTransition (before : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice Std.U8)) :
    registration.BeaconInitEffect → Prop
  | .Rejected original => original = before.state.original_control
  | .Ed25519SigningRequested after => replyTailMatches before reply ∧ match before.stage with
      | .PreKey => after.stage = .OneTimeKey ∧ after.state.pre_key.val = replyValues reply ∧
          { after.state with pre_key := before.state.pre_key } = before.state
      | .OneTimeKey => after.stage = .PqKey ∧ after.state.one_time_key.val = replyValues reply ∧
          { after.state with one_time_key := before.state.one_time_key } = before.state
      | .PqKey => False
  | .FingerprintRequested after => replyTailMatches before reply ∧
      before.stage = .PqKey ∧ after.state.pq_key.val = replyValues reply ∧
      { after.state with pq_key := before.state.pq_key } = before.state
  | _ => False

theorem matched_reply_tail (before : registration.BeaconEd25519Signing)
    (signed : Slice Std.U8) (suffix : core.option.Option (Slice Std.U8))
    (request : registration.Ed25519SigningRequest)
    (suffixShape : match suffix with
      | .None => signed.val.length < 64
      | .Some tail => 64 ≤ signed.val.length ∧
          tail.val = signed.val.slice 64 signed.val.length)
    (requestShape : request.message.val = signingMessageValues before)
    (matching : ¬ decide (optionalSliceValues suffix ≠
      optionalSliceValues (.Some request.message)) = true) :
    replyTailMatches before (.Some signed) := by
  have equal : optionalSliceValues suffix = optionalSliceValues (.Some request.message) := by
    simpa using matching
  cases suffix with
  | none => simp [optionalSliceValues] at equal
  | some suffix =>
    simpa [replyTailMatches, List.slice, List.take_of_length_le] using
      And.intro suffixShape.1
        (suffixShape.2.symm.trans ((Option.some.inj equal).trans requestShape))

/-- All replies return normally, preserving the original owner and the exact prekey/one-time/PQ order. -/
theorem ed_resume_refines (self : registration.BeaconEd25519Signing)
    (signed : core.option.Option (Slice Std.U8)) :
    ∃ result, self.resume signed = ok result ∧ EdReplyTransition self signed result := by
  cases signed with
  | none => exact ⟨_, rfl, rfl⟩
  | some signed =>
    obtain ⟨suffix, suffixRun, suffixShape⟩ := suffix_exact signed 64#usize
    obtain ⟨request, requestRun, requestShape⟩ := ed_request_exact self
    simp only [registration.BeaconEd25519Signing.resume, suffixRun, requestRun,
      optional_slice_ne_exact, bind_tc_ok]
    split
    · exact ⟨_, rfl, rfl⟩
    · have admitted : replyTailMatches self (.Some signed) :=
        matched_reply_tail self signed suffix request (by simpa using suffixShape)
          requestShape.2.2 (by assumption)
      obtain ⟨narrow, narrowRun, narrowShape⟩ := copied_slice_exact 98#usize signed
      obtain ⟨wide, wideRun, wideShape⟩ := copied_slice_exact 1249#usize signed
      cases stageEq : self.stage
      all_goals cases narrow
      all_goals cases wide
      all_goals simp only [narrowRun, wideRun, bind_tc_ok]
      all_goals refine ⟨_, rfl, ?_⟩
      all_goals simp [EdReplyTransition, stageEq, replyValues, narrowShape, wideShape, admitted]

/-- A missing or mismatched attached-message suffix rejects with the original Fresh control. -/
theorem bad_suffix_rejects (before : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice Std.U8)) (invalid : ¬ replyTailMatches before reply) :
    before.resume reply = ok (.Rejected before.state.original_control) := by
  obtain ⟨result, run, progress⟩ := ed_resume_refines before reply
  cases result <;> simp_all [EdReplyTransition]

end BeaconcryptCore.Refinement.RegistrationSigning

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigning.ed_request_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigning.suffix_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigning.suffix_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigning.matched_reply_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigning.matched_reply_tail
/-- info: 'BeaconcryptCore.Refinement.RegistrationSigning.bad_suffix_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigning.bad_suffix_rejects
