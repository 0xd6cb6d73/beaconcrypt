-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Refinement.RegistrationBytePrimitives
import BeaconcryptCore.Refinement.TranscriptAuth

/-! Exact outbound signing requests and continuations. Signatures and hashes remain actual external replies; these facts prove the core's selection, admission and retention. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationBytePrimitives

set_option autoImplicit false
set_option maxRecDepth 2048

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
  | .HashRequested after => replyTailMatches before reply ∧
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
      have hashInput (state : registration.BeaconInitState) :
          ∃ output, authentication.build_init_transcript
            ⟨state.started.message.identity_key, state.pre_key, state.one_time_key, state.pq_key⟩
            state.server_pin.binding.identity_key_id state.server_pin.binding.identity_public_key
            state.server_pin.public_key = ok output := by
        obtain ⟨output, ran, _⟩ := TranscriptAuthRefinement.build_init_transcript_abs
          ⟨state.started.message.identity_key, state.pre_key, state.one_time_key, state.pq_key⟩
          state.server_pin.binding.identity_key_id state.server_pin.binding.identity_public_key
          state.server_pin.public_key
        exact ⟨output, ran⟩
      cases stageEq : self.stage with
      | PreKey =>
        cases narrow
        all_goals simp only [narrowRun, bind_tc_ok]
        all_goals refine ⟨_, rfl, ?_⟩
        all_goals simp [EdReplyTransition, stageEq, replyValues, narrowShape, admitted]
      | OneTimeKey =>
        cases narrow
        all_goals simp only [narrowRun, bind_tc_ok]
        all_goals refine ⟨_, rfl, ?_⟩
        all_goals simp [EdReplyTransition, stageEq, replyValues, narrowShape, admitted]
      | PqKey =>
        cases wide with
        | Err error =>
          simp only [wideRun, bind_tc_ok]
          exact ⟨_, rfl, rfl⟩
        | Ok bytes =>
          obtain ⟨input, inputRun⟩ := hashInput {self.state with pq_key := bytes}
          dsimp only at inputRun
          simp only [wideRun, bind_tc_ok, registration.BeaconInitState.fields,
            pqxdh.InitKex.impl.identity_key, session.ServerAuthenticationPin.impl.binding, session.ServerAuthenticationPin.impl.public_key,
            inputRun]
          refine ⟨_, rfl, ?_⟩
          simp [EdReplyTransition, stageEq, replyValues, wideShape, admitted]

/-- The final attached signature selects the exact canonical request-hash input of the retained four fields and Server pin. -/
theorem final_hash_input_exact (before : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice Std.U8)) (after : registration.BeaconInitHash)
    (resumed : before.resume reply = ok (.HashRequested after)) :
    authentication.build_init_transcript
      ⟨after.state.started.message.identity_key, after.state.pre_key, after.state.one_time_key, after.state.pq_key⟩
      after.state.server_pin.binding.identity_key_id after.state.server_pin.binding.identity_public_key
      after.state.server_pin.public_key = ok after.input := by
  obtain ⟨effect, ran, progress⟩ := ed_resume_refines before reply
  have same : effect = .HashRequested after := RustM.ok.inj (ran.symm.trans resumed)
  subst effect
  have stage : before.stage = .PqKey := progress.2.1
  cases reply with
  | none => cases resumed
  | some signed =>
    obtain ⟨suffix, suffixRun, _suffixShape⟩ := suffix_exact signed 64#usize
    obtain ⟨request, requestRun, _requestShape⟩ := ed_request_exact before
    simp only [registration.BeaconEd25519Signing.resume, suffixRun, requestRun,
      optional_slice_ne_exact, bind_tc_ok, stage] at resumed
    split at resumed
    · cases resumed
    · obtain ⟨wide, wideRun, _wideShape⟩ := copied_slice_exact 1249#usize signed
      cases wide with
      | Err error => simp only [wideRun, bind_tc_ok] at resumed; cases resumed
      | Ok bytes =>
        obtain ⟨input, inputRun, _inputBytes⟩ := TranscriptAuthRefinement.build_init_transcript_abs
          ⟨before.state.started.message.identity_key, before.state.pre_key, before.state.one_time_key, bytes⟩
          before.state.server_pin.binding.identity_key_id before.state.server_pin.binding.identity_public_key
          before.state.server_pin.public_key
        simp only [wideRun, bind_tc_ok, registration.BeaconInitState.fields,
          pqxdh.InitKex.impl.identity_key, session.ServerAuthenticationPin.impl.binding,
          session.ServerAuthenticationPin.impl.public_key, inputRun] at resumed
        have exactState : (⟨{ before.state with pq_key := bytes }, input⟩ : registration.BeaconInitHash) = after := by
          simpa only [RustM.ok.injEq, registration.BeaconInitEffect.HashRequested.injEq] using resumed
        cases exactState
        exact inputRun

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

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigning.final_hash_input_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigning.final_hash_input_exact
