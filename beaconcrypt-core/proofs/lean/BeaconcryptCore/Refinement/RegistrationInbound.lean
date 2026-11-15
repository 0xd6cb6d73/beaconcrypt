-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthentication
import BeaconcryptCore.Refinement.RegistrationBytePrimitives

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationBytePrimitives

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationInbound

/-- The attached Ed signature is excluded exactly at the checked 64-byte boundary. -/
theorem attached_suffix_exact (bytes : Slice Std.U8) (bound : 64 ≤ bytes.val.length) :
    ∃ suffix : Slice Std.U8,
      core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.U8)
        bytes { start := 64#usize } = ok suffix ∧ suffix.val = bytes.val.drop 64 := by
  simp only [core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeFromUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, UScalar.le_equiv, Slice.length,
    Std.UScalar.ofNatCore_val_eq, rust_primitives.slice.slice_slice,
    Slice.subslice]
  simp only [bind_tc_ok, Slice.len_val, Slice.length, bound, ite_true, le_refl, and_self]
  simp only [Bind.bind, Aeneas.Std.bind, List.slice]
  exact ⟨_, rfl, by simp⟩

/-- Successful continuations attest an exact opened attached field and the required next phase. -/
def edProgress (before : registration.InitEd25519Verification)
    (opened : core.option.Option (Slice Std.U8)) (after : registration.InitAuthentication) : Prop :=
  match after with
  | .Rejected => True
  | .Ed25519VerificationRequested next =>
      ∃ bytes, opened = .Some bytes ∧ bytes.val = (edSignedBytes before).drop 64 ∧
        next.state = before.state ∧ next.public_key = before.public_key ∧
        ((before.stage = .PqKey ∧ next.stage = .PreKey ∧ next.pre_key = before.pre_key ∧
            next.pq_key.val = bytes.val) ∨
         (before.stage = .PreKey ∧ next.stage = .OneTimeKey ∧ next.pre_key.val = bytes.val ∧
            next.pq_key = before.pq_key))
  | .Accepted next =>
      ∃ bytes, opened = .Some bytes ∧ bytes.val = (edSignedBytes before).drop 64 ∧
        before.stage = .OneTimeKey ∧
        ∃ key : Std.Array Std.U8 34#usize, key.val = bytes.val ∧
          pqxdh.validate_init_kex {
            identity_key := before.state.fields.identity_key,
            prekey := before.pre_key, one_time_key := key, pq_key := before.pq_key } =
            ok (.Ok next.registration) ∧
          next.binding.server_pin = before.state.server_pin ∧
          next.binding.init_hash = before.state.init_hash ∧
          next.binding.init_fields = before.state.fields
  | _ => False

/-- Every Ed reply, including a malformed or mismatched opened slice, returns normally. -/
theorem init_ed_resume_refines (before : registration.InitEd25519Verification)
    (opened : core.option.Option (Slice Std.U8)) :
    ∃ result, before.resume opened = ok result ∧ edProgress before opened result := by
  cases opened with
  | none => exact ⟨_, rfl, trivial⟩
  | some bytes =>
    obtain ⟨request, requestRun, requestKey, requestBytes, requestLength⟩ :=
      init_ed_request_exact before
    obtain ⟨suffix, suffixRun, suffixBytes⟩ := attached_suffix_exact request.signed requestLength
    simp only [registration.InitEd25519Verification.resume, requestRun, bind_tc_ok,
      suffixRun, authentication.OwnedInitFields.fields, bind_tc_ok, core.Shared1A.Insts.CoreCmpPartialEqShared0B.ne,
      slice_ne_exact]
    split_ifs with mismatch
    · exact ⟨_, rfl, trivial⟩
    · obtain ⟨small, smallRun, smallBytes⟩ := copied_slice_exact 34#usize bytes
      obtain ⟨large, largeRun, largeBytes⟩ := copied_slice_exact 1185#usize bytes
      cases stage : before.stage
      case PreKey => cases small <;> simp_all [edProgress]
      case OneTimeKey =>
        cases small with
        | Err error => simp_all [edProgress]
        | Ok oneTime =>
          obtain ⟨verified, verifiedRun⟩ := BeaconcryptCore.PanicFreedom.validate_init_kex_ok
            { identity_key := before.state.fields.identity_key, prekey := before.pre_key,
              one_time_key := oneTime, pq_key := before.pq_key }
          cases verified <;> simp_all [pqxdh.InitKex.from_encoded, edProgress, session.RegistrationBinding.new]
          exact ⟨oneTime, smallBytes.1, verifiedRun⟩
      case PqKey => cases large <;> simp_all [edProgress]

/-- Accepted requests retain exact fields, request digest and pin; no final AD exists at this phase. -/
theorem accepted_request_retained (before : registration.InitEd25519Verification)
    (opened : core.option.Option (Slice Std.U8)) (accepted : registration.AuthenticatedInit)
    (returned : before.resume opened = ok (.Accepted accepted)) :
    accepted.binding.server_pin = before.state.server_pin ∧
      accepted.binding.init_hash = before.state.init_hash ∧
      accepted.binding.init_fields = before.state.fields := by
  obtain ⟨result, run, progress⟩ := init_ed_resume_refines before opened
  have same : result = .Accepted accepted := RustM.ok.inj (run.symm.trans returned)
  subst result
  obtain ⟨bytes, _, _, _, key, _, _, pin, digest, fields⟩ := progress
  exact ⟨pin, digest, fields⟩

end BeaconcryptCore.Refinement.RegistrationInbound

/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.attached_suffix_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.attached_suffix_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.init_ed_resume_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.init_ed_resume_refines

/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.accepted_request_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.accepted_request_retained
