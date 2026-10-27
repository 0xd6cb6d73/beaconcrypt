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
  | .ServerFingerprintRequested next =>
      ∃ bytes, opened = .Some bytes ∧ bytes.val = (edSignedBytes before).drop 64 ∧
        before.stage = .OneTimeKey ∧ next.state = before.state ∧
        ∃ key : Std.Array Std.U8 34#usize, key.val = bytes.val ∧
          pqxdh.validate_init_kex {
            identity_key := before.state.packet.identity_key,
            prekey := before.pre_key, one_time_key := key, pq_key := before.pq_key } =
            ok (.Ok next.registration)
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
      suffixRun, core.Shared1A.Insts.CoreCmpPartialEqShared0B.ne,
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
            { identity_key := before.state.packet.identity_key, prekey := before.pre_key,
              one_time_key := oneTime, pq_key := before.pq_key }
          cases verified <;> simp_all [pqxdh.InitKex.from_encoded, edProgress]
          exact ⟨oneTime, smallBytes.1, verifiedRun⟩
      case PqKey => cases large <;> simp_all [edProgress]

/-- Authentication creates final bound AD while retaining all authenticated registration fields. -/
theorem init_beacon_fingerprint_exact (before : registration.InitBeaconFingerprint)
    (fingerprint : Std.Array Std.U8 64#usize) :
    ∃ accepted : registration.AuthenticatedInit,
      before.resume (.Some fingerprint) = ok (.Accepted accepted) ∧
      accepted.registration = before.registration ∧
      accepted.binding.server_pin = before.server_pin ∧
      accepted.binding.init_hash = before.state.init_hash ∧
      accepted.binding.beacon_identity_public_key = before.registration.beacon_identity_public_key ∧
      accepted.binding.beacon_fingerprint = fingerprint ∧
      BeaconcryptCore.Refinement.SessionBinding.registrationConsistent accepted.binding := by
  obtain ⟨binding, bindingRun, pin, digest, identity, fp, ad⟩ :=
    BeaconcryptCore.Refinement.SessionBinding.registration_new_refines before.server_pin
      before.state.init_hash before.registration.beacon_identity_public_key fingerprint
  refine ⟨⟨before.registration, binding⟩, ?_, rfl, pin, digest, identity, fp, ?_⟩
  · simp [registration.InitBeaconFingerprint.resume,
      pqxdh.VerifiedInitKex.impl.beacon_identity_public_key, bindingRun]
  · simpa [BeaconcryptCore.Refinement.SessionBinding.registrationConsistent, pin, identity, fp] using ad

/-- The selected server ML fingerprint changes only that fingerprint slot. -/
theorem init_server_fingerprint_exact (before : registration.InitServerFingerprint)
    (fingerprint : Std.Array Std.U8 64#usize) :
    ∃ next : registration.InitBeaconFingerprint,
      before.resume (.Some fingerprint) = ok (.BeaconFingerprintRequested next) ∧
      next.state = before.state ∧ next.registration = before.registration ∧
      next.server_pin.binding = before.state.server_pin.binding ∧
      next.server_pin.public_key = before.state.server_pin.public_key ∧
      next.server_pin.fingerprint = fingerprint :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Missing fingerprints stop authentication before a capability can be returned. -/
theorem missing_fingerprint_rejects (server : registration.InitServerFingerprint)
    (beacon : registration.InitBeaconFingerprint) :
    server.resume .None = ok .Rejected ∧ beacon.resume .None = ok .Rejected :=
  ⟨rfl, rfl⟩

/-- The two fingerprint requests hash the complete retained ML public keys. -/
theorem fingerprint_requests_exact (server : registration.InitServerFingerprint)
    (beacon : registration.InitBeaconFingerprint) :
    ∃ serverRequest beaconRequest,
      server.request = ok serverRequest ∧ beacon.request = ok beaconRequest ∧
      hashBytes serverRequest = absBytes server.state.server_pin.public_key ∧
      hashBytes beaconRequest = absBytes beacon.state.packet.mldsa_public_key :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

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
/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.init_beacon_fingerprint_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.init_beacon_fingerprint_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.init_server_fingerprint_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.init_server_fingerprint_exact
/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.missing_fingerprint_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.missing_fingerprint_rejects
/-- info: 'BeaconcryptCore.Refinement.RegistrationInbound.fingerprint_requests_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationInbound.fingerprint_requests_exact
