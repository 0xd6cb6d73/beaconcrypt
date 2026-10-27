-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.Refinement.SessionBinding

/-!
The production agreement phases select the role-specific four-DH plan and retain the authenticated inputs through KEM, root construction and completion. Primitive execution and secret-handle provenance remain interpreter obligations.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.KeyAgreement

/-- The protocol's ordered DH operands, independently of the phase discriminator. -/
def dhPlan (state : agreement.AgreementState) :
    List (agreement.DhSecretRole × Array Std.U8 32#usize) :=
  match state.input with
  | .Server _ _ registration _ =>
    [(.LocalIdentity, registration.beacon_prekey_public_key),
     (.ServerEphemeral, state.remote_identity),
     (.ServerEphemeral, registration.beacon_prekey_public_key),
     (.ServerEphemeral, registration.beacon_one_time_public_key)]
  | .Beacon _ _ response _ =>
    [(.BeaconPrekey, state.remote_identity),
     (.LocalIdentity, response.ephemeral_key),
     (.BeaconPrekey, response.ephemeral_key),
     (.BeaconOneTime, response.ephemeral_key)]

def positionIndex : agreement.DhPosition → Nat
  | .First => 0
  | .Second => 1
  | .Third => 2
  | .Fourth => 3

/-- Each actual request is the corresponding entry of the intended ordered protocol plan. -/
theorem dh_request_refines (pending : agreement.DhPending) :
    ∃ request, agreement.DhPending.request pending = ok request ∧
      (dhPlan pending.state)[positionIndex pending.position]? =
        some (request.secret_role, request.public_key) := by
  cases inputEq : pending.state.input
  all_goals cases positionEq : pending.position
  all_goals simp [agreement.DhPending.request, inputEq, positionEq, dhPlan, positionIndex,
    pqxdh.VerifiedInitKex.impl.beacon_prekey_public_key,
    pqxdh.VerifiedInitKex.impl.beacon_one_time_public_key]

/-- Every failed conversion, generation, KEM or DH reply takes the retained rejection path. -/
theorem primitive_failures_reject (state : agreement.AgreementState)
    (position : agreement.DhPosition) :
    agreement.PublicConversionPending.resume ⟨state⟩ .None = state.reject ∧
    agreement.SecretConversionPending.resume ⟨state⟩ false = state.reject ∧
    agreement.EphemeralPending.resume ⟨state⟩ .None = state.reject ∧
    agreement.EncapsulationPending.resume ⟨state⟩ .None = state.reject ∧
    agreement.DecapsulationPending.resume ⟨state⟩ .None = state.reject ∧
    agreement.DhPending.resume ⟨state, position⟩ .None = state.reject := by
  simp [agreement.PublicConversionPending.resume, agreement.SecretConversionPending.resume,
    agreement.EphemeralPending.resume, agreement.EncapsulationPending.resume,
    agreement.DecapsulationPending.resume, agreement.DhPending.resume]

/-- Server rejection is neutral; Beacon rejection carries the retained pinned server ID. -/
def abortFor : agreement.AgreementInput → core.option.Option pqxdh.BeaconAborted
  | .Server _ _ _ _ => .None
  | .Beacon control _ _ _ =>
      .Some ⟨control.expected_server_binding.identity_key_id⟩

theorem rejection_refines (state : agreement.AgreementState) :
    state.reject = ok (.Rejected (abortFor state.input)) := by
  cases inputEq : state.input
  all_goals simp [agreement.AgreementState.reject, abortFor, inputEq, pqxdh.beacon_abort_init]

/-- The source driver only advances a DH capability; a rejected result stays rejected. -/
def resumeDh (effect : agreement.AgreementEffect)
    (reply : core.option.Option (Array Std.U8 32#usize)) : RustM agreement.AgreementEffect :=
  match effect with
  | .Dh pending => pending.resume reply
  | other => ok other

/-- Interpret exactly the four source DH continuations in their production order. -/
def fourDh (state : agreement.AgreementState)
    (first second third fourth : Array Std.U8 32#usize) : RustM agreement.AgreementEffect := do
  let effect ← agreement.DhPending.resume ⟨state, .First⟩ (.Some first)
  let effect ← resumeDh effect (.Some second)
  let effect ← resumeDh effect (.Some third)
  resumeDh effect (.Some fourth)

/-- Root admission uses precisely the four ordered replies, retaining all earlier KEM and owner fields. -/
theorem four_dh_refines (state : agreement.AgreementState)
    (first second third fourth : Array Std.U8 32#usize) :
    fourDh state first second third fourth = agreement.finish_dh
      { state with dh1 := ⟨first⟩, dh2 := ⟨second⟩, dh3 := ⟨third⟩, dh4 := ⟨fourth⟩ } := by
  simp [fourDh, resumeDh, agreement.DhPending.resume, ratchet.RatchetChain.from_bytes]

/-- The root transcript before erasure belongs to this retained registration candidate. -/
def candidateInput : agreement.AgreementCandidate → Array Std.U8 192#usize
  | .Server pending _ => pending.root_key_input.bytes
  | .Beacon candidate _ _ => candidate.root_key_input.bytes

/-- Root HKDF receives the retained preimage and fixed PQXDH domain, with its typed 32-byte reply. -/
theorem root_request_refines (pending : agreement.RootKdfPending) :
    ∃ request, pending.request = ok request ∧
      request.input = candidateInput pending.candidate ∧ request.info = pqxdh.PQXDH_INFO := by
  cases candidateEq : pending.candidate
  all_goals simp [agreement.RootKdfPending.request, candidateEq, candidateInput,
    pqxdh.PendingServerRegistration.impl.root_key_input,
    pqxdh.BeaconRegistrationCandidate.impl.root_key_input, pqxdh.RootKeyInput.as_bytes]

/-- A successful root reply erases only the preimage and retains the exact owner, ciphertext and root reply. -/
theorem root_success_refines (pending : agreement.RootKdfPending)
    (reply : Array Std.U8 32#usize) :
    pending.resume (.Some reply) = ok (match pending.candidate with
      | .Server candidate binding => .ServerComplete
        ⟨{ candidate with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, binding, ⟨reply⟩⟩
      | .Beacon candidate binding ciphertext => .BeaconComplete
        ⟨{ candidate with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, binding, ⟨reply⟩, ciphertext⟩) := by
  cases candidateEq : pending.candidate
  all_goals simp [agreement.RootKdfPending.resume, candidateEq,
    pqxdh.PendingServerRegistration.root_key_input_mut,
    pqxdh.BeaconRegistrationCandidate.root_key_input_mut, pqxdh.RootKeyInput.clear,
    ratchet.RatchetChain.from_bytes]

/-- The four DH replies and retained KEM result admitted into the old checked transcript builder. -/
def stateSecrets (state : agreement.AgreementState) : pqxdh.PqxdhSharedSecrets :=
  ⟨state.dh1.bytes, state.dh2.bytes, state.dh3.bytes, state.dh4.bytes, state.kem.bytes⟩

/-- Successful server admission retains the generated coins and exact FF/DH1/DH2/DH3/DH4/KEM transcript. -/
theorem server_root_admission_refines (state : agreement.AgreementState)
    (control : pqxdh.ServerState) (registration : pqxdh.VerifiedInitKex)
    (binding : session.RegistrationBinding)
    (nonzero : Pqxdh.dhNonZero (absDHs (stateSecrets state))) :
    ∃ pending : pqxdh.PendingServerRegistration,
      agreement.finish_dh { state with input := .Server control .Fresh registration binding } =
        ok (.RootKdf ⟨.Server pending binding⟩) ∧
      pending.server_binding = binding.server_pin.binding ∧
      pending.ephemeral_public_key = state.ephemeral_public_key ∧
      pending.kem_ciphertext = state.kem_ciphertext ∧
      absBytes pending.registration_id.bytes = (absVerified registration).rid ∧
      absBytes pending.root_key_input.bytes =
        Pqxdh.pqxdhIKM (absBytes state.dh1.bytes) (absBytes state.dh2.bytes)
          (absBytes state.dh3.bytes) (absBytes state.dh4.bytes) (absBytes state.kem.bytes) := by
  obtain ⟨root, rootEq, rootBytes⟩ := (build_root_key_input_abs (stateSecrets state)).1 nonzero
  obtain ⟨rid, ridEq, ridBytes⟩ := registration_id_abs registration
  simp only [stateSecrets] at rootEq
  refine ⟨⟨binding.server_pin.binding, rid, registration.beacon_identity_public_key,
    state.ephemeral_public_key, state.kem_ciphertext, root⟩, ?_, rfl, rfl, rfl, ridBytes, rootBytes⟩
  simp [agreement.finish_dh, ratchet.RatchetChain.as_bytes,
    session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
    pqxdh.server_accept, pqxdh.validate_registration_status, rootEq, ridEq]

/-- Beacon admission uses the same ordered transcript, after checking the retained Ed25519 identity. -/
theorem beacon_root_admission_refines (state : agreement.AgreementState)
    (control : pqxdh.BeaconInitSent) (binding : session.RegistrationBinding)
    (response : agreement.ResponsePublic) (ciphertext : Slice Std.U8)
    (identity : response.identity_key = control.expected_server_binding.identity_public_key)
    (nonzero : Pqxdh.dhNonZero (absDHs (stateSecrets state))) :
    ∃ candidate : pqxdh.BeaconRegistrationCandidate,
      agreement.finish_dh { state with input := .Beacon control binding response ciphertext } =
        ok (.RootKdf ⟨.Beacon candidate binding ciphertext⟩) ∧
      candidate.server_binding = control.expected_server_binding ∧
      candidate.assigned_key_id = response.key_id ∧
      absBytes candidate.root_key_input.bytes =
        Pqxdh.pqxdhIKM (absBytes state.dh1.bytes) (absBytes state.dh2.bytes)
          (absBytes state.dh3.bytes) (absBytes state.dh4.bytes) (absBytes state.kem.bytes) := by
  obtain ⟨root, rootEq, rootBytes⟩ := (build_root_key_input_abs (stateSecrets state)).1 nonzero
  obtain ⟨associatedData, associatedDataEq⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok
    control.expected_server_binding.identity_public_key control.beacon_identity_public_key
  refine ⟨⟨control.expected_server_binding, response.key_id, root, associatedData⟩,
    ?_, rfl, rfl, rootBytes⟩
  simp only [stateSecrets] at rootEq
  simp [agreement.finish_dh, ratchet.RatchetChain.as_bytes, pqxdh.beacon_prepare_finish,
    array_eq_abs, identity, rootEq, associatedDataEq]

/-- Replay rejection precedes all effects; a fresh entry retains the complete authenticated input. -/
theorem server_entry_refines (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) :
    agreement.begin_server_agreement control .Consumed authenticated = ok (.Rejected .None) ∧
    agreement.begin_server_agreement control .Fresh authenticated = (do
      let state ← agreement.AgreementState.new
        (.Server control .Fresh authenticated.registration authenticated.binding)
      ok (.GenerateEphemeral ⟨state⟩)) := by
  simp [agreement.begin_server_agreement, pqxdh.validate_registration_status,
    core.result.Result.is_err, registration.AuthenticatedInit.into_parts]

/-- The Beacon starts from the retained request control and binding, never from a reconstructed control value. -/
theorem beacon_entry_refines (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding =
      authenticated.pending.binding.server_pin.binding) :
    agreement.begin_beacon_agreement authenticated = (do
      let state ← agreement.AgreementState.new (.Beacon authenticated.pending.control
        authenticated.pending.binding authenticated.packet.public authenticated.packet.application)
      ok (.ConvertPublic ⟨state⟩)) := by
  simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
    pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
    session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
    array_eq_abs, coherent]

/-- Generated and decapsulated replies stay in the same owner capability through later phases. -/
theorem generated_replies_retained (state : agreement.AgreementState)
    (ephemeral : Array Std.U8 32#usize) (ciphertext : Array Std.U8 1088#usize)
    (shared converted : Array Std.U8 32#usize) :
    agreement.EphemeralPending.resume ⟨state⟩ (.Some ephemeral) =
      ok (.Encapsulate ⟨{ state with ephemeral_public_key := ephemeral }⟩) ∧
    agreement.EncapsulationPending.resume ⟨state⟩ (.Some (ciphertext, shared)) =
      ok (.ConvertPublic ⟨{ state with kem_ciphertext := ciphertext, kem := ⟨shared⟩ }⟩) ∧
    agreement.DecapsulationPending.resume ⟨state⟩ (.Some shared) =
      ok (.Dh ⟨{ state with kem := ⟨shared⟩ }, .First⟩) ∧
    agreement.PublicConversionPending.resume ⟨state⟩ (.Some converted) =
      ok (.ConvertSecret ⟨{ state with remote_identity := converted }⟩) := by
  simp [agreement.EphemeralPending.resume, agreement.EncapsulationPending.resume,
    agreement.DecapsulationPending.resume, agreement.PublicConversionPending.resume,
    ratchet.RatchetChain.from_bytes]

/-- Conversion and KEM operands come from the retained authenticated role input. -/
theorem conversion_kem_requests_refine (state : agreement.AgreementState) :
    agreement.PublicConversionPending.public_key ⟨state⟩ = ok (match state.input with
      | .Server _ _ registration _ => registration.beacon_identity_public_key
      | .Beacon _ _ response _ => response.identity_key) ∧
    agreement.EncapsulationPending.public_key ⟨state⟩ = ok (match state.input with
      | .Server _ _ registration _ => .Some registration.beacon_pq_public_key
      | .Beacon _ _ _ _ => .None) ∧
    agreement.DecapsulationPending.ciphertext ⟨state⟩ = ok (match state.input with
      | .Server _ _ _ _ => .None
      | .Beacon _ _ response _ => .Some response.kem_cipher_text) ∧
    agreement.SecretConversionPending.secret_role ⟨state⟩ = ok .LocalIdentity ∧
    agreement.EphemeralPending.role ⟨state⟩ = ok .ServerEphemeral := by
  cases inputEq : state.input
  all_goals simp [agreement.PublicConversionPending.public_key,
    agreement.EncapsulationPending.public_key, agreement.DecapsulationPending.ciphertext,
    agreement.SecretConversionPending.secret_role, agreement.EphemeralPending.role, inputEq,
    pqxdh.VerifiedInitKex.impl.beacon_identity_public_key,
    pqxdh.VerifiedInitKex.impl.beacon_pq_public_key]

/-- A failed root derivation publishes no completion and aborts only the retained Beacon owner. -/
theorem root_failure_refines (pending : agreement.RootKdfPending) :
    pending.resume .None = ok (match pending.candidate with
      | .Server _ _ => .Rejected .None
      | .Beacon candidate _ _ => .Rejected (.Some ⟨candidate.server_binding.identity_key_id⟩)) := by
  cases candidateEq : pending.candidate
  all_goals simp [agreement.RootKdfPending.resume, candidateEq, pqxdh.beacon_abort_candidate]

/-- An all-zero DH reply never reaches root HKDF, for either role and any retained registration state. -/
theorem zero_dh_rejects (state : agreement.AgreementState)
    (invalid : ¬ Pqxdh.dhNonZero (absDHs (stateSecrets state))) :
    agreement.finish_dh state = ok (.Rejected (abortFor state.input)) := by
  have rejected := (build_root_key_input_abs (stateSecrets state)).2 invalid
  simp only [stateSecrets] at rejected
  cases inputEq : state.input
  all_goals simp [agreement.finish_dh, ratchet.RatchetChain.as_bytes, inputEq,
    session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
    pqxdh.server_accept, pqxdh.validate_registration_status, pqxdh.beacon_prepare_finish,
    array_eq_abs, rejected, abortFor, pqxdh.beacon_abort_init]
  case Server control status registration binding => cases status <;> simp
  case Beacon control binding response ciphertext => split <;> simp

end BeaconcryptCore.Refinement.KeyAgreement

/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.dh_request_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.dh_request_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.primitive_failures_reject' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.primitive_failures_reject
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.rejection_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.rejection_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.four_dh_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.four_dh_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.root_request_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.root_request_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.root_success_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.root_success_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.server_root_admission_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.server_root_admission_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.beacon_root_admission_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.beacon_root_admission_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.beacon_entry_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.beacon_entry_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.generated_replies_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.generated_replies_retained
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.conversion_kem_requests_refine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.conversion_kem_requests_refine
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines
/-- info: 'BeaconcryptCore.Refinement.KeyAgreement.zero_dh_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.KeyAgreement.zero_dh_rejects
