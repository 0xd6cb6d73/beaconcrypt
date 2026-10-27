-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Pqxdh

/-! Totality of the extracted agreement effects for arbitrary represented states and replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom.KeyAgreement

theorem root_key_input_clear_total (self : pqxdh.RootKeyInput) :
    ∃ result, pqxdh.RootKeyInput.clear self = ok result :=
  ⟨_, rfl⟩

theorem agreement_state_new_total (input : agreement.AgreementInput) :
    ∃ result, agreement.AgreementState.new input = ok result :=
  ⟨_, rfl⟩

theorem agreement_state_reject_total (self : agreement.AgreementState) :
    ∃ result, agreement.AgreementState.reject self = ok result := by
  cases hinput : self.input <;>
    simp [agreement.AgreementState.reject, pqxdh.beacon_abort_init, hinput]

theorem finish_dh_total (state : agreement.AgreementState) :
    ∃ result, agreement.finish_dh state = ok result := by
  cases hinput : state.input with
  | Server control status registration binding =>
    obtain ⟨accepted, haccepted⟩ := server_accept_ok control registration status binding.server_pin.binding
      { ephemeral_public_key := state.ephemeral_public_key, kem_ciphertext := state.kem_ciphertext }
      { dh1 := state.dh1.bytes, dh2 := state.dh2.bytes, dh3 := state.dh3.bytes,
        dh4 := state.dh4.bytes, kem_shared_secret := state.kem.bytes }
    cases accepted with
    | Ok pair =>
      cases pair
      simp [agreement.finish_dh, ratchet.RatchetChain.as_bytes,
        session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
        hinput, haccepted]
    | Err error =>
      simp [agreement.finish_dh, ratchet.RatchetChain.as_bytes,
        session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
        hinput, haccepted]
  | Beacon control binding response application =>
    obtain ⟨prepared, hprepared⟩ := beacon_prepare_finish_ok control
      { response_server_identity := response.identity_key, assigned_key_id := response.key_id,
        shared_secrets :=
          { dh1 := state.dh1.bytes, dh2 := state.dh2.bytes,
            dh3 := state.dh3.bytes, dh4 := state.dh4.bytes, kem_shared_secret := state.kem.bytes } }
    cases prepared <;>
      simp [agreement.finish_dh, ratchet.RatchetChain.as_bytes, pqxdh.beacon_abort_init,
        hinput, hprepared]

theorem begin_beacon_agreement_total (authenticated : registration.AuthenticatedResponse) :
    ∃ result, agreement.begin_beacon_agreement authenticated = ok result := by
  by_cases hid : authenticated.pending.control.expected_server_binding.identity_key_id =
    authenticated.pending.binding.server_pin.binding.identity_key_id
  · by_cases hkey : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      absBytes authenticated.pending.binding.server_pin.binding.identity_public_key
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, agreement.AgreementState.new, ratchet.RatchetChain.from_bytes,
        pqxdh.beacon_abort_init, hid, hkey]
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, hid, hkey]
  · have hne : authenticated.pending.control.expected_server_binding.identity_key_id.val ≠
        authenticated.pending.binding.server_pin.binding.identity_key_id.val :=
      fun h => hid (UScalar.eq_of_val_eq h)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, hne]

theorem root_kdf_resume_total (self : agreement.RootKdfPending)
    (root : core.option.Option (Array Std.U8 32#usize)) :
    ∃ result, agreement.RootKdfPending.resume self root = ok result := by
  cases root <;> cases hcandidate : self.candidate <;>
    simp [agreement.RootKdfPending.resume, pqxdh.beacon_abort_candidate,
      pqxdh.PendingServerRegistration.root_key_input_mut,
      pqxdh.BeaconRegistrationCandidate.root_key_input_mut, pqxdh.RootKeyInput.clear,
      ratchet.RatchetChain.from_bytes, hcandidate]

theorem dh_resume_total (self : agreement.DhPending)
    (shared : core.option.Option (Array Std.U8 32#usize)) :
    ∃ result, agreement.DhPending.resume self shared = ok result := by
  cases shared with
  | none => simpa [agreement.DhPending.resume] using agreement_state_reject_total self.state
  | some shared =>
    cases hposition : self.position with
    | First => simp [agreement.DhPending.resume, ratchet.RatchetChain.from_bytes, hposition]
    | Second => simp [agreement.DhPending.resume, ratchet.RatchetChain.from_bytes, hposition]
    | Third => simp [agreement.DhPending.resume, ratchet.RatchetChain.from_bytes, hposition]
    | Fourth =>
      simpa [agreement.DhPending.resume, ratchet.RatchetChain.from_bytes, hposition] using
        finish_dh_total { self.state with dh4 := { bytes := shared } }

theorem begin_server_agreement_total (control : pqxdh.ServerState)
    (status : pqxdh.RegistrationStatus) (authenticated : registration.AuthenticatedInit) :
    ∃ result, agreement.begin_server_agreement control status authenticated = ok result := by
  cases status <;>
    simp [agreement.begin_server_agreement, pqxdh.validate_registration_status,
      core.result.Result.is_err, registration.AuthenticatedInit.into_parts,
      agreement.AgreementState.new, ratchet.RatchetChain.from_bytes]

theorem public_conversion_key_total (self : agreement.PublicConversionPending) :
    ∃ result, agreement.PublicConversionPending.public_key self = ok result := by
  cases hinput : self.state.input <;>
    simp [agreement.PublicConversionPending.public_key,
      pqxdh.VerifiedInitKex.impl.beacon_identity_public_key, hinput]

theorem public_conversion_resume_total (self : agreement.PublicConversionPending)
    (converted : core.option.Option (Array Std.U8 32#usize)) :
    ∃ result, agreement.PublicConversionPending.resume self converted = ok result :=
  match converted with
  | .none => by
    simpa [agreement.PublicConversionPending.resume] using agreement_state_reject_total self.state
  | .some _ => ⟨_, rfl⟩

theorem secret_conversion_role_total (self : agreement.SecretConversionPending) :
    ∃ result, agreement.SecretConversionPending.secret_role self = ok result :=
  ⟨_, rfl⟩

theorem secret_conversion_resume_total (self : agreement.SecretConversionPending)
    (converted : Bool) :
    ∃ result, agreement.SecretConversionPending.resume self converted = ok result := by
  cases converted with
  | false =>
    simpa [agreement.SecretConversionPending.resume] using agreement_state_reject_total self.state
  | true =>
    cases hinput : self.state.input <;>
      simp [agreement.SecretConversionPending.resume, hinput]

theorem ephemeral_role_total (self : agreement.EphemeralPending) :
    ∃ result, agreement.EphemeralPending.role self = ok result :=
  ⟨_, rfl⟩

theorem ephemeral_resume_total (self : agreement.EphemeralPending)
    (public_key : core.option.Option (Array Std.U8 32#usize)) :
    ∃ result, agreement.EphemeralPending.resume self public_key = ok result :=
  match public_key with
  | .none => by
    simpa [agreement.EphemeralPending.resume] using agreement_state_reject_total self.state
  | .some _ => ⟨_, rfl⟩

theorem encapsulation_key_total (self : agreement.EncapsulationPending) :
    ∃ result, agreement.EncapsulationPending.public_key self = ok result := by
  cases hinput : self.state.input <;>
    simp [agreement.EncapsulationPending.public_key,
      pqxdh.VerifiedInitKex.impl.beacon_pq_public_key, hinput]

theorem encapsulation_resume_total (self : agreement.EncapsulationPending)
    (reply : core.option.Option ((Array Std.U8 1088#usize) × (Array Std.U8 32#usize))) :
    ∃ result, agreement.EncapsulationPending.resume self reply = ok result :=
  match reply with
  | .none => by
    simpa [agreement.EncapsulationPending.resume] using agreement_state_reject_total self.state
  | .some (_, _) => ⟨_, rfl⟩

theorem decapsulation_ciphertext_total (self : agreement.DecapsulationPending) :
    ∃ result, agreement.DecapsulationPending.ciphertext self = ok result := by
  cases hinput : self.state.input <;>
    simp [agreement.DecapsulationPending.ciphertext, hinput]

theorem decapsulation_resume_total (self : agreement.DecapsulationPending)
    (shared : core.option.Option (Array Std.U8 32#usize)) :
    ∃ result, agreement.DecapsulationPending.resume self shared = ok result :=
  match shared with
  | .none => by
    simpa [agreement.DecapsulationPending.resume] using agreement_state_reject_total self.state
  | .some _ => ⟨_, rfl⟩

theorem dh_request_total (self : agreement.DhPending) :
    ∃ result, agreement.DhPending.request self = ok result := by
  cases hinput : self.state.input <;> cases hposition : self.position <;>
    simp [agreement.DhPending.request, pqxdh.VerifiedInitKex.impl.beacon_prekey_public_key,
      pqxdh.VerifiedInitKex.impl.beacon_one_time_public_key, hinput, hposition]

theorem root_kdf_request_total (self : agreement.RootKdfPending) :
    ∃ result, agreement.RootKdfPending.request self = ok result := by
  cases hcandidate : self.candidate <;>
    simp [agreement.RootKdfPending.request, pqxdh.PendingServerRegistration.impl.root_key_input,
      pqxdh.BeaconRegistrationCandidate.impl.root_key_input, pqxdh.RootKeyInput.as_bytes, hcandidate]

theorem server_registration_id_total (self : agreement.ServerAgreement) :
    ∃ result, agreement.ServerAgreement.registration_id self = ok result :=
  ⟨_, rfl⟩

end BeaconcryptCore.PanicFreedom.KeyAgreement

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.root_key_input_clear_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.root_key_input_clear_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.agreement_state_new_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.agreement_state_new_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.agreement_state_reject_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.agreement_state_reject_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.finish_dh_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.finish_dh_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.dh_resume_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.dh_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total

/-- info: 'BeaconcryptCore.PanicFreedom.KeyAgreement.server_registration_id_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.KeyAgreement.server_registration_id_total
