-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
/-! Both genuine Core agreement entry paths supply the source rank bound used by the actual public SDK executor. No caller success, credential or completed-agreement law is used. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementSourceEntries
open RegistrationAgreementExecutor
theorem server_rank (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_server_agreement control status authenticated = .ok initial) : rank initial ≤ 9 := by
  cases status with
  | Consumed =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).1] at actual
      cases RustM.ok.inj actual
      exact Nat.zero_le 9
  | Fresh =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).2] at actual
      simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok] at actual
      cases RustM.ok.inj actual
      exact Nat.le_refl 9

theorem beacon_rank (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_beacon_agreement authenticated = .ok initial) : rank initial ≤ 9 := by
  by_cases identityId : authenticated.control.expected_server_binding.identity_key_id =
    authenticated.binding.server_pin.binding.identity_key_id
  · by_cases identityKey : absBytes authenticated.control.expected_server_binding.identity_public_key =
      absBytes authenticated.binding.server_pin.binding.identity_public_key
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, agreement.AgreementState.new, ratchet.RatchetChain.from_bytes,
        pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      change 8 ≤ 9
      decide
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      exact Nat.zero_le 9
  · have unequal : authenticated.control.expected_server_binding.identity_key_id.val ≠
        authenticated.binding.server_pin.binding.identity_key_id.val :=
      fun same => identityId (UScalar.eq_of_val_eq same)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, unequal] at actual
    subst initial
    exact Nat.zero_le 9

theorem lookup_rank (lookup : peer.RegistrationLookup) (consumed : Bool)
    (phase : agreement.AgreementEffect) (actual : lookup.resume consumed = .ok phase) : rank phase ≤ 9 := by
  cases consumed with
  | false => exact server_rank lookup.control .Fresh lookup.authenticated phase actual
  | true =>
    simp only [peer.RegistrationLookup.resume, ↓reduceIte] at actual
    cases RustM.ok.inj actual
    exact Nat.zero_le _

end BeaconcryptCore.Computational.RegistrationAgreementSourceEntries

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceEntries.server_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceEntries.server_rank

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceEntries.beacon_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceEntries.beacon_rank

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementSourceEntries.lookup_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementSourceEntries.lookup_rank
