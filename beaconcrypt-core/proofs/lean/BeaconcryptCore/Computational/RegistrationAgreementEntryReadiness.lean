-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
/-! Actual Core role entries derive the empty private conversion-readiness invariant, and the complete original nine-step role programs erase its ghost guard for every native primitive backend. This supplies schedule coverage without an agreement-success premise. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness
open RegistrationAgreementExecutor RegistrationAgreementIdentityGuard
theorem server_ready (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_server_agreement control status authenticated = .ok initial) : Ready initial false := by
  cases status with
  | Consumed =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).1] at actual
      cases RustM.ok.inj actual
      exact False.elim
  | Fresh =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).2] at actual
      simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok] at actual
      cases RustM.ok.inj actual
      exact False.elim

theorem beacon_ready (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_beacon_agreement authenticated = .ok initial) : Ready initial false := by
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
      exact False.elim
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      exact False.elim
  · have unequal : authenticated.control.expected_server_binding.identity_key_id.val ≠
        authenticated.binding.server_pin.binding.identity_key_id.val :=
      fun same => identityId (UScalar.eq_of_val_eq same)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, unequal] at actual
    subst initial
    exact False.elim

theorem lookup_ready (lookup : peer.RegistrationLookup) (consumed : Bool)
    (phase : agreement.AgreementEffect) (actual : lookup.resume consumed = .ok phase) : Ready phase false := by
  cases consumed with
  | false => exact server_ready lookup.control .Fresh lookup.authenticated phase actual
  | true =>
    simp only [peer.RegistrationLookup.resume, ↓reduceIte] at actual
    cases RustM.ok.inj actual
    exact False.elim

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem server (base : QueryImpl Spec m) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) :
    Prod.fst <$> ((simulateQ (implementation base)
      (RegistrationAgreementExecutor.server control status authenticated)).run false) =
      simulateQ base (RegistrationAgreementExecutor.server control status authenticated) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total control status authenticated
  unfold RegistrationAgreementExecutor.server
  rw [started]
  exact drive_erasure base 9 phase false (server_ready control status authenticated phase started)

theorem beacon (base : QueryImpl Spec m) (authenticated : registration.AuthenticatedResponse) :
    Prod.fst <$> ((simulateQ (implementation base)
      (RegistrationAgreementExecutor.beacon authenticated)).run false) =
      simulateQ base (RegistrationAgreementExecutor.beacon authenticated) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total authenticated
  unfold RegistrationAgreementExecutor.beacon
  rw [started]
  exact drive_erasure base 9 phase false (beacon_ready authenticated phase started)

theorem lookup (base : QueryImpl Spec m) (pending : peer.RegistrationLookup) (consumed : Bool) :
    Prod.fst <$> ((simulateQ (implementation base)
      (continueWith (pending.resume consumed) (drive 9))).run false) =
      simulateQ base (continueWith (pending.resume consumed) (drive 9)) := by
  have normal : ∃ phase, pending.resume consumed = .ok phase := by
    cases consumed with
    | false => exact BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total pending.control .Fresh pending.authenticated
    | true => exact ⟨.Rejected .None, rfl⟩
  obtain ⟨phase, started⟩ := normal
  rw [started]
  exact drive_erasure base 9 phase false (lookup_ready pending consumed phase started)
end BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.server_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.server_ready

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.beacon_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.beacon_ready

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.lookup_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.lookup_ready

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.server

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness.lookup
