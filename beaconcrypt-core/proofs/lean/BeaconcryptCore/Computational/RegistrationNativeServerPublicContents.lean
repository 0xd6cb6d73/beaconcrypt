-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerContents

/-! The actual checked source Server candidate retains the consumed token's public operands and current Server identity before publication. This provides public-stage correspondence without assumptions about private root equality or completed peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPublicContents

/-- Successful actual allocation/preparation retains all three public agreement fields and the current source Server identity. -/
theorem prepared (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (candidate : pqxdh.ServerRegistrationCandidate)
    (actual : pqxdh.server_prepare_commit state pending binding availability = .ok (.Ok candidate)) :
    candidate.server_identity_public_key = binding.identity_public_key ∧
      candidate.beacon_identity_public_key = pending.beacon_identity_public_key ∧
      candidate.ephemeral_public_key = pending.ephemeral_public_key ∧ candidate.kem_ciphertext = pending.kem_ciphertext := by
  simp only [pqxdh.server_prepare_commit, array_eq_abs, bind_tc_ok] at actual
  split at actual
  · split at actual
    · obtain ⟨value, generated⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state
      simp only [generated, bind_tc_ok] at actual
      cases value with
      | Err error => simp at actual
      | Ok next =>
        cases availability <;> simp only [bind_tc_ok, Bool.false_eq_true, ite_false, ite_true] at actual
        · obtain ⟨ad, built⟩ := BeaconcryptCore.PanicFreedom.build_associated_data_ok binding.identity_public_key pending.beacon_identity_public_key
          simp only [built, bind_tc_ok] at actual
          cases RustM.ok.inj actual
          exact ⟨rfl, rfl, rfl, rfl⟩
        · simp at actual
    · simp at actual
  · simp at actual

/-- The original consuming initializer uses these exact public token fields and the actual current pin identity. -/
theorem initial (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (capability : agreement.ServerAgreement)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (actual : registration.begin_server_completion control pin availability capability application = .ok (.Ok initial)) :
    initial.candidate.server_identity_public_key = pin.binding.identity_public_key ∧
      initial.candidate.beacon_identity_public_key = capability.pending.beacon_identity_public_key ∧
      initial.candidate.ephemeral_public_key = capability.pending.ephemeral_public_key ∧
      initial.candidate.kem_ciphertext = capability.pending.kem_ciphertext := by
  obtain ⟨empty, emptyRun⟩ : ∃ result, core.slice.Slice.is_empty application = .ok result := ⟨_, rfl⟩
  obtain ⟨matched, matchRun⟩ := BeaconcryptCore.PanicFreedom.SessionBinding.RegistrationBinding_matches_server_total capability.binding pin
  obtain ⟨candidate, prepareRun⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok control capability.pending pin.binding availability
  cases candidate with
  | Err error =>
    cases empty <;> cases matched <;>
      simp [registration.begin_server_completion, session.ServerAuthenticationPin.impl.binding, emptyRun, matchRun, prepareRun] at actual
  | Ok candidate =>
    have fields := prepared control capability.pending pin.binding availability candidate prepareRun
    obtain ⟨pending, pendingRun⟩ := BeaconcryptCore.PanicFreedom.Structural.pqxdh_concrete_start_server_candidate_ratchet_kdf_total candidate capability.root.bytes
    cases empty <;> cases matched
    all_goals simp only [registration.begin_server_completion, session.ServerAuthenticationPin.impl.binding,
      ratchet.RatchetChain.as_bytes, emptyRun, matchRun, prepareRun, pendingRun, bind_tc_ok,
      Bool.false_eq_true, ite_false, ite_true, RustM.ok.injEq, core.result.Result.Ok.injEq, reduceCtorEq] at actual
    cases actual
    exact fields

end BeaconcryptCore.Computational.RegistrationNativeServerPublicContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.prepared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPublicContents.initial
