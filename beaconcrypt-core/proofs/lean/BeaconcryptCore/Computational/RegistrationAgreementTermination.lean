-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementMetadata

/-! The bounded native agreement controller has enough steps for every actual entry. Nonterminal source continuations strictly lower a finite phase rank, including rejected primitive replies and final native DH admission. A terminal effect remains terminal. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationAgreementExecutor

private def beaconExtra : agreement.AgreementInput → Nat
  | .Server _ _ _ _ => 0
  | .Beacon _ _ _ _ => 1

def rank : agreement.AgreementEffect → Nat
  | .Rejected _ => 0
  | .ServerComplete _ => 0
  | .BeaconComplete _ => 0
  | .GenerateEphemeral pending => 9 + beaconExtra pending.state.input
  | .Encapsulate pending => 8 + beaconExtra pending.state.input
  | .ConvertPublic pending => 7 + beaconExtra pending.state.input
  | .ConvertSecret pending => 6 + beaconExtra pending.state.input
  | .Decapsulate _ => 6
  | .Dh pending => match pending.position with
      | .First => 5
      | .Second => 4
      | .Third => 3
      | .Fourth => 2
  | .RootKdf _ => 1

private theorem reject_rank (state : agreement.AgreementState) (final : agreement.AgreementEffect)
    (actual : state.reject = .ok final) : rank final = 0 := by
  rw [BeaconcryptCore.Refinement.KeyAgreement.rejection_refines] at actual
  cases RustM.ok.inj actual
  rfl

private theorem finish_dh_rank (state : agreement.AgreementState) (final : agreement.AgreementEffect)
    (actual : agreement.finish_dh state = .ok final) : rank final ≤ 1 := by
  cases inputEq : state.input with
  | Server control status verified binding =>
      obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control verified status
        binding.server_pin.binding
        { ephemeral_public_key := state.ephemeral_public_key, kem_ciphertext := state.kem_ciphertext }
        { dh1 := state.dh1.bytes, dh2 := state.dh2.bytes, dh3 := state.dh3.bytes,
          dh4 := state.dh4.bytes, kem_shared_secret := state.kem.bytes }
      cases accepted with
      | Ok pair =>
          obtain ⟨control, pending⟩ := pair
          simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq,
            session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
            acceptedRun] at actual
          cases RustM.ok.inj actual
          exact Nat.le_refl 1
      | Err error =>
          simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq,
            session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding,
            acceptedRun] at actual
          cases RustM.ok.inj actual
          exact Nat.zero_le 1
  | Beacon control binding response application =>
      obtain ⟨prepared, preparedRun⟩ := BeaconcryptCore.PanicFreedom.beacon_prepare_finish_ok control
        { response_server_identity := response.identity_key, assigned_key_id := response.key_id,
          shared_secrets :=
            { dh1 := state.dh1.bytes, dh2 := state.dh2.bytes, dh3 := state.dh3.bytes,
              dh4 := state.dh4.bytes, kem_shared_secret := state.kem.bytes } }
      cases prepared with
      | Ok candidate =>
          simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq, preparedRun] at actual
          cases RustM.ok.inj actual
          exact Nat.le_refl 1
      | Err error =>
          simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq, preparedRun,
            pqxdh.beacon_abort_init] at actual
          cases RustM.ok.inj actual
          exact Nat.zero_le 1

theorem step_progress {initial final : agreement.AgreementEffect} (edge : Step initial final) :
    rank final < rank initial ∨ (rank initial = 0 ∧ rank final = 0) := by
  cases edge with
  | convertPublic pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | none => rw [reject_rank pending.state final resumed]; simp only [rank]; omega
      | some key =>
          simp only [agreement.PublicConversionPending.resume] at resumed
          cases RustM.ok.inj resumed
          simp only [rank]
          omega
  | convertSecret pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | false => rw [reject_rank pending.state final resumed]; simp only [rank]; omega
      | true =>
          cases inputEq : pending.state.input <;>
            simp only [agreement.SecretConversionPending.resume, inputEq, ↓reduceIte] at resumed <;>
            cases RustM.ok.inj resumed <;> simp only [rank, beaconExtra, inputEq] <;> omega
  | generate pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | none => rw [reject_rank pending.state final resumed]; simp only [rank]; omega
      | some key =>
          simp only [agreement.EphemeralPending.resume] at resumed
          cases RustM.ok.inj resumed
          simp only [rank]
          omega
  | encapsulate pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | none => rw [reject_rank pending.state final resumed]; simp only [rank]; omega
      | some pair =>
          obtain ⟨ciphertext, shared⟩ := pair
          simp only [agreement.EncapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          cases RustM.ok.inj resumed
          simp only [rank]
          omega
  | decapsulate pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | none => rw [reject_rank pending.state final resumed]; change 0 < 6; decide
      | some shared =>
          simp only [agreement.DecapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          cases RustM.ok.inj resumed
          change 5 < 6
          decide
  | dh pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | none =>
          rw [reject_rank pending.state final resumed]
          cases positionEq : pending.position <;> simp only [rank, positionEq] <;> decide
      | some shared =>
          cases positionEq : pending.position with
          | First =>
              simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              simp only [rank, positionEq]
              decide
          | Second =>
              simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              simp only [rank, positionEq]
              decide
          | Third =>
              simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              simp only [rank, positionEq]
              decide
          | Fourth =>
              have bounded := finish_dh_rank { pending.state with dh4 := ⟨shared⟩ } final
                (by simpa only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes,
                  bind_tc_ok] using resumed)
              have initialRank : rank (.Dh pending) = 2 := by simp only [rank, positionEq]
              rw [initialRank]
              omega
  | root pending request reply final requested resumed =>
      apply Or.inl
      cases reply with
      | none =>
          rw [BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines] at resumed
          cases candidateEq : pending.candidate <;> simp only [candidateEq] at resumed <;>
            cases RustM.ok.inj resumed <;> simp only [rank] <;> decide
      | some root =>
          rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines] at resumed
          cases candidateEq : pending.candidate <;> simp only [candidateEq] at resumed <;>
            cases RustM.ok.inj resumed <;> simp only [rank] <;> decide
  | rejected => exact Or.inr ⟨rfl, rfl⟩
  | server => exact Or.inr ⟨rfl, rfl⟩
  | beacon => exact Or.inr ⟨rfl, rfl⟩

theorem drive_finished (fuel : Nat) (initial final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (drive fuel initial)) (enough : rank initial ≤ fuel) : rank final = 0 := by
  induction fuel generalizing initial final with
  | zero =>
      simp only [drive, support_pure, Set.mem_singleton_iff, RustM.ok.injEq] at supported
      subst final
      omega
  | succ fuel ih =>
      simp only [drive, mem_support_bind_iff] at supported
      obtain ⟨result, first, rest⟩ := supported
      cases result with
      | fail error => simp [continueWith] at rest
      | div => simp [continueWith] at rest
      | ok middle =>
          apply ih middle final rest
          rcases step_progress (step_sound initial middle first) with decreased | terminal
          · omega
          · omega

private theorem server_entry_rank (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
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

private theorem beacon_entry_rank (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_beacon_agreement authenticated = .ok initial) : rank initial ≤ 9 := by
  by_cases identityId : authenticated.pending.control.expected_server_binding.identity_key_id =
    authenticated.pending.binding.server_pin.binding.identity_key_id
  · by_cases identityKey : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      absBytes authenticated.pending.binding.server_pin.binding.identity_public_key
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, agreement.AgreementState.new, ratchet.RatchetChain.from_bytes,
        pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      change 8 ≤ 9
      decide
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      exact Nat.zero_le 9
  · have unequal : authenticated.pending.control.expected_server_binding.identity_key_id.val ≠
        authenticated.pending.binding.server_pin.binding.identity_key_id.val :=
      fun same => identityId (UScalar.eq_of_val_eq same)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, unequal] at actual
    subst initial
    exact Nat.zero_le 9

inductive Terminal : agreement.AgreementEffect → Prop where
  | rejected (aborted) : Terminal (.Rejected aborted)
  | server (completed) : Terminal (.ServerComplete completed)
  | beacon (completed) : Terminal (.BeaconComplete completed)

private theorem rank_terminal (phase : agreement.AgreementEffect) (zero : rank phase = 0) : Terminal phase := by
  cases phase with
  | Rejected aborted => exact .rejected aborted
  | ServerComplete completed => exact .server completed
  | BeaconComplete completed => exact .beacon completed
  | GenerateEphemeral pending => simp [rank] at zero
  | Encapsulate pending => simp [rank] at zero
  | ConvertPublic pending => simp [rank] at zero
  | ConvertSecret pending => simp [rank] at zero
  | Decapsulate pending => simp [rank] at zero
  | RootKdf pending => simp [rank] at zero
  | Dh pending => cases positionEq : pending.position <;> simp [rank, positionEq] at zero

private theorem entry_support {Input : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM agreement.AgreementEffect)) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (continueWith result next)) :
    ∃ input, result = .ok input ∧ .ok final ∈ support (next input) := by
  cases result <;> simp_all [continueWith]

attribute [local irreducible] drive agreement.begin_server_agreement agreement.begin_beacon_agreement

theorem server_terminal (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (server control status authenticated)) : Terminal final := by
  obtain ⟨initial, started, ran⟩ := entry_support _ _ final supported
  exact rank_terminal final (drive_finished 9 initial final ran
    (server_entry_rank control status authenticated initial started))

theorem beacon_terminal (authenticated : registration.AuthenticatedResponse) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (beacon authenticated)) : Terminal final := by
  obtain ⟨initial, started, ran⟩ := entry_support _ _ final supported
  exact rank_terminal final (drive_finished 9 initial final ran (beacon_entry_rank authenticated initial started))

theorem interpreted_server_terminal {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp)) (before after : State)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (final : agreement.AgreementEffect)
    (supported : (.ok final, after) ∈ support
      ((simulateQ implementation (server control status authenticated)).run before)) : Terminal final := by
  apply server_terminal control status authenticated final
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

theorem interpreted_beacon_terminal {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp)) (before after : State)
    (authenticated : registration.AuthenticatedResponse) (final : agreement.AgreementEffect)
    (supported : (.ok final, after) ∈ support
      ((simulateQ implementation (beacon authenticated)).run before)) : Terminal final := by
  apply beacon_terminal authenticated final
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationAgreementExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.step_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.step_progress
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.drive_finished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.drive_finished
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_terminal
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_terminal
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_server_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_server_terminal
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_beacon_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_beacon_terminal
