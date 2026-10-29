-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementShared

/-! Actual agreement continuations retain the authenticated registration binding through every successful primitive response, native root admission and preimage erasure. Rejection carries no installable binding. These field facts require no primitive correctness or secret-provenance premise. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationAgreementExecutor

def inputBinding : agreement.AgreementInput → session.RegistrationBinding
  | .Server _ _ _ binding => binding
  | .Beacon _ binding _ _ => binding

def candidateBinding : agreement.AgreementCandidate → session.RegistrationBinding
  | .Server _ binding => binding
  | .Beacon _ binding _ => binding

def Retains (binding : session.RegistrationBinding) : agreement.AgreementEffect → Prop
  | .Rejected _ => True
  | .ConvertPublic pending => inputBinding pending.state.input = binding
  | .ConvertSecret pending => inputBinding pending.state.input = binding
  | .GenerateEphemeral pending => inputBinding pending.state.input = binding
  | .Encapsulate pending => inputBinding pending.state.input = binding
  | .Decapsulate pending => inputBinding pending.state.input = binding
  | .Dh pending => inputBinding pending.state.input = binding
  | .RootKdf pending => candidateBinding pending.candidate = binding
  | .ServerComplete completed => completed.binding = binding
  | .BeaconComplete completed => completed.binding = binding

theorem reject_retains (state : agreement.AgreementState) (binding : session.RegistrationBinding)
    (final : agreement.AgreementEffect) (actual : state.reject = .ok final) : Retains binding final := by
  rw [BeaconcryptCore.Refinement.KeyAgreement.rejection_refines] at actual
  cases RustM.ok.inj actual
  trivial

theorem finish_dh_retains (state : agreement.AgreementState) (final : agreement.AgreementEffect)
    (actual : agreement.finish_dh state = .ok final) : Retains (inputBinding state.input) final := by
  cases inputEq : state.input with
  | Server control status verified binding =>
      obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control verified status
        binding.server_pin.binding
        { ephemeral_public_key := state.ephemeral_public_key, kem_ciphertext := state.kem_ciphertext }
        { dh1 := state.dh1.bytes, dh2 := state.dh2.bytes, dh3 := state.dh3.bytes,
          dh4 := state.dh4.bytes, kem_shared_secret := state.kem.bytes }
      simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq,
        session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding, acceptedRun] at actual
      cases accepted with
      | Ok pair =>
          obtain ⟨control, pending⟩ := pair
          cases RustM.ok.inj actual
          simp only [Retains, candidateBinding, inputBinding]
      | Err error =>
          cases RustM.ok.inj actual
          trivial
  | Beacon control binding response application =>
      obtain ⟨prepared, preparedRun⟩ := BeaconcryptCore.PanicFreedom.beacon_prepare_finish_ok control
        { response_server_identity := response.identity_key, assigned_key_id := response.key_id,
          shared_secrets :=
            { dh1 := state.dh1.bytes, dh2 := state.dh2.bytes, dh3 := state.dh3.bytes,
              dh4 := state.dh4.bytes, kem_shared_secret := state.kem.bytes } }
      simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq, preparedRun] at actual
      cases prepared with
      | Ok candidate =>
          cases RustM.ok.inj actual
          simp only [Retains, candidateBinding, inputBinding]
      | Err error =>
          simp only [bind_tc_ok, pqxdh.beacon_abort_init] at actual
          cases RustM.ok.inj actual
          trivial

theorem step_retains (binding : session.RegistrationBinding) {initial final : agreement.AgreementEffect}
    (edge : Step initial final) (prior : Retains binding initial) : Retains binding final := by
  cases edge with
  | convertPublic pending request reply final requested resumed =>
      cases reply with
      | none => exact reject_retains pending.state binding final resumed
      | some key =>
          simp only [agreement.PublicConversionPending.resume] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | convertSecret pending request reply final requested resumed =>
      cases reply with
      | false => exact reject_retains pending.state binding final resumed
      | true =>
          cases inputEq : pending.state.input <;>
            simp only [agreement.SecretConversionPending.resume, inputEq,
              ↓reduceIte] at resumed <;>
            cases RustM.ok.inj resumed <;> exact prior
  | generate pending request reply final requested resumed =>
      cases reply with
      | none => exact reject_retains pending.state binding final resumed
      | some key =>
          simp only [agreement.EphemeralPending.resume] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | encapsulate pending request reply final requested resumed =>
      cases reply with
      | none => exact reject_retains pending.state binding final resumed
      | some pair =>
          obtain ⟨ciphertext, shared⟩ := pair
          simp only [agreement.EncapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | decapsulate pending request reply final requested resumed =>
      cases reply with
      | none => exact reject_retains pending.state binding final resumed
      | some shared =>
          simp only [agreement.DecapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
          cases RustM.ok.inj resumed
          exact prior
  | dh pending request reply final requested resumed =>
      cases reply with
      | none => exact reject_retains pending.state binding final resumed
      | some shared =>
          cases positionEq : pending.position with
          | First =>
              simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              exact prior
          | Second =>
              simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              exact prior
          | Third =>
              simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              exact prior
          | Fourth =>
              have retained := finish_dh_retains { pending.state with dh4 := ⟨shared⟩ } final
                (by simpa only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes,
                  bind_tc_ok] using resumed)
              change inputBinding pending.state.input = binding at prior
              simpa only [prior] using retained
  | root pending request reply final requested resumed =>
      cases reply with
      | none =>
          rw [BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines] at resumed
          cases candidateEq : pending.candidate <;> simp only [candidateEq] at resumed <;>
            cases RustM.ok.inj resumed <;> trivial
      | some root =>
          rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines] at resumed
          cases candidateEq : pending.candidate <;> simp only [candidateEq] at resumed <;>
            cases RustM.ok.inj resumed <;> simpa only [Retains, candidateBinding, candidateEq] using prior
  | rejected => exact prior
  | server => exact prior
  | beacon => exact prior

theorem run_retains (binding : session.RegistrationBinding) {initial final : agreement.AgreementEffect}
    (run : Run initial final) (prior : Retains binding initial) : Retains binding final := by
  induction run with
  | refl => exact prior
  | cons first rest ih => exact ih (step_retains binding first prior)

theorem server_entry_retains (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_server_agreement control status authenticated = .ok initial) :
    Retains authenticated.binding initial := by
  cases status with
  | Consumed =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).1] at actual
      cases RustM.ok.inj actual
      trivial
  | Fresh =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).2] at actual
      simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok] at actual
      cases RustM.ok.inj actual
      rfl

theorem beacon_entry_retains (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_beacon_agreement authenticated = .ok initial) :
    Retains authenticated.pending.binding initial := by
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
      rfl
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      trivial
  · have unequal : authenticated.pending.control.expected_server_binding.identity_key_id.val ≠
        authenticated.pending.binding.server_pin.binding.identity_key_id.val :=
      fun same => identityId (UScalar.eq_of_val_eq same)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.RegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, unequal] at actual
    subst initial
    trivial

theorem server_binding (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (supported : .ok (.ServerComplete completed) ∈ support (server control status authenticated)) :
    completed.binding = authenticated.binding := by
  obtain ⟨initial, started, ran⟩ := server_sound control status authenticated _ supported
  exact run_retains authenticated.binding ran (server_entry_retains control status authenticated initial started)

theorem beacon_binding (authenticated : registration.AuthenticatedResponse) (completed : agreement.BeaconAgreement)
    (supported : .ok (.BeaconComplete completed) ∈ support (beacon authenticated)) :
    completed.binding = authenticated.pending.binding := by
  obtain ⟨initial, started, ran⟩ := beacon_sound authenticated _ supported
  exact run_retains authenticated.pending.binding ran (beacon_entry_retains authenticated initial started)

theorem interpreted_server_binding {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp)) (before after : State)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      ((simulateQ implementation (server control status authenticated)).run before)) :
    completed.binding = authenticated.binding := by
  apply server_binding control status authenticated completed
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

theorem interpreted_beacon_binding {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp)) (before after : State)
    (authenticated : registration.AuthenticatedResponse) (completed : agreement.BeaconAgreement)
    (supported : (.ok (.BeaconComplete completed), after) ∈ support
      ((simulateQ implementation (beacon authenticated)).run before)) :
    completed.binding = authenticated.pending.binding := by
  apply beacon_binding authenticated completed
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationAgreementExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.reject_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.reject_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.finish_dh_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.finish_dh_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.step_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.step_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.run_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.run_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_entry_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_entry_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_entry_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_entry_retains
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_binding
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_binding
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_server_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_server_binding
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_beacon_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.interpreted_beacon_binding
