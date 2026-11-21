-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementMetadata
import BeaconcryptCore.Computational.RegistrationReplaySchedule

/-! The actual Server agreement controller retains the authenticated replay identifier through every native conversion/KEM/DH edge. Successful root completion clears its preimage and retains that same identifier, so persistent membership and insertion address one source-derived value rather than independently supplied IDs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin
open RegistrationAgreementExecutor

private def inputMatches (verified : pqxdh.VerifiedInitKex) : agreement.AgreementInput → Prop
  | .Server _ _ retained _ => retained = verified
  | .Beacon _ _ _ _ => False

private def candidateMatches (verified : pqxdh.VerifiedInitKex) : agreement.AgreementCandidate → Prop
  | .Server pending _ => absBytes pending.registration_id.bytes = (absVerified verified).rid
  | .Beacon _ _ _ => False

private def Retains (verified : pqxdh.VerifiedInitKex) : agreement.AgreementEffect → Prop
  | .Rejected _ => True
  | .ConvertPublic pending => inputMatches verified pending.state.input
  | .ConvertSecret pending => inputMatches verified pending.state.input
  | .GenerateEphemeral pending => inputMatches verified pending.state.input
  | .Encapsulate pending => inputMatches verified pending.state.input
  | .Decapsulate pending => inputMatches verified pending.state.input
  | .Dh pending => inputMatches verified pending.state.input
  | .RootKdf pending => candidateMatches verified pending.candidate
  | .ServerComplete completed =>
      absBytes completed.pending.registration_id.bytes = (absVerified verified).rid ∧
        completed.pending.root_key_input.bytes = Std.Array.repeat 192#usize 0#u8
  | .BeaconComplete _ => False

private theorem accept_id (control next : pqxdh.ServerState) (verified : pqxdh.VerifiedInitKex)
    (status : pqxdh.RegistrationStatus) (binding : pqxdh.ServerBinding) (coins : pqxdh.ServerCoins)
    (secrets : pqxdh.PqxdhSharedSecrets) (pending : pqxdh.PendingServerRegistration)
    (actual : pqxdh.server_accept control verified status binding coins secrets = .ok (.Ok (next, pending))) :
    absBytes pending.registration_id.bytes = (absVerified verified).rid := by
  obtain ⟨rootResult, rootRun⟩ := BeaconcryptCore.PanicFreedom.build_root_key_input_ok secrets
  obtain ⟨identifier, idRun, bytes⟩ := registration_id_abs verified
  cases status <;> cases rootResult <;>
    simp only [pqxdh.server_accept, pqxdh.validate_registration_status, rootRun, idRun,
      bind_tc_ok, Bool.false_eq_true, ite_false, ite_true, RustM.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq, reduceCtorEq] at actual
  cases actual.2
  exact bytes

private theorem reject_retains (verified : pqxdh.VerifiedInitKex) (state : agreement.AgreementState)
    (final : agreement.AgreementEffect) (actual : state.reject = .ok final) : Retains verified final := by
  rw [BeaconcryptCore.Refinement.KeyAgreement.rejection_refines] at actual
  cases RustM.ok.inj actual
  trivial

private theorem finish_retains (verified : pqxdh.VerifiedInitKex) (state : agreement.AgreementState)
    (prior : inputMatches verified state.input) (final : agreement.AgreementEffect)
    (actual : agreement.finish_dh state = .ok final) : Retains verified final := by
  cases inputEq : state.input with
  | Beacon control binding response application => cases (show False by simp only [inputMatches, inputEq] at prior)
  | Server control status retained binding =>
    have same : retained = verified := by simpa only [inputMatches, inputEq] using prior
    subst retained
    obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control verified status
      binding.server_pin.binding
      ⟨state.ephemeral_public_key, state.kem_ciphertext⟩
      ⟨state.dh1.bytes, state.dh2.bytes, state.dh3.bytes, state.dh4.bytes, state.kem.bytes⟩
    simp only [agreement.finish_dh, ratchet.RatchetChain.as_bytes, bind_tc_ok, inputEq,
      session.RegistrationBinding.impl.server_pin, session.ServerAuthenticationPin.impl.binding, acceptedRun] at actual
    cases accepted with
    | Err error => cases RustM.ok.inj actual; trivial
    | Ok pair =>
      obtain ⟨next, pending⟩ := pair
      cases RustM.ok.inj actual
      exact accept_id control next verified status binding.server_pin.binding _ _ pending acceptedRun

private theorem step_retains (verified : pqxdh.VerifiedInitKex) {initial final : agreement.AgreementEffect}
    (edge : Step initial final) (prior : Retains verified initial) : Retains verified final := by
  cases edge with
  | convertPublic pending request reply final requested resumed =>
    cases reply with
    | none => exact reject_retains verified pending.state final resumed
    | some key => simp only [agreement.PublicConversionPending.resume] at resumed; cases RustM.ok.inj resumed; exact prior
  | convertSecret pending request reply final requested resumed =>
    cases reply with
    | false => exact reject_retains verified pending.state final resumed
    | true =>
      cases inputEq : pending.state.input <;>
        simp only [agreement.SecretConversionPending.resume, inputEq, ↓reduceIte] at resumed <;>
        cases RustM.ok.inj resumed <;> exact prior
  | generate pending request reply final requested resumed =>
    cases reply with
    | none => exact reject_retains verified pending.state final resumed
    | some key => simp only [agreement.EphemeralPending.resume] at resumed; cases RustM.ok.inj resumed; exact prior
  | encapsulate pending request reply final requested resumed =>
    cases reply with
    | none => exact reject_retains verified pending.state final resumed
    | some pair =>
      obtain ⟨ciphertext, shared⟩ := pair
      simp only [agreement.EncapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
      cases RustM.ok.inj resumed
      exact prior
  | decapsulate pending request reply final requested resumed =>
    cases reply with
    | none => exact reject_retains verified pending.state final resumed
    | some shared =>
      simp only [agreement.DecapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
      cases RustM.ok.inj resumed
      exact prior
  | dh pending request reply final requested resumed =>
    cases reply with
    | none => exact reject_retains verified pending.state final resumed
    | some shared =>
      cases positionEq : pending.position with
      | First => simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed; cases RustM.ok.inj resumed; exact prior
      | Second => simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed; cases RustM.ok.inj resumed; exact prior
      | Third => simp only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed; cases RustM.ok.inj resumed; exact prior
      | Fourth =>
        exact finish_retains verified { pending.state with dh4 := ⟨shared⟩ } prior final
          (by simpa only [agreement.DhPending.resume, positionEq, ratchet.RatchetChain.from_bytes, bind_tc_ok] using resumed)
  | root pending request reply final requested resumed =>
    cases reply with
    | none =>
      rw [BeaconcryptCore.Refinement.KeyAgreement.root_failure_refines] at resumed
      cases candidateEq : pending.candidate <;> simp only [candidateEq] at resumed <;>
        cases RustM.ok.inj resumed <;> trivial
    | some root =>
      rw [BeaconcryptCore.Refinement.KeyAgreement.root_success_refines] at resumed
      cases candidateEq : pending.candidate with
      | Beacon candidate binding ciphertext => exact False.elim (by simp only [Retains, candidateMatches, candidateEq] at prior)
      | Server candidate binding =>
        simp only [candidateEq] at resumed
        cases RustM.ok.inj resumed
        exact ⟨by simpa only [Retains, candidateMatches, candidateEq] using prior, rfl⟩
  | rejected => exact prior
  | server => exact prior
  | beacon => exact prior

private theorem run_retains (verified : pqxdh.VerifiedInitKex) {initial final : agreement.AgreementEffect}
    (ran : Run initial final) (prior : Retains verified initial) : Retains verified final := by
  induction ran with
  | refl => exact prior
  | cons first rest ih => exact ih (step_retains verified first prior)

/-- The complete actual Server controller returns the authenticated lookup identifier and clears the source root preimage before replay insertion. -/
theorem server_origin (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (supported : .ok (.ServerComplete completed) ∈ support (server control status authenticated)) :
    absBytes completed.pending.registration_id.bytes = RegistrationReplaySchedule.identifier authenticated ∧
      completed.pending.root_key_input.bytes = Std.Array.repeat 192#usize 0#u8 := by
  obtain ⟨initial, started, ran⟩ := server_sound control status authenticated _ supported
  have entry : Retains authenticated.registration initial := by
    cases status with
    | Consumed =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).1] at started
      cases RustM.ok.inj started
      trivial
    | Fresh =>
      rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines control authenticated).2] at started
      simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok] at started
      cases RustM.ok.inj started
      rfl
  exact run_retains authenticated.registration ran entry

/-- Every concrete interpreter of the actual callbacks retains the same canonical replay identifier, including the actual shared World interpreter. -/
theorem interpreted_server_origin {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp)) (before after : State)
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (completed : agreement.ServerAgreement)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      ((simulateQ implementation (server control status authenticated)).run before)) :
    absBytes completed.pending.registration_id.bytes = RegistrationReplaySchedule.identifier authenticated ∧
      completed.pending.root_key_input.bytes = Std.Array.repeat 192#usize 0#u8 := by
  apply server_origin control status authenticated completed
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin.server_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin.server_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin.interpreted_server_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin.interpreted_server_origin
