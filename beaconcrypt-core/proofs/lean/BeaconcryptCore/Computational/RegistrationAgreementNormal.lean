-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
import BeaconcryptCore.PanicFreedom.KeyAgreement
/-! Every actual Core agreement getter and resume is total. Consequently the complete actual free request program returns a RustM.ok phase on every primitive-reply history, including all optional conversion, KEM, DH and root failures. This derived normality avoids introducing a whole-controller success contract in source wrapper composition. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationAgreementNormal
open RegistrationAgreementExecutor
open BeaconcryptCore.PanicFreedom.KeyAgreement

def Normal (work : OracleComp Spec (RustM agreement.AgreementEffect)) : Prop :=
  ∀ outcome, outcome ∈ support work → ∃ phase, outcome = .ok phase

private theorem callback (query : Request) (resume : Spec.Range query → RustM agreement.AgreementEffect)
    (total : ∀ reply, ∃ phase, resume reply = .ok phase) :
    Normal (do let reply ← (Spec.query query : OracleComp Spec _); pure (resume reply)) := by
  intro outcome supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨reply, _, returned⟩ := supported
  obtain ⟨phase, normal⟩ := total reply
  simp only [normal, support_pure, Set.mem_singleton_iff] at returned
  exact ⟨phase, returned⟩

theorem step_normal (phase : agreement.AgreementEffect) : Normal (step phase) := by
  cases phase with
  | ConvertPublic pending =>
      obtain ⟨request, requested⟩ := public_conversion_key_total pending
      simp only [step, requested, continueWith]
      exact callback (.convertPublic request) pending.resume (public_conversion_resume_total pending)
  | ConvertSecret pending =>
      obtain ⟨request, requested⟩ := secret_conversion_role_total pending
      simp only [step, requested, continueWith]
      exact callback (.convertSecret request) pending.resume (secret_conversion_resume_total pending)
  | GenerateEphemeral pending =>
      obtain ⟨request, requested⟩ := ephemeral_role_total pending
      simp only [step, requested, continueWith]
      exact callback (.generate request) pending.resume (ephemeral_resume_total pending)
  | Encapsulate pending =>
      obtain ⟨request, requested⟩ := encapsulation_key_total pending
      simp only [step, requested, continueWith]
      exact callback (.encapsulate request) pending.resume (encapsulation_resume_total pending)
  | Decapsulate pending =>
      obtain ⟨request, requested⟩ := decapsulation_ciphertext_total pending
      simp only [step, requested, continueWith]
      exact callback (.decapsulate request) pending.resume (decapsulation_resume_total pending)
  | Dh pending =>
      obtain ⟨request, requested⟩ := dh_request_total pending
      simp only [step, requested, continueWith]
      exact callback (.dh request) pending.resume (dh_resume_total pending)
  | RootKdf pending =>
      obtain ⟨request, requested⟩ := root_kdf_request_total pending
      simp only [step, requested, continueWith]
      exact callback (.root request) pending.resume (root_kdf_resume_total pending)
  | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
      intro outcome supported
      simp only [step, support_pure, Set.mem_singleton_iff] at supported
      exact ⟨_, supported⟩

theorem drive_normal (fuel : Nat) (phase : agreement.AgreementEffect) : Normal (drive fuel phase) := by
  induction fuel generalizing phase with
  | zero =>
      intro outcome supported
      simp only [drive, support_pure, Set.mem_singleton_iff] at supported
      exact ⟨phase, supported⟩
  | succ fuel ih =>
      intro outcome supported
      simp only [drive, mem_support_bind_iff] at supported
      obtain ⟨result, reached, continued⟩ := supported
      obtain ⟨next, normal⟩ := step_normal phase result reached
      rw [normal] at continued
      exact ih next outcome continued

theorem beacon_normal (authenticated : registration.AuthenticatedResponse) : Normal (beacon authenticated) := by
  obtain ⟨phase, started⟩ := begin_beacon_agreement_total authenticated
  simp only [beacon, started, continueWith]
  exact drive_normal 9 phase

theorem server_normal (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) : Normal (server control status authenticated) := by
  obtain ⟨phase, started⟩ := begin_server_agreement_total control status authenticated
  simp only [server, started, continueWith]
  exact drive_normal 9 phase

end BeaconcryptCore.Computational.RegistrationAgreementNormal

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementNormal.step_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementNormal.step_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementNormal.drive_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementNormal.drive_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementNormal.beacon_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementNormal.beacon_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementNormal.server_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementNormal.server_normal
