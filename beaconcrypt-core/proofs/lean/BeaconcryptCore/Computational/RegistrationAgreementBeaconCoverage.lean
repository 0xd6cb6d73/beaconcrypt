-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
import BeaconcryptCore.PanicFreedom.KeyAgreement
import VCVio.OracleComp.QueryTracking.QueryBound
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The genuine Beacon Core entry never invokes generation or encapsulation. Its only private conversion role is LocalIdentity. This is source control coverage on the complete request tree, including every rejected reply, so the NoEntropy SDK path requires no generation/sampling contract. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage
open RegistrationAgreementExecutor

def Allowed : Request → Prop
  | .generate _ | .encapsulate _ => False
  | .convertSecret role => role = .LocalIdentity
  | _ => True

def Bound {A : Type} (work : OracleComp Spec A) : Prop :=
  IsQueryBound work () (fun request _ => Allowed request) (fun _ _ => ())

def Covered (phase : agreement.AgreementEffect) : Prop :=
  rank phase ≤ 8 ∧ ∀ pending, phase ≠ .Encapsulate pending

theorem under_eight (phase : agreement.AgreementEffect) (small : rank phase < 8) : Covered phase := by
  refine ⟨by omega, ?_⟩
  intro pending impossible
  subst phase
  simp only [rank] at small
  omega

theorem progress {initial final : agreement.AgreementEffect} (edge : Step initial final)
    (prior : Covered initial) : Covered final := by
  have initialBound := prior.1
  apply under_eight
  rcases step_progress edge with decreased | ⟨_, zero⟩
  · omega
  · omega

theorem drive_bound (fuel : Nat) (phase : agreement.AgreementEffect) (covered : Covered phase) : Bound (drive fuel phase) := by
  induction fuel generalizing phase with
  | zero => exact isQueryBound_pure _ _ _ _
  | succ fuel ih =>
    cases phase with
    | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
      simp only [drive, step, continueWith, pure_bind]
      exact ih _ covered
    | GenerateEphemeral pending =>
      have bounded := covered.1
      simp only [rank] at bounded
      omega
    | Encapsulate pending => exact False.elim (covered.2 pending rfl)
    | ConvertPublic pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_resume_total pending reply
        rw [resumed]
        exact ih final (progress (.convertPublic pending request reply final requested resumed) covered)
    | ConvertSecret pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · exact RustM.ok.inj ((show pending.secret_role = .ok .LocalIdentity from rfl).symm.trans requested).symm
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_resume_total pending reply
        rw [resumed]
        exact ih final (progress (.convertSecret pending request reply final requested resumed) covered)
    | Decapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_resume_total pending reply
        rw [resumed]
        exact ih final (progress (.decapsulate pending request reply final requested resumed) covered)
    | Dh pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_resume_total pending reply
        rw [resumed]
        exact ih final (progress (.dh pending request reply final requested resumed) covered)
    | RootKdf pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_resume_total pending reply
        rw [resumed]
        exact ih final (progress (.root pending request reply final requested resumed) covered)
theorem beacon_entry (authenticated : registration.AuthenticatedResponse) (initial : agreement.AgreementEffect)
    (actual : agreement.begin_beacon_agreement authenticated = .ok initial) : Covered initial := by
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
      refine ⟨?_, ?_⟩
      · change 8 ≤ 8
        exact Nat.le_refl 8
      · intro pending impossible
        cases impossible
    · simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
        pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
        session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
        array_eq_abs, pqxdh.beacon_abort_init, identityId, identityKey] at actual
      subst initial
      exact ⟨Nat.zero_le 8, fun pending impossible => by cases impossible⟩
  · have unequal : authenticated.control.expected_server_binding.identity_key_id.val ≠
        authenticated.binding.server_pin.binding.identity_key_id.val :=
      fun same => identityId (UScalar.eq_of_val_eq same)
    simp [agreement.begin_beacon_agreement, registration.AuthenticatedResponse.into_parts,
      pqxdh.BeaconInitSent.impl.expected_server_binding, session.CompletedRegistrationBinding.impl.server_pin,
      session.ServerAuthenticationPin.impl.binding, pqxdh.beacon_abort_init, unequal] at actual
    subst initial
    exact ⟨Nat.zero_le 8, fun pending impossible => by cases impossible⟩

theorem beacon_bound (authenticated : registration.AuthenticatedResponse) :
    Bound (RegistrationAgreementExecutor.beacon authenticated) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total authenticated
  unfold RegistrationAgreementExecutor.beacon
  rw [started]
  exact drive_bound 9 phase (beacon_entry authenticated phase started)
end BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.under_eight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.under_eight

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.progress

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.drive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.drive_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.beacon_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.beacon_entry

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementBeaconCoverage.beacon_bound
