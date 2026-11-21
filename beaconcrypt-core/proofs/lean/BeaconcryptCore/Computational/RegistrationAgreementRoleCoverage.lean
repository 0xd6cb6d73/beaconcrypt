-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
import BeaconcryptCore.PanicFreedom.KeyAgreement
import VCVio.OracleComp.QueryTracking.QueryBound
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Every actual Core agreement secret-conversion getter names LocalIdentity, and every actual ephemeral-generation getter names ServerEphemeral. These bounds hold for every phase, every finite driver and every primitive reply, including rejection branches. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage
open RegistrationAgreementExecutor

def Allowed : Request → Prop
  | .convertSecret role => role = .LocalIdentity
  | .generate role => role = .ServerEphemeral
  | _ => True

def Bound {A : Type} (work : OracleComp Spec A) : Prop :=
  IsQueryBound work () (fun request _ => Allowed request) (fun _ _ => ())

theorem drive_bound (fuel : Nat) (phase : agreement.AgreementEffect) : Bound (drive fuel phase) := by
  induction fuel generalizing phase with
  | zero => exact isQueryBound_pure _ _ _ _
  | succ fuel ih =>
    cases phase with
    | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
      simp only [drive, step, continueWith, pure_bind]
      exact ih _
    | GenerateEphemeral pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · exact RustM.ok.inj ((show pending.role = .ok .ServerEphemeral from rfl).symm.trans requested).symm
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_resume_total pending reply
        rw [resumed]
        exact ih final
    | Encapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨True.intro, ?_⟩
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_resume_total pending reply
      rw [resumed]
      exact ih final
    | ConvertPublic pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_resume_total pending reply
        rw [resumed]
        exact ih final
    | ConvertSecret pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · exact RustM.ok.inj ((show pending.secret_role = .ok .LocalIdentity from rfl).symm.trans requested).symm
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_resume_total pending reply
        rw [resumed]
        exact ih final
    | Decapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_resume_total pending reply
        rw [resumed]
        exact ih final
    | Dh pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_resume_total pending reply
        rw [resumed]
        exact ih final
    | RootKdf pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total pending
      simp only [drive, step, requested, continueWith, bind_assoc, pure_bind]
      rw [Bound, isQueryBound_query_bind_iff]
      refine ⟨?_, ?_⟩
      · trivial
      · intro reply
        obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_resume_total pending reply
        rw [resumed]
        exact ih final

theorem server_bound (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) : Bound (RegistrationAgreementExecutor.server control status authenticated) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total control status authenticated
  unfold RegistrationAgreementExecutor.server
  rw [started]
  exact drive_bound 9 phase

theorem beacon_bound (authenticated : registration.AuthenticatedResponse) : Bound (RegistrationAgreementExecutor.beacon authenticated) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total authenticated
  unfold RegistrationAgreementExecutor.beacon
  rw [started]
  exact drive_bound 9 phase

theorem lookup_bound (pending : peer.RegistrationLookup) (consumed : Bool) :
    Bound (continueWith (pending.resume consumed) (drive 9)) := by
  have normal : ∃ phase, pending.resume consumed = .ok phase := by
    cases consumed with
    | false => exact BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total pending.control .Fresh pending.authenticated
    | true => exact ⟨.Rejected .None, rfl⟩
  obtain ⟨phase, started⟩ := normal
  rw [started]
  exact drive_bound 9 phase
end BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.drive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.drive_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.server_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.beacon_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.lookup_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementRoleCoverage.lookup_bound
