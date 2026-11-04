-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationExecution

/-! Every actual Init authentication continuation strictly decreases the number of remaining callbacks: Init hash, ML gate, three attached-signature gates and two fingerprints. Optional failure may terminate earlier. The original callback executor therefore needs seven callbacks and at most one terminal inspection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationAuthenticationTermination
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationInbound

def rank : registration.InitAuthentication → Nat
  | .HashRequested _ => 7
  | .MldsaVerificationRequested _ => 6
  | .Ed25519VerificationRequested pending => match pending.stage with
      | .PqKey => 5
      | .PreKey => 4
      | .OneTimeKey => 3
  | .ServerFingerprintRequested _ => 2
  | .BeaconFingerprintRequested _ => 1
  | .Accepted _ | .Rejected => 0

theorem rank_le (state : registration.InitAuthentication) : rank state ≤ 7 := by
  cases state <;> simp only [rank] <;> try omega
  split <;> omega

/-- Every successful actual source continuation, including rejection, consumes at least one remaining callback. -/
theorem step_progress {before after : registration.InitAuthentication} {event : Event}
    (edge : Step before event after) : rank after < rank before := by
  cases edge with
  | hash pending reply after run =>
      cases reply with
      | none =>
          have same : after = .Rejected := (RustM.ok.inj run).symm
          rw [same]
          norm_num [rank]
      | some digest =>
          obtain ⟨next, resumed, _facts⟩ := init_hash_success pending digest
          have same := RustM.ok.inj (resumed.symm.trans run)
          cases same
          norm_num [rank]
  | mldsa pending verified after run =>
      obtain ⟨actual, resumed, facts⟩ := init_mldsa_exact pending verified
      have same := RustM.ok.inj (resumed.symm.trans run)
      subst actual
      cases after <;> simp only [initMldsaOutcome] at facts
      · simp only [rank, facts.2.2.2.1]
        norm_num [rank]
      · norm_num [rank]
  | ed25519 pending opened after run =>
      obtain ⟨actual, resumed, facts⟩ := init_ed_resume_refines pending opened
      have same := RustM.ok.inj (resumed.symm.trans run)
      subst actual
      cases after <;> simp only [edProgress] at facts
      · obtain ⟨_bytes, _opened, _suffix, _state, _key, transition⟩ := facts
        rcases transition with previous | previous
        · simp only [rank, previous.1, previous.2.1]
          norm_num [rank]
        · simp only [rank, previous.1, previous.2.1]
          norm_num [rank]
      · obtain ⟨_bytes, _opened, _suffix, stage, _state, _validation⟩ := facts
        simp only [rank, stage]
        norm_num [rank]
      · simp only [rank]
        split <;> omega
  | serverFingerprint pending reply after run =>
      cases reply with
      | none =>
          have same : after = .Rejected := (RustM.ok.inj run).symm
          rw [same]
          norm_num [rank]
      | some digest =>
          obtain ⟨next, resumed, _facts⟩ := init_server_fingerprint_exact pending digest
          have same := RustM.ok.inj (resumed.symm.trans run)
          cases same
          norm_num [rank]
  | beaconFingerprint pending reply after run =>
      cases reply with
      | none =>
          have same : after = .Rejected := (RustM.ok.inj run).symm
          rw [same]
          norm_num [rank]
      | some digest =>
          obtain ⟨next, resumed, _facts⟩ := init_beacon_fingerprint_exact pending digest
          have same := RustM.ok.inj (resumed.symm.trans run)
          cases same
          norm_num [rank]

/-- The executable callback step supplies this same source transition rank decrease, rather than a caller's assumed progress condition. -/
theorem executable_step {before after : registration.InitAuthentication} {event : Event}
    (supported : .ok (some (event, after)) ∈ support (RegistrationAuthenticationExecutor.step before)) :
    rank after < rank before :=
  step_progress (RegistrationAuthenticationExecutor.step_sound before event after supported)

end BeaconcryptCore.Computational.RegistrationAuthenticationTermination
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationTermination.rank_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationTermination.rank_le
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationTermination.step_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationTermination.step_progress
/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationTermination.executable_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationTermination.executable_step
