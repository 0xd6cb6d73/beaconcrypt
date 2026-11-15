-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationExecution

/-! Every actual Init authentication continuation strictly decreases the number of remaining callbacks: Init hash and three attached-signature checks. Optional failure may terminate earlier. The original callback executor therefore needs four callbacks and at most one terminal inspection. -/
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
  | .HashRequested _ => 4
  | .Ed25519VerificationRequested pending => match pending.stage with
      | .PqKey => 3
      | .PreKey => 2
      | .OneTimeKey => 1
  | .Accepted _ | .Rejected => 0

theorem rank_le (state : registration.InitAuthentication) : rank state ≤ 4 := by
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
          obtain ⟨actual, resumed, facts⟩ := init_hash_resume_refines pending digest
          have same := RustM.ok.inj (resumed.symm.trans run)
          subst actual
          cases after <;> simp only [initHashOutcome] at facts
          case Ed25519VerificationRequested next =>
            simp only [rank, facts.2.2.2.2.1]
            norm_num
          case Rejected => norm_num [rank]
  | ed25519 pending opened after run =>
      obtain ⟨actual, resumed, facts⟩ := init_ed_resume_refines pending opened
      have same := RustM.ok.inj (resumed.symm.trans run)
      subst actual
      cases after <;> simp only [edProgress] at facts
      case Ed25519VerificationRequested next =>
        obtain ⟨_bytes, _opened, _suffix, _state, _key, transition⟩ := facts
        rcases transition with previous | previous
        · simp only [rank, previous.1, previous.2.1]
          norm_num
        · simp only [rank, previous.1, previous.2.1]
          norm_num
      case Accepted accepted => cases stage : pending.stage <;> norm_num [rank, stage]
      case Rejected => cases stage : pending.stage <;> norm_num [rank, stage]

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
