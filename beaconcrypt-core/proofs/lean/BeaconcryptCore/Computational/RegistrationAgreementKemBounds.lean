-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
import BeaconcryptCore.PanicFreedom.KeyAgreement
import VCVio.OracleComp.QueryTracking.QueryBound
/-! The actual agreement request tree makes at most one encapsulation and at most one decapsulation, for every initial phase and every primitive reply. A source-stage potential pays each counted call before resuming; optional rejection, Rust failure/divergence and terminal stuttering retain their true prefixes. These are algorithm-call caps, separate from primitive execution costs and recipient-correctness probabilities. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationAgreementKemBounds
open RegistrationAgreementExecutor
inductive Kind where
  | encapsulate
  | decapsulate

def counted : Kind → Request → Prop
  | .encapsulate, .encapsulate _ => True
  | .decapsulate, .decapsulate _ => True
  | _, _ => False

instance (kind : Kind) (query : Request) : Decidable (counted kind query) := by
  cases kind <;> cases query <;> simp only [counted] <;> infer_instance

def budget : Kind → agreement.AgreementEffect → Nat
  | .encapsulate, .GenerateEphemeral _ | .encapsulate, .Encapsulate _ => 1
  | .encapsulate, _ => 0
  | .decapsulate, phase => if 6 ≤ rank phase then 1 else 0

def spent : Kind → agreement.AgreementEffect → Nat
  | .encapsulate, .Encapsulate _ | .decapsulate, .Decapsulate _ => 1
  | _, _ => 0

theorem budget_le_one (kind : Kind) (phase : agreement.AgreementEffect) : budget kind phase ≤ 1 := by
  cases kind with
  | encapsulate => cases phase <;> simp only [budget] <;> omega
  | decapsulate => simp only [budget]; split <;> omega

private theorem under_eight (phase : agreement.AgreementEffect) (small : rank phase < 8) :
    budget .encapsulate phase = 0 := by
  cases phase with
  | GenerateEphemeral pending | Encapsulate pending => simp only [rank] at small; omega
  | _ => rfl

theorem progress (kind : Kind) {initial final : agreement.AgreementEffect} (edge : Step initial final) :
    budget kind final ≤ budget kind initial - spent kind initial := by
  cases kind with
  | decapsulate =>
      have monotone : rank final ≤ rank initial := by
        rcases step_progress edge with smaller | ⟨beforeZero, afterZero⟩ <;> omega
      have bounded : (if 6 ≤ rank final then 1 else 0) ≤ (if 6 ≤ rank initial then 1 else 0) := by
        split <;> split <;> omega
      cases initial with
      | Decapsulate pending =>
          have smaller := (step_progress edge).resolve_right (by change ¬(6 = 0 ∧ rank final = 0); omega)
          change rank final < 6 at smaller
          change (if 6 ≤ rank final then 1 else 0) ≤ 0
          rw [ite_eq_right (by omega)]
      | _ => simpa only [budget, spent, Nat.sub_zero] using bounded
  | encapsulate =>
      cases edge with
      | generate pending request reply final requested resumed =>
          simpa only [budget, spent, Nat.sub_zero] using budget_le_one .encapsulate final
      | encapsulate pending request reply final requested resumed =>
          cases reply with
          | none =>
              change pending.state.reject = .ok final at resumed
              rw [BeaconcryptCore.Refinement.KeyAgreement.rejection_refines] at resumed
              cases RustM.ok.inj resumed
              simp only [budget, spent, Nat.sub_self]
              omega
          | some pair =>
              rcases pair with ⟨ciphertext, shared⟩
              simp only [agreement.EncapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
              cases RustM.ok.inj resumed
              simp only [budget, spent, Nat.sub_self]
              omega
      | rejected aborted | server completed | beacon completed => simp only [budget, spent]; omega
      | convertPublic pending request reply final requested resumed =>
          have before : rank (.ConvertPublic pending) ≤ 8 := by
            cases input : pending.state.input with
            | Server control status verified binding => simp only [rank, input]; change 7 + 0 ≤ 8; omega
            | Beacon control binding response application => simp only [rank, input]; change 7 + 1 ≤ 8; omega
          have small : rank final < 8 := by
            rcases step_progress (.convertPublic pending request reply final requested resumed) with smaller | ⟨_, zero⟩ <;> omega
          rw [under_eight final small]
          omega
      | convertSecret pending request reply final requested resumed =>
          have before : rank (.ConvertSecret pending) ≤ 8 := by
            cases input : pending.state.input with
            | Server control status verified binding => simp only [rank, input]; change 6 + 0 ≤ 8; omega
            | Beacon control binding response application => simp only [rank, input]; change 6 + 1 ≤ 8; omega
          have small : rank final < 8 := by
            rcases step_progress (.convertSecret pending request reply final requested resumed) with smaller | ⟨_, zero⟩ <;> omega
          rw [under_eight final small]
          omega
      | decapsulate pending request reply final requested resumed =>
          have before : rank (.Decapsulate pending) ≤ 8 := by change 6 ≤ 8; decide
          have small : rank final < 8 := by
            rcases step_progress (.decapsulate pending request reply final requested resumed) with smaller | ⟨_, zero⟩ <;> omega
          rw [under_eight final small]
          omega
      | dh pending request reply final requested resumed =>
          have before : rank (.Dh pending) ≤ 8 := by cases position : pending.position <;> simp [rank, position]
          have small : rank final < 8 := by
            rcases step_progress (.dh pending request reply final requested resumed) with smaller | ⟨_, zero⟩ <;> omega
          rw [under_eight final small]
          omega
      | root pending request reply final requested resumed =>
          have before : rank (.RootKdf pending) ≤ 8 := by change 1 ≤ 8; decide
          have small : rank final < 8 := by
            rcases step_progress (.root pending request reply final requested resumed) with smaller | ⟨_, zero⟩ <;> omega
          rw [under_eight final small]
          omega

theorem spent_le_one (kind : Kind) (phase : agreement.AgreementEffect) : spent kind phase ≤ 1 := by
  cases kind <;> cases phase
  all_goals first | exact Nat.zero_le _ | exact Nat.le_refl 1

theorem spent_le_budget (kind : Kind) (phase : agreement.AgreementEffect) : spent kind phase ≤ budget kind phase := by
  cases kind <;> cases phase
  all_goals first | exact Nat.zero_le _ | (change 1 ≤ 1; exact Nat.le_refl 1)

private theorem callback_bound (kind : Kind) (fuel : Nat) (phase : agreement.AgreementEffect)
    (query : Request) (resume : Spec.Range query → RustM agreement.AgreementEffect)
    (edge : ∀ reply next, resume reply = .ok next → Step phase next)
    (charge : counted kind query ↔ spent kind phase = 1)
    (continued : ∀ next, (drive fuel next).IsQueryBoundP (counted kind) (budget kind next)) :
    IsQueryBoundP (do
      let reply ← (Spec.query query : OracleComp Spec _)
      continueWith (resume reply) (drive fuel)) (counted kind) (budget kind phase) := by
  classical
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨?_, fun reply => ?_⟩
  · by_cases called : counted kind query
    · right
      have paid := spent_le_budget kind phase
      rw [charge.mp called] at paid
      omega
    · exact .inl called
  · cases resumed : resume reply with
    | fail error | div => trivial
    | ok next =>
        apply (continued next).mono
        have decreases := progress kind (edge reply next resumed)
        by_cases called : counted kind query
        · rw [ite_eq_left called]
          rwa [charge.mp called] at decreases
        · rw [ite_eq_right called]
          have free : spent kind phase = 0 := by
            have cap := spent_le_one kind phase
            have absent : spent kind phase ≠ 1 := fun one => called (charge.mpr one)
            omega
          simpa only [free, Nat.sub_zero] using decreases

theorem drive_bound (kind : Kind) (fuel : Nat) (phase : agreement.AgreementEffect) :
    (drive fuel phase).IsQueryBoundP (counted kind) (budget kind phase) := by
  induction fuel generalizing phase with
  | zero => trivial
  | succ fuel ih =>
      cases phase with
      | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
          simp only [drive, step, continueWith, pure_bind]
          exact ih _
      | ConvertPublic pending =>
          simp only [drive, step]
          cases requested : pending.public_key with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.ConvertPublic pending) (.convertPublic request) pending.resume
              · intro reply next resumed
                exact .convertPublic pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih
      | ConvertSecret pending =>
          simp only [drive, step]
          cases requested : pending.secret_role with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.ConvertSecret pending) (.convertSecret request) pending.resume
              · intro reply next resumed
                exact .convertSecret pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih
      | GenerateEphemeral pending =>
          simp only [drive, step]
          cases requested : pending.role with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.GenerateEphemeral pending) (.generate request) pending.resume
              · intro reply next resumed
                exact .generate pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih
      | Encapsulate pending =>
          simp only [drive, step]
          cases requested : pending.public_key with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.Encapsulate pending) (.encapsulate request) pending.resume
              · intro reply next resumed
                exact .encapsulate pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih
      | Decapsulate pending =>
          simp only [drive, step]
          cases requested : pending.ciphertext with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.Decapsulate pending) (.decapsulate request) pending.resume
              · intro reply next resumed
                exact .decapsulate pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih
      | Dh pending =>
          simp only [drive, step]
          cases requested : pending.request with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.Dh pending) (.dh request) pending.resume
              · intro reply next resumed
                exact .dh pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih
      | RootKdf pending =>
          simp only [drive, step]
          cases requested : pending.request with
          | fail error | div => simp only [continueWith, pure_bind]; trivial
          | ok request =>
              simp only [continueWith, bind_assoc, pure_bind]
              apply callback_bound kind fuel (.RootKdf pending) (.root request) pending.resume
              · intro reply next resumed
                exact .root pending request reply next requested resumed
              · cases kind <;> simp [counted, spent]
              · exact ih


theorem drive_one (kind : Kind) (fuel : Nat) (phase : agreement.AgreementEffect) :
    (drive fuel phase).IsQueryBoundP (counted kind) 1 :=
  (drive_bound kind fuel phase).mono (budget_le_one kind phase)

theorem server (kind : Kind) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) :
    (RegistrationAgreementExecutor.server control status authenticated).IsQueryBoundP (counted kind) 1 := by
  unfold RegistrationAgreementExecutor.server
  cases initial : agreement.begin_server_agreement control status authenticated with
  | fail error | div => trivial
  | ok phase => exact drive_one kind 9 phase

theorem beacon (kind : Kind) (authenticated : registration.AuthenticatedResponse) :
    (RegistrationAgreementExecutor.beacon authenticated).IsQueryBoundP (counted kind) 1 := by
  unfold RegistrationAgreementExecutor.beacon
  cases initial : agreement.begin_beacon_agreement authenticated with
  | fail error | div => trivial
  | ok phase => exact drive_one kind 9 phase

end BeaconcryptCore.Computational.RegistrationAgreementKemBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.budget_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.budget_le_one

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.progress

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.spent_le_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.spent_le_one

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.spent_le_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.spent_le_budget

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.drive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.drive_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.drive_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.drive_one

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.server

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementKemBounds.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementKemBounds.beacon
