-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementQueryTrace
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Actual Core conversion readiness also erases its private guard when the same tree returns its complete query/reply trace. Thus logging is retained during the source/native role coupling. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard
open RegistrationAgreementExecutor RegistrationAgreementIdentityGuard RegistrationAgreementQueryTrace
variable {m : Type → Type} [Monad m] [LawfulMonad m]
theorem drive_trace_erasure (base : QueryImpl Spec m) (fuel : Nat) (phase : agreement.AgreementEffect)
    (flag : Bool) (journal : Trace) (ready : Ready phase flag) :
    Prod.fst <$> ((simulateQ (implementation base) (trace (drive fuel phase) journal)).run flag) =
      simulateQ base (trace (drive fuel phase) journal) := by
  induction fuel generalizing phase flag journal with
  | zero => simp only [drive, trace_pure, simulateQ_pure, StateT.run_pure, map_pure]
  | succ fuel ih =>
    cases phase with
    | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
      simp only [drive, step, continueWith, pure_bind]
      exact ih _ flag journal ready
    | ConvertPublic pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag _
      apply progress (.convertPublic pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | ConvertSecret pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  secret_run, StateT.run_bind,    pure_bind, map_bind, bind_map_left,  bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final reply _
      exact converted pending reply final resumed
    | GenerateEphemeral pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag _
      apply progress (.generate pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | Encapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag _
      apply progress (.encapsulate pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | Decapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag _
      apply progress (.decapsulate pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | Dh pending =>
      have yes : flag = true := ready trivial
      subst flag
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  dh_ready, StateT.run_bind,    pure_bind, map_bind, bind_map_left,  bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final true _
      apply progress (.dh pending request reply final requested resumed) true
      · intro secret impossible
        cases impossible
      · exact ready
    | RootKdf pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total pending
      simp only [drive, step, trace_query_bind, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag _
      apply progress (.root pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready

theorem server (base : QueryImpl Spec m) (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (journal : Trace) :
    Prod.fst <$> ((simulateQ (implementation base)
      (trace (RegistrationAgreementExecutor.server control status authenticated) journal)).run false) =
      simulateQ base (trace (RegistrationAgreementExecutor.server control status authenticated) journal) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total control status authenticated
  unfold RegistrationAgreementExecutor.server
  rw [started]
  exact drive_trace_erasure base 9 phase false journal
    (RegistrationAgreementEntryReadiness.server_ready control status authenticated phase started)

theorem beacon (base : QueryImpl Spec m) (authenticated : registration.AuthenticatedResponse) (journal : Trace) :
    Prod.fst <$> ((simulateQ (implementation base)
      (trace (RegistrationAgreementExecutor.beacon authenticated) journal)).run false) =
      simulateQ base (trace (RegistrationAgreementExecutor.beacon authenticated) journal) := by
  obtain ⟨phase, started⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.begin_beacon_agreement_total authenticated
  unfold RegistrationAgreementExecutor.beacon
  rw [started]
  exact drive_trace_erasure base 9 phase false journal
    (RegistrationAgreementEntryReadiness.beacon_ready authenticated phase started)

theorem lookup (base : QueryImpl Spec m) (pending : peer.RegistrationLookup) (consumed : Bool) (journal : Trace) :
    Prod.fst <$> ((simulateQ (implementation base)
      (trace (continueWith (pending.resume consumed) (drive 9)) journal)).run false) =
      simulateQ base (trace (continueWith (pending.resume consumed) (drive 9)) journal) := by
  have normal : ∃ phase, pending.resume consumed = .ok phase := by
    cases consumed with
    | false => exact BeaconcryptCore.PanicFreedom.KeyAgreement.begin_server_agreement_total pending.control .Fresh pending.authenticated
    | true => exact ⟨.Rejected .None, rfl⟩
  obtain ⟨phase, started⟩ := normal
  rw [started]
  exact drive_trace_erasure base 9 phase false journal
    (RegistrationAgreementEntryReadiness.lookup_ready pending consumed phase started)
end BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.drive_trace_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.drive_trace_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.server

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementQueryTraceGuard.lookup
