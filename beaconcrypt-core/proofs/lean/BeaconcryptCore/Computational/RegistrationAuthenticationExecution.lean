-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

/-! Every successful executor trace consists of actual extracted continuation equations. The entry-point theorem then supplies the existing four-callback classical request-validation guarantee for every actual primitive interpretation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

theorem step_sound (initial : registration.InitAuthentication) (event : Event)
    (after : registration.InitAuthentication)
    (supported : .ok (some (event, after)) ∈ support (step initial)) :
    Step initial event after := by
  cases initial with
  | Ed25519VerificationRequested before =>
      obtain ⟨request, _, called⟩ := continueWith_support before.request _ _ supported
      exact (query_edge_support (.ed25519 request) (fun reply => .ed25519 before.stage reply)
        before.resume event after called).elim fun reply facts =>
          facts.1 ▸ Step.ed25519 before reply after facts.2
  | HashRequested before =>
      obtain ⟨request, _, called⟩ := continueWith_support before.request
        (fun request => do
          let reply ← (Spec.query (.hash request) : OracleComp Spec _)
          pure (edge (.hash reply) (before.resume reply))) (some (event, after)) supported
      exact (query_edge_support (.hash request) Event.hash before.resume event after called).elim
        fun reply facts => facts.1 ▸ Step.hash before reply after facts.2
  | Accepted accepted => simp [step] at supported
  | Rejected => simp [step] at supported

theorem execute_sound (fuel : Nat) (initial : registration.InitAuthentication) (events : List Event)
    (final : registration.InitAuthentication)
    (supported : .ok (events, final) ∈ support (execute fuel initial)) : Run initial events final := by
  induction fuel generalizing initial events final with
  | succ fuel ih =>
      simp only [execute, mem_support_bind_iff] at supported
      obtain ⟨result, first, returned⟩ := supported
      obtain ⟨next, resultEq, continued⟩ := continueWith_support result _ _ returned
      subst result
      cases next with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff, RustM.ok.injEq,
            Prod.mk.injEq] at continued
          obtain ⟨rfl, rfl⟩ := continued
          exact Run.refl _
      | some next =>
          obtain ⟨event, after⟩ := next
          simp only [mem_support_bind_iff] at continued
          obtain ⟨rest, restSupported, restReturned⟩ := continued
          obtain ⟨tail, restEq, joined⟩ := continueWith_support rest _ _ restReturned
          subst rest
          simp only [support_pure, Set.mem_singleton_iff, RustM.ok.injEq,
            Prod.mk.injEq] at joined
          obtain ⟨rfl, rfl⟩ := joined
          exact run_trans (Run.step (Run.refl initial) (step_sound initial event after first))
            (ih after tail.1 tail.2 restSupported)
  | zero =>
      simp only [execute, support_pure, Set.mem_singleton_iff, RustM.ok.injEq,
        Prod.mk.injEq] at supported
      obtain ⟨rfl, rfl⟩ := supported
      exact Run.refl _

attribute [local irreducible] execute registration.begin_init_authentication

theorem begin_sound (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (final : registration.InitAuthentication)
    (supported : .ok (events, final) ∈ support (begin pin packet)) :
    Executes pin packet events final := by
  unfold begin at supported
  obtain ⟨initial, started, executed⟩ := continueWith_support
    (registration.begin_init_authentication pin packet) (execute 5) (events, final) supported
  exact ⟨initial, started, execute_sound 5 initial events final executed⟩

theorem begin_accepted_classical_checks (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket) (events : List Event) (accepted : registration.AuthenticatedInit)
    (supported : .ok (events, .Accepted accepted) ∈ support (begin pin packet)) :
    ValidatedRequestHistory packet events := by
  exact accepted_requires_classical_checks pin packet events accepted
    (begin_sound pin packet events (.Accepted accepted) supported)

theorem begin_accepted_callback_count (pin : session.ServerAuthenticationPin)
    (packet : registration.InitPacket) (events : List Event) (accepted : registration.AuthenticatedInit)
    (supported : .ok (events, .Accepted accepted) ∈ support (begin pin packet)) :
    events.length = 4 := by
  exact accepted_callback_count pin packet events accepted
    (begin_sound pin packet events (.Accepted accepted) supported)

/-- Stateful primitive interpretation cannot invent an accepting controller trace. -/
theorem simulated_begin_sound {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (final : registration.InitAuthentication) (before after : State)
    (supported : (.ok (events, final), after) ∈ support
      ((simulateQ implementation (begin pin packet)).run before)) :
    Executes pin packet events final := by
  apply begin_sound pin packet events final
  apply OracleComp.support_simulateQ_run'_subset implementation (begin pin packet) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

theorem simulated_begin_accepted_classical_checks {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (before after : State)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((simulateQ implementation (begin pin packet)).run before)) :
    ValidatedRequestHistory packet events ∧ events.length = 4 := by
  have execution := simulated_begin_sound implementation pin packet events (.Accepted accepted)
    before after supported
  exact ⟨accepted_requires_classical_checks pin packet events accepted execution,
    accepted_callback_count pin packet events accepted execution⟩

/-- A supported native execution retains the actual entry pin, signed fields and request-hash reply. -/
theorem simulated_begin_accepted_request_provenance {State : Type}
    (implementation : QueryImpl Spec (StateT State ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (before after : State)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((simulateQ implementation (begin pin packet)).run before)) :
    accepted.binding.server_pin = pin ∧
      accepted.binding.init_fields = BeaconcryptCore.Refinement.RegistrationAuthentication.ownedFields packet ∧
      ∃ tail, events = .hash (.Some accepted.binding.init_hash) :: tail :=
  accepted_request_provenance pin packet events accepted
    (simulated_begin_sound implementation pin packet events (.Accepted accepted) before after supported)

end BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.step_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.step_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.execute_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.execute_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.begin_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.begin_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.begin_accepted_classical_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.begin_accepted_classical_checks

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.begin_accepted_callback_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.begin_accepted_callback_count

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.simulated_begin_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.simulated_begin_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.simulated_begin_accepted_classical_checks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.simulated_begin_accepted_classical_checks

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.simulated_begin_accepted_request_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.simulated_begin_accepted_request_provenance
