-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthenticationFlow
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
Executable interpretation of the extracted registration authentication controller. Requests and continuations are the extracted operations themselves; primitive replies remain explicit oracle calls. Simulation into a stateful primitive implementation retains its reached state on rejection and error.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

inductive Request where
  | hash (request : registration.HashRequest)
  | mldsa (request : registration.MldsaVerificationRequest)
  | ed25519 (request : registration.Ed25519VerificationRequest)

abbrev Spec : OracleSpec Request
  | .hash _ => core.option.Option Digest
  | .mldsa _ => Bool
  | .ed25519 _ => Opened

def continueWith {Input Result : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) : OracleComp Spec (RustM Result) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def edge (event : Event) (result : RustM registration.InitAuthentication) :
    RustM (Option (Event × registration.InitAuthentication)) :=
  match result with
  | .ok state => .ok (some (event, state))
  | .fail error => .fail error
  | .div => .div

/-- One actual getter, one primitive call and its actual extracted continuation. -/
def step (state : registration.InitAuthentication) :
    OracleComp Spec (RustM (Option (Event × registration.InitAuthentication))) :=
  match state with
  | .HashRequested before => continueWith before.request fun request => do
      let reply ← Spec.query (.hash request)
      pure (edge (.hash reply) (before.resume reply))
  | .MldsaVerificationRequested before => continueWith before.request fun request => do
      let reply ← Spec.query (.mldsa request)
      pure (edge (.mldsa reply) (before.resume reply))
  | .Ed25519VerificationRequested before => continueWith before.request fun request => do
      let reply ← Spec.query (.ed25519 request)
      pure (edge (.ed25519 before.stage reply) (before.resume reply))
  | .ServerFingerprintRequested before => continueWith before.request fun request => do
      let reply ← Spec.query (.hash request)
      pure (edge (.serverFingerprint reply) (before.resume reply))
  | .BeaconFingerprintRequested before => continueWith before.request fun request => do
      let reply ← Spec.query (.hash request)
      pure (edge (.beaconFingerprint reply) (before.resume reply))
  | .Accepted _ | .Rejected => pure (.ok none)

/-- Fuel bounds callbacks, while an early terminal result keeps its complete trace. -/
def execute : Nat → registration.InitAuthentication →
    OracleComp Spec (RustM (List Event × registration.InitAuthentication))
  | 0, state => pure (.ok ([], state))
  | fuel + 1, state => do
      let result ← step state
      continueWith result fun next => match next with
      | none => pure (.ok ([], state))
      | some (event, after) => do
          let rest ← execute fuel after
          continueWith rest fun final => pure (.ok (event :: final.1, final.2))

/-- The real entry point executes at most seven callbacks, with one terminal check. -/
def begin (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    OracleComp Spec (RustM (List Event × registration.InitAuthentication)) :=
  continueWith (registration.begin_init_authentication pin packet) (execute 8)

theorem execute_zero (state : registration.InitAuthentication) :
    execute 0 state = pure (.ok ([], state)) := by
  rfl

theorem edge_success (event : Event) (result : RustM registration.InitAuthentication)
    (actual : Event) (after : registration.InitAuthentication)
    (success : edge event result = .ok (some (actual, after))) :
    event = actual ∧ result = .ok after := by
  cases result <;> simp_all [edge]

theorem run_trans {start middle final : registration.InitAuthentication} {left right : List Event}
    (first : Run start left middle) (second : Run middle right final) :
    Run start (left ++ right) final := by
  induction second with
  | step previous transition ih =>
      simpa only [List.append_assoc] using Run.step ih transition
  | refl => simpa only [List.append_nil] using first

theorem continueWith_support {Input Result : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) (value : Result)
    (supported : .ok value ∈ support (continueWith result next)) :
    ∃ input, result = .ok input ∧ .ok value ∈ support (next input) := by
  cases result <;> simp_all [continueWith]

theorem query_edge_support (query : Spec.Domain) (eventOf : Spec.Range query → Event)
    (resume : Spec.Range query → RustM registration.InitAuthentication)
    (event : Event) (after : registration.InitAuthentication)
    (supported : .ok (some (event, after)) ∈ support (do
      let reply ← (Spec.query query : OracleComp Spec (Spec.Range query))
      pure (edge (eventOf reply) (resume reply)))) :
    ∃ reply, eventOf reply = event ∧ resume reply = .ok after := by
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  exact supported.elim fun reply facts => ⟨reply, edge_success _ _ _ _ facts.2.symm⟩

end BeaconcryptCore.Computational.RegistrationAuthenticationExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.execute_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.execute_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.edge_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.edge_success

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.run_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.run_trans

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.continueWith_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.continueWith_support

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.query_edge_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationExecutor.query_edge_support
