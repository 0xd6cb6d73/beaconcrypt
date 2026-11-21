-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedFrontend
import BeaconcryptCore.Computational.RegistrationNativeG2Trace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendTrace

/-! The checked source's private Unit audits carry the actual preparation and demand chronology. This observer consumes those audits, records the unchanged common installation and KEM replies, and forwards every other checked callback once. Its trace uses literal native messages; evaluation of the symbolic frontend trace is explicit. No observation is inferred from an erased source equation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace
open RegistrationNativeSecretWordCheckedFrontend (Spec PlainSpec erase)
open RegistrationNativeG2Trace (State Event)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {n : Nat} {KemSK Value : Type}

def event (candidate : MlKemSharedSecret) : RegistrationNativeSecretWordFrontendTrace.Event → Event
  | .prepare message => .prepare (RegistrationNativeSecretWordMessage.eval candidate message)
  | .demand message => .demand (RegistrationNativeSecretWordMessage.eval candidate message)
  | .encapsulate selected key ciphertext secret => .encapsulate selected key ciphertext (secret.eval candidate)
  | .installAttempt role message => .installAttempt role (RegistrationNativeSecretWordMessage.eval candidate message)
  | .install role message => .install role (RegistrationNativeSecretWordMessage.eval candidate message)

def state (candidate : MlKemSharedSecret) (before : RegistrationNativeSecretWordFrontendTrace.State) : State :=
  ⟨before.current.map (RegistrationNativeSecretWordMessage.eval candidate), before.events.map (event candidate)⟩

def begin (query : (Spec n KemSK).Domain) (before : State) : State :=
  match query with
  | .inr (.inr (.prepare message)) => ⟨none, before.events ++ [.prepare message]⟩
  | .inr (.inr (.demand message)) => ⟨some message, before.events ++ [.demand message]⟩
  | .inr (.inl (.inl common)) => RegistrationNativeG2Trace.begin
      (n := n) (KemSK := KemSK) (.inl (.inr (.inl (.inr common)))) before
  | _ => before

def finish (candidate : MlKemSharedSecret) : (query : (Spec n KemSK).Domain) → (Spec n KemSK).Range query → State → State
  | .inr (.inl (.inl common)), reply, before => RegistrationNativeG2Trace.finish
      (n := n) (KemSK := KemSK) (.inl (.inr (.inl (.inr common)))) reply before
  | .inr (.inl (.inr (.inl (.inl (.inr key))))), reply, before =>
      { before with events := before.events ++ [.encapsulate false key reply.1 (reply.2.eval candidate)] }
  | .inr (.inl (.inr (.inl (.inr (.inr key))))), reply, before =>
      { before with events := before.events ++ [.encapsulate true key reply.1 (reply.2.eval candidate)] }
  | _, _, before => before

def handler (candidate : MlKemSharedSecret) : QueryImpl (Spec n KemSK) (StateT State (OracleComp (PlainSpec n KemSK))) :=
  fun query before => (fun reply => (reply, finish candidate query reply (begin query before))) <$> erase query

/-- Consuming a private Unit audit changes only the exact native chronological trace and emits no oracle call. -/
theorem audit_query (candidate : MlKemSharedSecret) (audit : RegistrationNativeSecretWordChecked.Audit) (before : State) :
    (handler (n := n) (KemSK := KemSK) candidate (.inr (.inr audit))).run before =
      pure ((), begin (n := n) (KemSK := KemSK) (.inr (.inr audit)) before) := by
  cases audit <;> rfl

/-- The observer removes only Unit audits and its own trace state; every key, common, KEM and record query remains literal. -/
theorem query_erase (candidate : MlKemSharedSecret) (query : (Spec n KemSK).Domain) (before : State) :
    Prod.fst <$> (handler candidate query).run before = erase query := by
  simp only [handler, StateT.run, Functor.map_map, id_map']

/-- Erasing the private observer gives precisely the checked interface's explicit audit erasure through every adaptive continuation. -/
theorem program_erase (candidate : MlKemSharedSecret) (work : OracleComp (Spec n KemSK) Value) (before : State) :
    Prod.fst <$> (simulateQ (handler candidate) work).run before = simulateQ erase work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [handler, StateT.run, bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply _

/-- Evaluation preserves a concrete role attempt, including a missing current demand. -/
theorem attempt_state (candidate : MlKemSharedSecret) (role : PqxdhRecordLiftInterface.Role)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :
    state candidate (RegistrationNativeSecretWordFrontendTrace.attempt role before) =
      RegistrationNativeG2Trace.attempt role (state candidate before) := by
  cases found : before.current <;>
    simp only [RegistrationNativeSecretWordFrontendTrace.attempt, RegistrationNativeG2Trace.attempt,
      state, found, Option.map_none, Option.map_some, List.map_append, List.map_cons, List.map_nil, event]

/-- Evaluation preserves successful and failed concrete installation outcomes and clears the same active demand. -/
theorem installed_state (candidate : MlKemSharedSecret) (role : PqxdhRecordLiftInterface.Role) (reply : Bool)
    (before : RegistrationNativeSecretWordFrontendTrace.State) :
    state candidate (RegistrationNativeSecretWordFrontendTrace.installed role reply before) =
      RegistrationNativeG2Trace.installed role reply (state candidate before) := by
  cases reply <;> cases found : before.current <;>
    simp only [RegistrationNativeSecretWordFrontendTrace.installed, RegistrationNativeG2Trace.installed,
      state, found, Option.map_none, Option.map_some, List.map_append, List.map_cons, List.map_nil, event]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.audit_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.audit_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.query_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.program_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.attempt_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.attempt_state
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.installed_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace.installed_state
