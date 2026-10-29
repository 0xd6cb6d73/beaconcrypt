-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyStartup

/-! A pure analysis layer records the actual chronological preparation, demand, encapsulation and successful installation callbacks of the native frontend. Each callback is forwarded once with its literal reply; signing, World effects and failed operations are unchanged. This is an internal G2 observer state, not a new production capability or an assertion that any alias event is negligible. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG2Trace
open RegistrationNativeRelatedFamily (Message)
open PqxdhRecordLiftInterface (Role)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
variable {n : Nat} {KemSK Value : Type}

inductive Event where
  | prepare (message : Message)
  | demand (message : Message)
  | encapsulate (selected : Bool) (key : MlKem768PublicKey) (ciphertext : MlKem768Ciphertext) (secret : MlKemSharedSecret)
  | installAttempt (role : Role) (message : Message)
  | install (role : Role) (message : Message)

structure State where
  current : Option Message
  events : List Event

def initial : State := ⟨none, []⟩

def attempt (role : Role) (before : State) : State :=
  match before.current with
  | none => before
  | some message => { before with events := before.events ++ [.installAttempt role message] }

def begin : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → State → State
  | .inl (.inl message), before => ⟨none, before.events ++ [.prepare message]⟩
  | .inl (.inr (.inl (.inl message))), before => ⟨some message, before.events ++ [.demand message]⟩
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer _ _ _)))))), before => attempt .server before
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon _ _ _)))))), before => attempt .beacon before
  | _, before => before

def installed (role : Role) (reply : Bool) (before : State) : State :=
  ⟨none, match reply, before.current with
    | true, some message => before.events ++ [.install role message]
    | _, _ => before.events⟩

def finish : (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) →
    (RegistrationNativePublicFrontend.Spec n KemSK).Range query → State → State
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer _ _ _)))))), reply, before => installed .server reply before
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon _ _ _)))))), reply, before => installed .beacon reply before
  | .inl (.inr (.inr (.inl (.inr key)))), reply, before =>
      { before with events := before.events ++ [.encapsulate false key reply.1 reply.2] }
  | .inl (.inr (.inr (.inr (.inr key)))), reply, before =>
      { before with events := before.events ++ [.encapsulate true key reply.1 reply.2] }
  | _, _, before => before

def handler : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT State (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))) := fun query before =>
  (fun reply => (reply, finish query reply (begin query before))) <$>
    (RegistrationNativePublicFrontend.Spec n KemSK).query query

def program (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) :
    OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) (Value × State) :=
  (simulateQ handler work).run initial

/-- The observer forwards exactly one original query, with no synthetic callback or altered reply. -/
theorem query_erase (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State) :
    Prod.fst <$> (handler query).run before = (RegistrationNativePublicFrontend.Spec n KemSK).query query := by
  simp only [handler, StateT.run, Functor.map_map, id_map']

/-- Erasing the internal observer recovers the literal original frontend AST, including every adaptive failure continuation. -/
theorem program_erase (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State) :
    Prod.fst <$> (simulateQ handler work).run before = work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [handler, StateT.run, bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply _

/-- The real trace layer preserves every original query-predicate cap, rather than assuming a new bound for the observer. -/
theorem program_bound (predicate : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → Prop)
    [DecidablePred predicate] (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP predicate count) (before : State) :
    ((simulateQ handler work).run before).IsQueryBoundP predicate count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simp [handler, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, counted]
  · intro query free current
    simp [handler, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, free]

/-- A successful actual Server insertion records its current demanded descriptor and closes that local demand. -/
theorem installed_server (before : State) (message : Message) (active : before.current = some message) :
    installed .server true before = ⟨none, before.events ++ [.install .server message]⟩ := by
  simp only [installed, active]

/-- A failed actual insertion records no successful role and still closes the local demand. -/
theorem install_failed (role : Role) (before : State) :
    installed role false before = ⟨none, before.events⟩ := rfl

def SameRoleAlias (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (events : List Event) : Prop :=
  ∃ earlier middle later role first second bytes,
    events = earlier ++ [.install role first] ++ middle ++ [.install role second] ++ later ∧
      input first = some bytes ∧ input second = some bytes ∧ inside bytes = true

def RepeatedRoleAttempt (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (events : List Event) : Prop :=
  ∃ earlier middle later role first second bytes,
    events = earlier ++ [.install role first] ++ middle ++ [.installAttempt role second] ++ later ∧
      input first = some bytes ∧ input second = some bytes ∧ inside bytes = true

end BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Trace.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Trace.query_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Trace.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Trace.program_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Trace.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Trace.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Trace.installed_server' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Trace.installed_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG2Trace.install_failed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG2Trace.install_failed
