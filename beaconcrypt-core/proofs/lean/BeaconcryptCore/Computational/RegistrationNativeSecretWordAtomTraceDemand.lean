-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrderSource

/-! Every chronological installation event uses a descriptor previously demanded by that same actual observer. The property holds for arbitrary callback programs and replies, so even a failed demand is not silently identified with a material query; the separate Prepared/source receipt establishes that last step for a valid protected literal input. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordFrontendTrace (Event State begin finish)
open PqxdhRecordLiftInterface (Role)
variable {n : Nat} {KemSK Value : Type}

def exposed : Event → List Message
  | .install _ message | .installAttempt _ message => [message]
  | _ => []

def Holds (before : State) : Prop :=
  (∀ message, before.current = some message → Event.demand message ∈ before.events) ∧
  ∀ event ∈ before.events, ∀ message ∈ exposed event, Event.demand message ∈ before.events

private theorem extend (before : State) (valid : Holds before) (current : Option Message) (extra : List Event)
    (active : ∀ message, current = some message → Event.demand message ∈ before.events ++ extra)
    (new : ∀ event ∈ extra, ∀ message ∈ exposed event, Event.demand message ∈ before.events ++ extra) :
    Holds ⟨current, before.events ++ extra⟩ := by
  refine ⟨active, ?_⟩
  intro event member message selected
  rcases List.mem_append.mp member with old | added
  · exact List.mem_append_left _ (valid.2 event old message selected)
  · exact new event added message selected

private theorem append_quiet (before : State) (valid : Holds before) (event : Event) (quiet : exposed event = []) :
    Holds { before with events := before.events ++ [event] } := by
  apply extend before valid before.current [event]
  · intro message current
    exact List.mem_append_left _ (valid.1 message current)
  · intro added member message selected
    simp only [List.mem_singleton] at member
    subst added
    rw [quiet] at selected
    cases selected

private theorem clear (before : State) (valid : Holds before) : Holds { before with current := none } := by
  refine ⟨?_, valid.2⟩
  intro message impossible
  cases impossible

private theorem demanded (before : State) (valid : Holds before) (message : Message) :
    Holds ⟨some message, before.events ++ [.demand message]⟩ := by
  apply extend before valid (some message) [.demand message]
  · intro other same
    cases same
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · intro added member other selected
    simp only [List.mem_singleton] at member
    subst added
    cases selected

private theorem attempted (role : Role) (before : State) (valid : Holds before) :
    Holds (RegistrationNativeSecretWordFrontendTrace.attempt role before) := by
  cases formed : before.current with
  | none => simpa only [RegistrationNativeSecretWordFrontendTrace.attempt, formed] using valid
  | some message =>
      simp only [RegistrationNativeSecretWordFrontendTrace.attempt, formed]
      apply extend before valid (some message) [.installAttempt role message]
      · intro other active
        exact List.mem_append_left _ (valid.1 other (formed.trans active))
      · intro event member other selected
        simp only [List.mem_singleton] at member
        subst event
        simp only [exposed, List.mem_singleton] at selected
        subst other
        exact List.mem_append_left _ (valid.1 message formed)

private theorem installed (role : Role) (reply : Bool) (before : State) (valid : Holds before) :
    Holds (RegistrationNativeSecretWordFrontendTrace.installed role reply before) := by
  cases reply with
  | false => exact clear before valid
  | true =>
      cases formed : before.current with
      | none => simpa only [RegistrationNativeSecretWordFrontendTrace.installed, formed] using clear before valid
      | some message =>
          simp only [RegistrationNativeSecretWordFrontendTrace.installed, formed]
          apply extend before valid none [.install role message]
          · intro other impossible
            cases impossible
          · intro event member other selected
            simp only [List.mem_singleton] at member
            subst event
            simp only [exposed, List.mem_singleton] at selected
            subst other
            exact List.mem_append_left _ (valid.1 message formed)

/-- The actual observer keeps the same demanded descriptor witness for every newly recorded role attempt or successful installation. -/
theorem query (request : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range request) (before : State) (valid : Holds before) :
    Holds (finish request reply (begin request before)) := by
  rcases request with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · exact clear _ (append_quiet before valid (.prepare prepare) rfl)
  · exact demanded before valid demand
  · exact valid
  · rcases environment with coin | capability
    · exact valid
    · cases capability with
      | installServer keyId binding kernel => exact installed .server reply _ (attempted .server before valid)
      | installBeacon owner shell kernel => exact installed .beacon reply _ (attempted .beacon before valid)
      | _ => exact valid
  · exact valid
  · exact append_quiet before valid (.encapsulate false key reply.1 reply.2) rfl
  · exact valid
  · exact append_quiet before valid (.encapsulate true key reply.1 reply.2) rfl
  · exact valid

/-- Every supported adaptive observer execution retains its actual descriptor-demand witnesses. -/
theorem program (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value) (before : State)
    (valid : Holds before) (result : Value × State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before)) : Holds result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind request next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      exact ih reply _ (query request reply before valid) continued

/-- Exact installation events in any concretely interpreted initialized trace retain an earlier same-descriptor demand event. -/
theorem interpreted {κ Private : Type} {target : OracleSpec κ}
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private (OracleComp target)))
    (outer : QueryImpl target ProbComp) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : Private) (result : (Value × State) × Private)
    (supported : result ∈ support (simulateQ outer ((simulateQ implementation
      (RegistrationNativeSecretWordFrontendTrace.program work)).run before)))
    (role : Role) (message : Message)
    (member : Event.install role message ∈ result.1.2.events ∨ Event.installAttempt role message ∈ result.1.2.events) :
    Event.demand message ∈ result.1.2.events := by
  have opened := PqxdhDeploymentEnvironment.support_simulateQ_subset outer _ supported
  have observed : result.1 ∈ support (RegistrationNativeSecretWordFrontendTrace.program work) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst opened
  have valid := program work RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [Holds, RegistrationNativeSecretWordFrontendTrace.initial]) result.1 observed
  rcases member with installed | attempted
  · exact valid.2 (.install role message) installed message (List.mem_singleton_self _)
  · exact valid.2 (.installAttempt role message) attempted message (List.mem_singleton_self _)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand.interpreted
