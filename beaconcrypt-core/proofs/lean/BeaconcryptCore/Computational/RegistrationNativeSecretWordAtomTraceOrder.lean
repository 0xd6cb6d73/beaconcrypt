-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace

/-! A successful atom installation has an earlier atom installation attempt in the same chronological trace. The relevant event stream starts with an attempt, including failed insertions, so a later atom attempt would require at least two actual attempts. This is a purely ordered-event fact and introduces no independence assumption. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordFrontendTrace (Event State begin finish)
open RegistrationNativeSecretWordAtomInstallTrace (atom count attempt)
variable {n : Nat} {KemSK Value : Type}

def view (role : Role) : Event → Option Bool
  | .installAttempt actual message => if role = actual ∧ atom (some message) = 1 then some true else none
  | .install actual message => if role = actual ∧ atom (some message) = 1 then some false else none
  | _ => none

def stream (role : Role) (events : List Event) : List Bool := events.filterMap (view role)
def Good (role : Role) (events : List Event) : Prop := (stream role events).head? ≠ some false

private theorem head_append (before after : List Bool) (first : before.head? ≠ some false) (second : after.head? ≠ some false) :
    (before ++ after).head? ≠ some false := by
  cases before with
  | nil => exact second
  | cons head tail => exact first

private theorem good_append (role : Role) (before after : List Event) (first : Good role before) (second : Good role after) :
    Good role (before ++ after) := by
  unfold Good stream at *
  rw [List.filterMap_append]
  exact head_append _ _ first second

private theorem good_empty (role : Role) : Good role [] := by simp [Good, stream]

private theorem install_chunk (role actual : Role) (reply : Bool) (before : State) :
    ∃ suffix, (RegistrationNativeSecretWordFrontendTrace.installed actual reply
      (RegistrationNativeSecretWordFrontendTrace.attempt actual before)).events = before.events ++ suffix ∧ Good role suffix := by
  cases formed : before.current with
  | none => exact ⟨[], by simp [RegistrationNativeSecretWordFrontendTrace.attempt,
      RegistrationNativeSecretWordFrontendTrace.installed, formed], good_empty role⟩
  | some message =>
      cases reply with
      | false =>
          refine ⟨[.installAttempt actual message], ?_, ?_⟩
          · simp only [RegistrationNativeSecretWordFrontendTrace.attempt, RegistrationNativeSecretWordFrontendTrace.installed, formed]
          · cases role <;> cases actual <;> cases word : message.kem <;> simp [Good, stream, view, atom, word]
      | true =>
          refine ⟨[.installAttempt actual message, .install actual message], ?_, ?_⟩
          · simp only [RegistrationNativeSecretWordFrontendTrace.attempt, RegistrationNativeSecretWordFrontendTrace.installed, formed, List.append_assoc, List.cons_append, List.nil_append]
          · cases role <;> cases actual <;> cases word : message.kem <;> simp [Good, stream, view, atom, word]

private theorem query_chunk (role : Role) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query) (before : State) :
    ∃ suffix, (finish query reply (begin query before)).events = before.events ++ suffix ∧ Good role suffix := by
  rcases query with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · exact ⟨[.prepare prepare], rfl, by simp [Good, stream, view]⟩
  · exact ⟨[.demand demand], rfl, by simp [Good, stream, view]⟩
  · exact ⟨[], by simp only [begin, finish, List.append_nil], good_empty role⟩
  · rcases environment with coin | capability
    · exact ⟨[], by simp only [begin, finish, List.append_nil], good_empty role⟩
    · cases capability with
      | installServer keyId binding kernel => exact install_chunk role .server reply before
      | installBeacon owner shell kernel => exact install_chunk role .beacon reply before
      | _ => exact ⟨[], by simp only [begin, finish, List.append_nil], good_empty role⟩
  · exact ⟨[], by simp only [begin, finish, List.append_nil], good_empty role⟩
  · exact ⟨[.encapsulate false key reply.1 reply.2], rfl, by simp [Good, stream, view]⟩
  · exact ⟨[], by simp only [begin, finish, List.append_nil], good_empty role⟩
  · exact ⟨[.encapsulate true key reply.1 reply.2], rfl, by simp [Good, stream, view]⟩
  · exact ⟨[], by simp only [begin, finish, List.append_nil], good_empty role⟩

/-- Every actual observer callback preserves the order in which an atom attempt precedes its successful installation. -/
theorem query_good (role : Role) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query) (before : State)
    (valid : Good role before.events) : Good role (finish query reply (begin query before)).events := by
  obtain ⟨suffix, same, validSuffix⟩ := query_chunk role query reply before
  rw [same]
  exact good_append role _ _ valid validSuffix

/-- The exact chronological pure observer retains this order on every supported adaptive execution. -/
theorem program_good (role : Role) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : State) (valid : Good role before.events) (result : Value × State)
    (supported : result ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before)) :
    Good role result.2.events := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [RegistrationNativeSecretWordFrontendTrace.handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      exact ih reply _ (query_good role query reply before valid) continued

private theorem stream_count (role : Role) (events : List Event) :
    (stream role events).countP id = events.countP (attempt role) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event with
      | prepare message | demand message | encapsulate selected key ciphertext secret =>
          simp only [stream, List.filterMap_cons, view, List.countP_cons, attempt, Bool.false_eq_true, ite_false]
          exact ih
      | installAttempt actual message =>
          cases role <;> cases actual <;> cases word : message.kem <;>
            simpa [stream, List.filterMap_cons, view, attempt, atom, word] using ih
      | install actual message =>
          cases role <;> cases actual <;> cases word : message.kem <;>
            simpa [stream, List.filterMap_cons, view, attempt, atom, word] using ih

private theorem first_install (before after : List Bool) (valid : (before ++ false :: after).head? ≠ some false) :
    0 < before.countP id := by
  cases before with
  | nil => exact False.elim (valid rfl)
  | cons head tail =>
      cases head with
      | false => exact False.elim (valid rfl)
      | true => simp only [List.countP_cons, id_eq, ite_true]; omega

/-- With at most one actual atom attempt, a successful atom installation cannot be followed by another atom attempt of the same role. -/
theorem no_second (role : Role) (events : List Event) (valid : Good role events)
    (bounded : events.countP (attempt role) ≤ 1)
    (earlier middle later : List Event) (first second : RegistrationNativeSecretWordMessage.Message)
    (shape : events = earlier ++ [.install role first] ++ middle ++ [.installAttempt role second] ++ later)
    (firstAtom : first.kem = .atom) (secondAtom : second.kem = .atom) : False := by
  have sameStream : stream role events = stream role earlier ++ [false] ++ stream role middle ++ [true] ++ stream role later := by
    rw [shape]
    simp only [stream, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, view,
      atom, firstAtom, secondAtom, and_self, ite_true]
  change (stream role events).head? ≠ some false at valid
  rw [sameStream] at valid
  have earlierPositive : 0 < (stream role earlier).countP id := by
    apply first_install (stream role earlier) (stream role middle ++ true :: stream role later)
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using valid
  have total := stream_count role events
  rw [sameStream] at total
  simp only [List.countP_append, List.countP_singleton, id_eq, ite_true] at total
  omega

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder.no_second' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder.no_second
