-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessRun
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTrace

/-! The extra native preparation observer is a literal fold of the retained protocol chronology. Preparation and demand events contain the complete evaluated native descriptor; all getter and installation events leave this observer unchanged. Thus the no-failure observer fact can be transported using the already proved full chronological source rather than inferred from erased outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordNativeReadiness (Audit valid step initial)
open RegistrationNativeSecretWordFrontendTrace (State Event begin finish)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)

def nativeEvent : RegistrationNativeG2Trace.Event → Audit → Audit
  | .prepare message, before => { before with native := Function.update before.native message (valid setup seed scalar message) }
  | .demand message, before => { before with bad := before.bad || (valid setup seed scalar message && !(before.native message)) }
  | _, before => before

def readNative (events : List RegistrationNativeG2Trace.Event) : Audit :=
  events.foldl (fun before event => nativeEvent setup seed scalar event before) initial

def wordEvent (event : Event) (before : Audit) : Audit :=
  nativeEvent setup seed scalar (RegistrationNativeSecretWordCheckedTrace.event candidate event) before

def read (before : State) : Audit := before.events.foldl (fun audit event => wordEvent setup seed scalar candidate event audit) initial

/-- Evaluating the complete symbolic event list gives exactly the same native preparation observer. -/
theorem evaluated_read (before : State) :
    readNative setup seed scalar (RegistrationNativeSecretWordCheckedTrace.state candidate before).events =
      read setup seed scalar candidate before := by
  simp only [readNative, RegistrationNativeSecretWordCheckedTrace.state, List.foldl_map, read, wordEvent]

private theorem append_event (events : List Event) (event : Event) :
    (events ++ [event]).foldl (fun audit event => wordEvent setup seed scalar candidate event audit) initial =
      wordEvent setup seed scalar candidate event
        (events.foldl (fun audit event => wordEvent setup seed scalar candidate event audit) initial) := by
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Every actual callback's retained chronological update gives precisely the extra native observer's update, on every original reply and failure. -/
theorem query_read (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query) (before : State) :
    read setup seed scalar candidate (finish query reply (begin query before)) =
      step setup seed scalar candidate query (read setup seed scalar candidate before) := by
  rcases query with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, wordEvent, RegistrationNativeSecretWordCheckedTrace.event, nativeEvent, step]
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, wordEvent, RegistrationNativeSecretWordCheckedTrace.event, nativeEvent, step]
  · rfl
  · rcases environment with coin | capability
    · rfl
    · cases capability <;> try rfl
      case installServer keyId binding tag =>
        cases formed : before.current <;> cases reply <;>
          simp only [begin, finish, RegistrationNativeSecretWordFrontendTrace.attempt,
            RegistrationNativeSecretWordFrontendTrace.installed, formed, read, List.foldl_append, List.foldl_cons, List.foldl_nil,
            wordEvent, RegistrationNativeSecretWordCheckedTrace.event, nativeEvent, step]
      case installBeacon owner shell tag =>
        cases formed : before.current <;> cases reply <;>
          simp only [begin, finish, RegistrationNativeSecretWordFrontendTrace.attempt,
            RegistrationNativeSecretWordFrontendTrace.installed, formed, read, List.foldl_append, List.foldl_cons, List.foldl_nil,
            wordEvent, RegistrationNativeSecretWordCheckedTrace.event, nativeEvent, step]
  · rfl
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, wordEvent, RegistrationNativeSecretWordCheckedTrace.event, nativeEvent, step]
  · cases pool <;> rfl
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, wordEvent, RegistrationNativeSecretWordCheckedTrace.event, nativeEvent, step]
  · rfl
end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace.evaluated_read' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace.evaluated_read
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace.query_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace.query_read
