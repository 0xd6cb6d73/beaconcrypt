-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeChecked
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeReadinessTrace

/-! The unchecked native preparation audit is the literal fold of the same original G2 prepare/demand events. The fold ignores all getters and installation events. Its valid-input test is exactly the actual optional native input's isSome bit, so it specializes to the already derived native readiness observer without any trace correspondence premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeG3NativeChecked (Spec State bad unchecked plain)
open RegistrationNativeG2Trace (Event begin finish)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {KemSK : Type}

def initial : State := (fun _ => false, false)

def event (input : Message → Option Pqxdh.Bytes) : Event → State → State
  | .prepare message, before => (Function.update before.1 message (input message).isSome, before.2)
  | .demand message, before => (before.1, before.2 || ((input message).isSome && !before.1 message))
  | _, before => before

def read (input : Message → Option Pqxdh.Bytes) (events : List Event) : State :=
  events.foldl (fun before selected => event input selected before) initial

def serviceStep (input : Message → Option Pqxdh.Bytes) : Spec.Domain → State → State
  | .inr (.prepare message), before => event input (.prepare message) before
  | .inr (.demand message), before => event input (.demand message) before
  | _, before => before

def nativeStep (input : Message → Option Pqxdh.Bytes) : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → State → State
  | .inl (.inl message), before => event input (.prepare message) before
  | .inl (.inr (.inl (.inl message))), before => event input (.demand message) before
  | _, before => before

/-- Every actual retained service query updates precisely its native preparation-audit state, independently of the callback reply. -/
theorem query_state (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (query : Spec.Domain) (before : State) (result : Spec.Range query × State)
    (supported : result ∈ support ((unchecked source input inside query).run before)) :
    result.2 = serviceStep input query before := by
  simp only [unchecked, StateT.run, support_map] at supported
  obtain ⟨reached, actual, rfl⟩ := supported
  cases query with
  | inl coin =>
      change reached ∈ support ((plain source input inside (.inl coin)).run before.1) at actual
      simp only [plain, StateT.run_lift, bind_pure_comp, support_map] at actual
      obtain ⟨reply, _possible, rfl⟩ := actual
      simp only [serviceStep, bad, Bool.or_false]
  | inr command => cases command with
    | prepare message =>
        simp only [plain, mem_support_pure_iff] at actual
        cases actual
        simp only [serviceStep, event, bad, Bool.or_false]
    | demand message =>
        cases formed : input message with
        | none =>
            simp only [plain, formed, mem_support_pure_iff] at actual
            cases actual
            rfl
        | some bytes =>
            simp only [plain, formed] at actual
            split at actual
            · simp only [support_map] at actual
              obtain ⟨output, _possible, rfl⟩ := actual
              rfl
            · simp only [mem_support_pure_iff] at actual
              cases actual
              rfl

/-- The original complete native chronological callback update gives exactly the unchecked preparation-audit fold update. -/
theorem query_read (input : Message → Option Pqxdh.Bytes)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range query) (before : RegistrationNativeG2Trace.State) :
    read input (finish query reply (begin query before)).events = nativeStep input query (read input before.events) := by
  rcases query with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, event, nativeStep]
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, event, nativeStep]
  · rfl
  · rcases environment with coin | capability
    · rfl
    · cases capability <;> try rfl
      case installServer keyId binding tag =>
        cases current : before.current <;> cases reply <;>
          simp only [begin, finish, RegistrationNativeG2Trace.attempt, RegistrationNativeG2Trace.installed,
            current, read, List.foldl_append, List.foldl_cons, List.foldl_nil, event, nativeStep]
      case installBeacon owner shell tag =>
        cases current : before.current <;> cases reply <;>
          simp only [begin, finish, RegistrationNativeG2Trace.attempt, RegistrationNativeG2Trace.installed,
            current, read, List.foldl_append, List.foldl_cons, List.foldl_nil, event, nativeStep]
  · rfl
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, event, nativeStep]
  · cases pool <;> rfl
  · simp only [begin, finish, read, List.foldl_append, List.foldl_cons, List.foldl_nil, event, nativeStep]
  · rfl

private theorem native_fold {ι Secret : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base Secret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (events : List Event)
    (before : RegistrationNativeSecretWordNativeReadiness.Audit) :
    let actual := events.foldl (fun audit selected => RegistrationNativeSecretWordNativeReadinessTrace.nativeEvent setup seed scalar selected audit) before
    (actual.native, actual.bad) = events.foldl (fun audit selected => event (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) selected audit)
      (before.native, before.bad) := by
  induction events generalizing before with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih]
      cases head <;> rfl

/-- At the actual native optional input, the generic unchecked fold is exactly the derived same-trace native readiness observer. -/
theorem read_native {ι Secret : Type} {base : OracleSpec ι} (setup : PqxdhServerAuthExperiment.Setup base Secret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (events : List Event) :
    let actual := RegistrationNativeSecretWordNativeReadinessTrace.readNative setup seed scalar events
    (actual.native, actual.bad) = read (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) events :=
  native_fold setup seed scalar events RegistrationNativeSecretWordNativeReadiness.initial

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace.query_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace.query_state
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace.query_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace.query_read
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace.read_native' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace.read_native
