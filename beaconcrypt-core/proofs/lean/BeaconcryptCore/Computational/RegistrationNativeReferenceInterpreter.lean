-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedServerService
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot

/-! The first related-root hop uses a concrete all-known material interpreter. It forwards root preparation once, stores only the returned opaque root under the public descriptor, and evaluates the actual source108 schedule at later demand. It does not compute the private literal input or a Protected bit. The subsequent private paired/seed rewrite is a separate step after the root hop. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativePairedServerService (PublicSpec Common)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat} {Value : Type}

abbrev PrepareSpec := Message →ₒ Option Message
abbrev Spec (n : Nat) := PrepareSpec + PublicSpec n
abbrev Target (n : Nat) := RootSpec + Common n
abbrev State := Message → Option RootOutput

def initial : State := fun _ => none

def compiler (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl (Spec n) (StateT State (OracleComp (Target n)))
  | .inl message => fun before => do
      let root ← ((Target n).query (.inl (.inr (.derive message))) : OracleComp (Target n) _)
      pure (root.map (fun _ => message), Function.update before message root)
  | .inr (.inl message) => fun before =>
      pure ((before message).map (fun root => RegistrationNativePairedChoice.Choice.known
        (PqxdhServerAuthKeySchedule.fromRoot source root)), before)
  | .inr (.inr query) => fun before =>
      (fun reply => (reply, before)) <$> ((Target n).query (.inr query) : OracleComp (Target n) _)

def client (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (work : OracleComp (Spec n) Value) : OracleComp (Target n) Value :=
  (simulateQ (compiler source) work).run' initial

/-- The public native preparation performs the actual root query before erasing only its returned root from the API reply. -/
theorem prepare_query (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (message : Message) (before : State) :
    (compiler (n := n) source (.inl message)).run before = (do
      let root ← ((Target n).query (.inl (.inr (.derive message))) : OracleComp (Target n) _)
      pure (root.map (fun _ => message), Function.update before message root)) := rfl

/-- A prepared native token retains its real deferred source material, without an independent-context premise. -/
theorem demand_known (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (message : Message)
    (before : State) (root : RootOutput) (prepared : before message = some root) :
    (compiler (n := n) source (.inr (.inl message))).run before =
      pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source root)), before) := by
  simp only [compiler, StateT.run, prepared, Option.map_some]

/-- A material call cannot manufacture an earlier successful root preparation. -/
theorem demand_missing (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (message : Message)
    (before : State) (missing : before message = none) :
    (compiler (n := n) source (.inr (.inl message))).run before = pure (none, before) := by
  simp only [compiler, StateT.run, missing, Option.map_none]


def IsPrepare : (Spec n).Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred (IsPrepare (n := n)) := fun query => by
  cases query with
  | inl _ => exact isTrue trivial
  | inr _ => exact isFalse id

def IsRoot : (Target n).Domain → Prop
  | .inl (.inr (.derive _)) => True
  | _ => False

instance : DecidablePred (IsRoot (n := n)) := fun query => by
  cases query with
  | inr _ => exact isFalse id
  | inl query => cases query with
    | inl _ => exact isFalse id
    | inr query => cases query with
      | sign _ => exact isFalse id
      | publicHmac _ _ => exact isFalse id
      | derive _ => exact isTrue trivial

/-- A root query occurs at native preparation, never at deferred material demand or a local record/signing continuation. -/
theorem compiler_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : (Spec n).Domain) (before : State) :
    ((compiler source query).run before).IsQueryBoundP IsRoot (if IsPrepare query then 1 else 0) := by
  cases query with
  | inl message => simp [compiler, StateT.run, IsRoot, IsPrepare]
  | inr query => cases query with
    | inl message => trivial
    | inr query => simp [compiler, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsRoot, IsPrepare]

/-- The complete root-free native phase schedule retains the actual structural preparation bill at its first primitive hop. -/
theorem client_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (work : OracleComp (Spec n) Value) (cap : Nat) (bounded : work.IsQueryBoundP IsPrepare cap) :
    (client source work).IsQueryBoundP IsRoot cap := by
  unfold client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted before
    simpa only [ite_eq_left counted] using compiler_bound source query before
  · intro query free before
    simpa only [ite_eq_right free] using compiler_bound source query before

abbrev WithSpec {Index : Type} (extra : OracleSpec Index) (n : Nat) := PrepareSpec + (PublicSpec n + extra)
abbrev WithTarget {Index : Type} (extra : OracleSpec Index) (n : Nat) := RootSpec + (Common n + extra)

def targetLift {Index : Type} (extra : OracleSpec Index) : QueryImpl (Target n) (OracleComp (WithTarget extra n))
  | .inl query => (WithTarget extra n).query (.inl query)
  | .inr query => (WithTarget extra n).query (.inr (.inl query))

/-- The actual indexed KEM service can be threaded beside native phases without an extra root interface or a private-input oracle. -/
def compilerWith {Index : Type} (extra : OracleSpec Index)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl (WithSpec extra n) (StateT State (OracleComp (WithTarget extra n)))
  | .inl message => fun before => simulateQ (targetLift extra) ((compiler source (.inl message)).run before)
  | .inr (.inl query) => fun before => simulateQ (targetLift extra) ((compiler source (.inr query)).run before)
  | .inr (.inr query) => fun before =>
      (fun reply => (reply, before)) <$> ((WithTarget extra n).query (.inr (.inr query)) : OracleComp (WithTarget extra n) _)

end BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.prepare_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.prepare_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.demand_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.demand_known
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.demand_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.demand_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.compiler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter.client_bound
