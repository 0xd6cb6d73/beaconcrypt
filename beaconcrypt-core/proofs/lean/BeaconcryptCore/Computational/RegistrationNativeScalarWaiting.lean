-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarRoster

/-! Concrete source receipts for the waiting phase of the eager scalar argument. All ordinary callbacks preserve the remaining target position, and the literal selected birth crosses it exactly once. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarWaiting
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeExperiment (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Away (selected : Nat) (query : TypedSpec.Domain) (before : State n KemSK source) : Prop :=
  ∀ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) → before.beacons.length ≠ selected

/-- Every callback away from selected creation is literally the ordinary native source callback. -/
theorem away_handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes) (query : TypedSpec.Domain)
    (before : State n KemSK source) (away : Away selected query before) :
    (RegistrationNativeScalarEager.handler setup checks wire route representation created source credential selected scalar query).run before =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before := by
  cases query with
  | inl coin => rfl
  | inr command =>
      cases command <;> try rfl
      case create edPin mlPin keyId =>
        exact RegistrationNativeScalarOrdinary.handler setup checks wire route representation created credential
          selected scalar _ before (away edPin mlPin keyId rfl)

/-- An actual callback away from the selected birth leaves its target waiting, including every rejected native path. -/
theorem away_short (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (query : TypedSpec.Domain) (before : State n KemSK source)
    (result : TypedSpec.Range query × State n KemSK source) (short : before.beacons.length ≤ selected)
    (away : Away selected query before)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    result.2.beacons.length ≤ selected := by
  by_cases isCreate : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId)
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := isCreate
    exact RegistrationNativeScalarRoster.step_short setup checks wire route representation created credential
      selected _ before result (by have different := away edPin mlPin keyId rfl; omega) supported
  · push Not at isCreate
    rw [RegistrationNativeScalarRoster.noncreate_length setup checks wire route representation created credential query isCreate before result supported]
    exact short

/-- The actual counted scalar draw preserves the whole existing owner roster. -/
theorem sample_owners (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : State n KemSK source)
    (result : PqxdhJointGapDh.ScalarBytes × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before)) :
    result.2.beacons = before.beacons := by
  rw [RegistrationNativeScalarSource.scalar, support_map] at supported
  obtain ⟨scalar, _possible, equal⟩ := supported
  cases equal
  rfl

/-- A successful final native birth crosses the selected roster position after its unchanged counted dummy draw. -/
theorem birth_done (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (selected : Nat)
    (edPin : Std.Array U8 32#usize) (keyId : U64) (prepared : RegistrationNativeBeaconFrontend.Prepared source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : State n KemSK source) (chosen : before.beacons.length = selected)
    (drawn : PqxdhJointGapDh.ScalarBytes × State n KemSK source)
    (drawnSupport : drawn ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar)).run before))
    (born : RustM (Option Nat) × State n KemSK source)
    (bornSupport : born ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin prepared.credentials prepared.identity scalar)).run drawn.2)) :
    selected < born.2.beacons.length := by
  have same := sample_owners setup checks representation created before drawn drawnSupport
  have counted := RegistrationNativeScalarRoster.born_length setup checks representation created edPin keyId prepared scalar drawn.2 born bornSupport
  rw [same, chosen] at counted
  omega

end BeaconcryptCore.Computational.RegistrationNativeScalarWaiting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.away_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.away_handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.away_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.away_short
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.sample_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.sample_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.birth_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarWaiting.birth_done
