-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeScalarOrdinary

/-! The actual roster changes at exactly successful owner birth. These source receipts identify the first selected scalar draw without an assumed birth schedule, public-key uniqueness or constructor-success premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeScalarRoster
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeExperiment (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem beacon_property (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (predicate : Value → RegistrationNativeBeaconFrontend.State source → Prop)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (law : ∀ inner, inner ∈ support ((work.run before.beacons).run
        (RegistrationWorldAgreementCompiler.erase before.server.world)) → predicate inner.1.1 inner.1.2)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    predicate result.1 result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have actual : inner.1 ∈ support ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  cases returned
  exact law inner.1 actual

/-- Every failed constructor leaves the roster fixed; every successful constructor appends exactly one actual owner and returns its index. -/
theorem create_shape (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source) (result : RustM (Option Nat) × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    RegistrationNativeKemBirthCreateShape.Shape before.beacons result.1 result.2.beacons :=
  beacon_property setup checks representation created _ _ before result
    (fun inner reached => RegistrationNativeKemBirthCreateShape.create_shape setup source edPin mlPin keyId
      before.beacons _ inner.1.1 inner.1.2 inner.2 reached) supported

/-- Every native callback other than creation keeps the original roster length exactly. -/
theorem noncreate_length (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (notCreate : ∀ edPin mlPin keyId, query ≠ .inr (.create edPin mlPin keyId))
    (before : State n KemSK source) (result : TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    result.2.beacons.length = before.beacons.length := by
  have ordinary (valid : RegistrationNativeStatePreservation.Ordinary query) : result.2.beacons.length = before.beacons.length :=
    congrArg List.length (RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation
      created credential query valid before result supported).2
  cases query with
  | inl coin => exact ordinary trivial
  | inr command => cases command with
    | create edPin mlPin keyId => exact False.elim (notCreate edPin mlPin keyId rfl)
    | bundle index =>
        apply beacon_property setup checks representation created _ (fun _ owners => owners.length = before.beacons.length) before result _ supported
        intro inner reached
        have same := RegistrationNativeKemBirthLifecycle.bundle_metadata setup source wire index before.beacons
          (RegistrationWorldAgreementCompiler.erase before.server.world) inner reached
        simpa only [List.length_map] using congrArg List.length same
    | finish index packet =>
        apply beacon_property setup checks representation created _ (fun _ owners => owners.length = before.beacons.length) before result _ supported
        intro inner reached
        have same := RegistrationNativeKemBirthLifecycle.finish_metadata setup source wire index packet before.beacons
          (RegistrationWorldAgreementCompiler.erase before.server.world) inner reached
        simpa only [List.length_map] using congrArg List.length same
    | _ => exact ordinary trivial

/-- Before reaching the selected position, any actual typed callback leaves the owner count at most that position. -/
theorem step_short (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (query : TypedSpec.Domain) (before : State n KemSK source)
    (result : TypedSpec.Range query × State n KemSK source) (short : before.beacons.length < selected)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    result.2.beacons.length ≤ selected := by
  by_cases isCreate : ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId)
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := isCreate
    have shape := create_shape setup checks representation created edPin mlPin keyId before result supported
    cases actual : result.1 with
    | fail error | div =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        rw [shape]
        omega
    | ok reply => cases reply with
      | none =>
          simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
          rw [shape]
          omega
      | some index =>
          simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
          obtain ⟨_index, owner, after⟩ := shape
          rw [after, List.length_append, List.length_singleton]
          omega
  · push Not at isCreate
    rw [noncreate_length setup checks wire route representation created credential query isCreate before result supported]
    omega

/-- The literal post-scalar native birth always creates the next owner, on every callback reply. -/
theorem born_length (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (prepared : RegistrationNativeBeaconFrontend.Prepared source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : State n KemSK source) (result : RustM (Option Nat) × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.appendBorn setup source edPin keyId prepared.pin prepared.credentials prepared.identity scalar)).run before)) :
    result.2.beacons.length = before.beacons.length + 1 := by
  apply beacon_property setup checks representation created _ (fun _ owners => owners.length = before.beacons.length + 1) before result _ supported
  intro inner reached
  rw [RegistrationNativeBeaconBirth.append_program] at reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨born, _bornSupport, worldOwner, _ownerSupport, returned⟩ := reached
  cases returned
  simp only [List.length_append, List.length_singleton]

end BeaconcryptCore.Computational.RegistrationNativeScalarRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRoster.create_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRoster.create_shape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRoster.noncreate_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRoster.noncreate_length
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRoster.step_short' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRoster.step_short
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeScalarRoster.born_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeScalarRoster.born_length
