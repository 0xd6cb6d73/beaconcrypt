-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationNativeKemBirthSourceInvariant
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-! Actual native construction extends the owner roster while every later lifecycle step retains each previous immutable owner snapshot. This preserves generated identities without a public-key injectivity assumption or an owner-before-accept restriction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerRoster
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State)
open RegistrationNativeOwnerFields (metadata)
open RegistrationNativeRawAdapter (TypedSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.accept

def Prefix (before after : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∃ tail, after.map metadata = before.map metadata ++ tail

private theorem refl (owners : RegistrationNativeBeaconFrontend.State source) : Prefix owners owners :=
  ⟨[], (List.append_nil _).symm⟩

private theorem trans (first middle last : RegistrationNativeBeaconFrontend.State source)
    (earlier : Prefix first middle) (later : Prefix middle last) : Prefix first last := by
  obtain ⟨left, before⟩ := earlier
  obtain ⟨right, after⟩ := later
  exact ⟨left ++ right, by rw [after, before, List.append_assoc]⟩

/-- Lookup of an earlier public owner retains its exact private handle and public KEM bytes, even after later creations. -/
theorem lookup (before after : RegistrationNativeBeaconFrontend.State source) (preserved : Prefix before after)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (found : before[index]? = some owner) :
    ∃ current, after[index]? = some current ∧ metadata current = metadata owner := by
  obtain ⟨tail, same⟩ := preserved
  have mapped : (after.map metadata)[index]? = some (metadata owner) := by
    rw [same, List.getElem?_append_left (by simpa only [List.length_map] using (List.getElem?_eq_some_iff.mp found).1)]
    simp [found]
  rw [List.getElem?_map] at mapped
  exact Option.map_eq_some_iff.mp mapped

private theorem beacon_prefix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (localLaw : ∀ owners env result, result ∈ support ((work.run owners).run env) → Prefix owners result.1.2)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    Prefix before.beacons result.2.beacons := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have actual : inner.1 ∈ support
      ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have retained := localLaw before.beacons _ inner.1 actual
  cases returned
  exact retained

private theorem create_prefix (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (supported : result ∈ support (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    Prefix owners result.1.2 := by
  have shape := RegistrationNativeKemBirthCreateShape.create_shape setup source edPin mlPin keyId owners env
    result.1.1 result.1.2 result.2 supported
  cases actual : result.1.1 with
  | fail error | div =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
      simpa only [shape] using refl owners
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        simpa only [shape] using refl owners
    | some index =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        obtain ⟨_index, owner, same⟩ := shape
        exact ⟨[metadata owner], by rw [same, List.map_append]; rfl⟩

/-- Every actual typed source callback preserves the earlier owner-to-private-KEM roster, including all failed native paths. -/
theorem typed_prefix (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (before : State n KemSK source) (result : TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential query).run before)) : Prefix before.beacons result.2.beacons := by
  have ordinary (valid : RegistrationNativeStatePreservation.Ordinary query) : Prefix before.beacons result.2.beacons := by
    have same := (RegistrationNativeStatePreservation.handler_keeps setup checks wire route representation created
      credential query valid before result supported).2
    simpa only [same] using refl before.beacons
  cases query with
  | inl coin => exact ordinary trivial
  | inr command => cases command with
    | create edPin mlPin keyId => exact beacon_prefix setup checks representation created _ (create_prefix setup edPin mlPin keyId) before result supported
    | bundle index =>
        apply beacon_prefix setup checks representation created _ _ before result supported
        intro owners env inner reached
        exact ⟨[], by simpa only [List.append_nil] using RegistrationNativeOwnerFields.bundle_metadata setup source wire index owners env inner reached⟩
    | finish index packet =>
        apply beacon_prefix setup checks representation created _ _ before result supported
        intro owners env inner reached
        exact ⟨[], by simpa only [List.append_nil] using RegistrationNativeOwnerFields.finish_metadata setup source wire index packet owners env inner reached⟩
    | _ => exact ordinary trivial

/-- Arbitrary adaptive typed native continuations retain all old owner handles and KEM public keys. -/
theorem program_prefix (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp TypedSpec Value) (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential) work).run before)) : Prefix before.beacons result.2.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => Prefix before.beacons current.beacons)
    (fun query current prior next reached => trans _ _ _ prior
      (typed_prefix setup checks wire route representation created credential query current next reached))
    work before (refl before.beacons) result supported

/-- Actual raw parsing and projected native replies retain the same source roster relation. -/
theorem raw_program_prefix (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeInterface.Spec Value) (before : State n KemSK source)
    (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)) work).run before)) :
    Prefix before.beacons result.2.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_prefix setup checks wire route representation created credential _ before result supported

/-- Original secrecy draws and internal sends preserve the roster below the complete original ledger step. -/
theorem full_step_prefix (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    Prefix before.2.beacons result.2.2.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact raw_program_prefix setup checks wire route representation created credential _ before.2 inner reached

end BeaconcryptCore.Computational.RegistrationNativeOwnerRoster
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.lookup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.typed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.typed_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.program_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.raw_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.raw_program_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.full_step_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerRoster.full_step_prefix
