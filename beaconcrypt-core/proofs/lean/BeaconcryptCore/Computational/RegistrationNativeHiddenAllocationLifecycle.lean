-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFinishFields
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields

/-! Native publication and response finishing retain immutable physical owner addresses. These source facts concern the actual local controllers, including translated ordinary-owner references and all rejection paths, before choosing any KEM or World interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenAllocationOwners (Indexed NativeIndexed)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem metadata_indexed (before after : RegistrationNativeBeaconFrontend.State source)
    (valid : NativeIndexed before)
    (same : after.map RegistrationNativeOwnerFields.metadata = before.map RegistrationNativeOwnerFields.metadata) :
    NativeIndexed after := by
  intro index current found
  have earlier : (before.map RegistrationNativeOwnerFields.metadata)[index]? = some (RegistrationNativeOwnerFields.metadata current) := by
    rw [← same, List.getElem?_map, found]
    rfl
  rw [List.getElem?_map] at earlier
  obtain ⟨old, present, sameFields⟩ := Option.map_eq_some_iff.mp earlier
  exact (congrArg RegistrationNativeBeaconFrontend.Owner.worldOwner sameFields).symm.trans (valid index old present)

/-- Actual outgoing publication retains the physical address at every local position and the entire roster length. -/
theorem bundle (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (valid : Indexed owners) (supported : result ∈ support
      (((RegistrationNativePublicOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env)) :
    result.1.2.length = owners.length ∧ Indexed result.1.2 := by
  simp only [RegistrationNativePublicOwners.bundle, RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at supported
  obtain ⟨native, reached, rfl⟩ := supported
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  have same := RegistrationNativeOwnerFields.bundle_metadata setup source wire index (owners.map RegistrationNativePublicOwners.restore) env native actual
  constructor
  · rw [RegistrationNativeHiddenAllocationOwners.pack_length]
    have lengths := congrArg List.length same
    simpa only [List.length_map] using lengths
  · exact RegistrationNativeHiddenAllocationOwners.pack selected publicPrekey native.1.2
      (metadata_indexed _ _ (RegistrationNativeHiddenAllocationOwners.restore owners valid) same)

private theorem write_indexed (owners : RegistrationNativePublicOwners.State source) (valid : Indexed owners)
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source)
    (found : owners[index]? = some owner) (view : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (same : view.worldOwner = owner.view.worldOwner) : Indexed (owners.set index { owner with view }) := by
  intro position current stored
  by_cases equal : position = index
  · subst position
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, Option.some.injEq] at stored
    subst current
    exact same.trans (valid index owner found)
  · rw [List.getElem?_set_ne (Ne.symm equal)] at stored
    exact valid position current stored

/-- Selected and ordinary finish retain every physical address and the complete local roster length. -/
theorem finish (setup : Setup base KemSK) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState RegistrationServerRoleBackend.State)
    (valid : Indexed owners) (supported : result ∈ support
      (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env)) :
    result.1.2.length = owners.length ∧ Indexed result.1.2 := by
  cases found : owners[index]? with
  | none =>
      simp only [RegistrationNativePublicOwners.finish, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, valid⟩
  | some owner =>
      cases scalarEq : owner.scalar <;>
        simp only [RegistrationNativePublicOwners.finish, StateT.run, found, scalarEq, support_map] at supported
      case none =>
        obtain ⟨reached, member, equal⟩ := supported
        have kept := RegistrationNativeHiddenAllocationFinishFields.finish_index setup packet owner.view env reached member
        cases equal
        exact ⟨List.length_set, by simpa only [scalarEq] using write_indexed owners valid index owner found reached.1.2 kept⟩
      case some scalar =>
        obtain ⟨reached, member, equal⟩ := supported
        have kept := RegistrationNativeHiddenAllocationFinishFields.finish_index setup packet owner.view env reached
          (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member)
        cases equal
        exact ⟨List.length_set, by simpa only [scalarEq] using write_indexed owners valid index owner found reached.1.2 kept⟩

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle.bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle.finish
