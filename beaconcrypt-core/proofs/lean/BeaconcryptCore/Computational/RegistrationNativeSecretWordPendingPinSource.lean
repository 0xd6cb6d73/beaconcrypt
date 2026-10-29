-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinInterface

/-! The actual symbolic constructor and outgoing controller inherit the stronger stored-pin invariant from their literal native execution. Scalar erasure preserves both the retained pin and pending phase; no runtime or whole-source equality is postulated. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordPendingPin (Coherent Holds holds_iff)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem restored_holds (owners : RegistrationNativePublicOwners.State source) (valid : Holds owners) :
    RegistrationNativeSecretWordPendingPinNative.Holds (owners.map RegistrationNativePublicOwners.restore) := by
  intro owner member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have prior := (holds_iff owners).mp valid original present
  cases phase : original.view.phase
  all_goals simp only [RegistrationNativeSecretWordPendingPinNative.Coherent, Coherent, phase,
    RegistrationNativePublicOwners.restore, RegistrationBeaconReferenceCompiler.restoreOwner] at prior ⊢
  all_goals exact prior

private theorem packed_holds (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (valid : RegistrationNativeSecretWordPendingPinNative.Holds owners) :
    Holds (RegistrationNativePublicOwners.pack selected publicPrekey owners) := by
  intro index owner found
  simp only [RegistrationNativePublicOwners.pack, List.getElem?_mapIdx, Option.map_eq_some_iff] at found
  obtain ⟨original, present, rfl⟩ := found
  have prior := valid original (List.mem_of_getElem? present)
  cases phase : original.phase <;> by_cases chosen : index = selected
  all_goals simp only [chosen, ite_true, ite_false, Coherent, RegistrationNativeSecretWordPendingPinNative.Coherent, phase,
    RegistrationBeaconReferenceCompiler.eraseOwner] at prior ⊢
  all_goals exact prior

/-- The same actual symbolic outgoing bundle preserves the pending controller's equality with its indexed owner's configured pin. -/
theorem bundle_keeps (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected index : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (prior : Holds owners) (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env)) :
    Holds result.1.2 := by
  simp only [RegistrationNativeSecretWordOwners.bundle, RegistrationNativeSecretWordOwners.executeLocal, StateT.run] at supported
  have pubSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at pubSupport
  obtain ⟨reached, called, equal⟩ := pubSupport
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have kept := RegistrationNativeSecretWordPendingPinNative.bundle_keeps setup wire index
    (owners.map RegistrationNativePublicOwners.restore) env reached (restored_holds owners prior) native
  cases equal
  exact packed_holds selected publicPrekey reached.1.2 kept

/-- Actual symbolic construction appends only a fresh owner and preserves the stored-pin relation of every earlier pending owner. -/
theorem create_keeps (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary)
    (prior : Holds owners) (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env)) :
    Holds result.1.2 := by
  simp only [RegistrationNativeSecretWordOwners.create, RegistrationNativeSecretWordOwners.executeLocal, StateT.run] at supported
  have pubSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at pubSupport
  obtain ⟨reached, called, equal⟩ := pubSupport
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have kept := RegistrationNativeSecretWordPendingPinNative.create_keeps setup edPin mlPin keyId
    (owners.map RegistrationNativePublicOwners.restore) env reached (restored_holds owners prior) native
  cases equal
  exact packed_holds selected publicPrekey reached.1.2 kept

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource.bundle_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource.bundle_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource.create_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource.create_keeps
