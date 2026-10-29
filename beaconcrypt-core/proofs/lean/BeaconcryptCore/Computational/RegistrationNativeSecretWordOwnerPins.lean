-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-! The actual selected-scalar view preserves immutable configured owner pins. Native outgoing controller metadata preserves these public bindings independently of every private root or KEM interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicOwners (Owner State)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def key (owner : Owner source) : PqxdhBeaconPhase2Preparation.Word32 × U64 :=
  (owner.view.pin.binding.identity_public_key, owner.view.pin.binding.identity_key_id)
def nativeKey (owner : RegistrationNativeBeaconFrontend.Owner source) : PqxdhBeaconPhase2Preparation.Word32 × U64 :=
  (owner.pin.binding.identity_public_key, owner.pin.binding.identity_key_id)

/-- Erasing the selected scalar preserves every configured owner pin. -/
theorem pack_keys (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) :
    (RegistrationNativePublicOwners.pack selected publicPrekey owners).map key = owners.map nativeKey := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, RegistrationNativePublicOwners.pack, List.getElem?_mapIdx]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      by_cases chosen : index = selected <;>
        simp only [Option.map_some, chosen, ite_true, ite_false, key, nativeKey,
          RegistrationBeaconReferenceCompiler.eraseOwner]

/-- Restoring any ordinary scalar preserves the same immutable owner bindings. -/
theorem restore_keys (owners : State source) :
    (owners.map RegistrationNativePublicOwners.restore).map nativeKey = owners.map key := by
  simp only [List.map_map]
  rfl

/-- Every actual symbolic outgoing publication retains all configured owner pins, including failed signatures and writers. -/
theorem bundle_keys (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (selected index : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env)) :
    result.1.2.map key = owners.map key := by
  simp only [RegistrationNativeSecretWordOwners.bundle, RegistrationNativeSecretWordOwners.executeLocal,
    StateT.run] at supported
  have pubSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at pubSupport
  obtain ⟨reached, called, equal⟩ := pubSupport
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have fields := RegistrationNativeOwnerFields.bundle_metadata setup source wire index
    (owners.map RegistrationNativePublicOwners.restore) env reached native
  have pins : reached.1.2.map nativeKey = (owners.map RegistrationNativePublicOwners.restore).map nativeKey := by
    simp only [List.map_map]
    change reached.1.2.map (fun owner => (owner.pin.binding.identity_public_key, owner.pin.binding.identity_key_id)) =
      owners.map (fun owner => ((RegistrationNativePublicOwners.restore owner).pin.binding.identity_public_key,
        (RegistrationNativePublicOwners.restore owner).pin.binding.identity_key_id))
    simpa only [List.map_map, Function.comp_def, nativeKey, RegistrationNativeOwnerFields.metadata] using congrArg (List.map nativeKey) fields
  cases equal
  rw [pack_keys, pins, restore_keys]
/-- A successful actual symbolic constructor appends exactly its configured binding; every rejected constructor retains all earlier pins. -/
theorem create_keys (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : RegistrationServerReferenceCompiler.Environment)
    (result : (RustM (Option Nat) × State source) × RegistrationServerReferenceCompiler.Environment)
    (supported : result ∈ support
      (((RegistrationNativeSecretWordOwners.create (n := n) setup source selected publicPrekey edPin mlPin keyId).run owners).run env)) :
    result.1.2.map key = match result.1.1 with
      | .ok (some _) => owners.map key ++ [(edPin, keyId)]
      | _ => owners.map key := by
  simp only [RegistrationNativeSecretWordOwners.create, RegistrationNativeSecretWordOwners.executeLocal,
    StateT.run] at supported
  have pubSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, support_map] at pubSupport
  obtain ⟨reached, called, equal⟩ := pubSupport
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have shape := RegistrationNativeKemBirthCreateShape.create_shape setup source edPin mlPin keyId
    (owners.map RegistrationNativePublicOwners.restore) env reached.1.1 reached.1.2 reached.2 native
  cases equal
  rw [pack_keys]
  cases actual : reached.1.1 with
  | fail error | div =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
      rw [shape, restore_keys]
  | ok reply => cases reply with
    | none =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        rw [shape, restore_keys]
    | some index =>
        simp only [RegistrationNativeKemBirthCreateShape.Shape, actual] at shape
        obtain ⟨indexEq, born, roster⟩ := shape
        obtain ⟨owner, found, binding, _ml⟩ := RegistrationNativeOwnerPinBirth.create_pin setup source edPin mlPin keyId
          (owners.map RegistrationNativePublicOwners.restore) env index reached.1.2 reached.2 (by
            have same : reached = ((.ok (some index), reached.1.2), reached.2) := Prod.ext (Prod.ext actual rfl) rfl
            exact same ▸ native)
        rw [roster, indexEq] at found
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at found
        have bornPin : born.pin.binding = ⟨edPin, keyId⟩ := (congrArg (fun owner => owner.pin.binding) found).trans binding
        have identity := congrArg (fun pin : pqxdh.ServerBinding => pin.identity_public_key) bornPin
        have assigned := congrArg (fun pin : pqxdh.ServerBinding => pin.identity_key_id) bornPin
        simp only [roster, List.map_append, List.map_cons, List.map_nil, nativeKey, identity, assigned]
        rw [← restore_keys]
end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.pack_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.pack_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.restore_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.restore_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.bundle_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.bundle_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.create_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins.create_keys
