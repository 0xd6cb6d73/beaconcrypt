-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle

/-! Successful symbolic bundle publication retains the actual original owner's signed PQ payload. This proof descends through the literal realization and native outgoing controller, so it is independent of later random material choices. Packing a selected scalar changes no retained KEM handle or public key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicOwners (Owner State)
open RegistrationNativeKemBirthInvariant (metadata)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def key (owner : Owner source) : Nat × PqxdhKemIndCca.MlKem768PublicKey :=
  (owner.view.kemHandle, owner.view.kemPublic)

/-- Public selected-scalar packing preserves all retained private-handle and public-key metadata. -/
theorem pack_keys (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) :
    (RegistrationNativePublicOwners.pack selected publicPrekey owners).map key = owners.map metadata := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, RegistrationNativePublicOwners.pack, List.getElem?_mapIdx]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      by_cases chosen : index = selected <;>
        simp only [Option.map_some, chosen, ite_true, ite_false, key, metadata,
          RegistrationBeaconReferenceCompiler.eraseOwner]

/-- Restoring any ordinary scalar leaves exactly the same handle and PQ bytes at every roster position. -/
theorem restore_keys (owners : State source) :
    (owners.map RegistrationNativePublicOwners.restore).map metadata = owners.map key := by
  simp only [List.map_map]
  rfl

/-- Actual symbolic outgoing publication has the original retained owner's decoded signed PQ payload. -/
theorem bundle_key (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (readback : RegistrationNativeWire.InitReadBack wire) (selected index : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (owners : State source) (env : EnvState Auxiliary)
    (raw : Pqxdh.Bytes) (afterOwners : State source) (afterEnv : EnvState Auxiliary)
    (supported : ((.ok (some raw), afterOwners), afterEnv) ∈ support
      (((RegistrationNativeSecretWordOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env)) :
    ∃ owner packet, owners[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      RegistrationNativeKemTarget.PacketKey packet owner.view.kemPublic := by
  simp only [RegistrationNativeSecretWordOwners.bundle, RegistrationNativeSecretWordOwners.executeLocal,
    StateT.run] at supported
  have pubSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePublicOwners.executeLocal,
    StateT.run, support_map] at pubSupport
  obtain ⟨⟨⟨reply, reachedOwners⟩, reachedEnv⟩, reached, equal⟩ := pubSupport
  have replyEq : reply = .ok (some raw) := congrArg (fun result => result.1.1) equal
  subst reply
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  obtain ⟨restored, published, found, encoded, receipt⟩ := RegistrationNativeBeaconPublication.bundle_key
    setup source wire index (owners.map RegistrationNativePublicOwners.restore) reachedOwners env reachedEnv raw native
  simp only [List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨owner, ownerAt, restoredEq⟩ := found
  subst restored
  obtain ⟨packet, decoded, keyMatches⟩ := RegistrationNativeKemPublication.decoded_key wire readback
    (RegistrationNativePublicOwners.restore owner).kemPublic published receipt
  exact ⟨owner, packet, ownerAt, encoded ▸ decoded, keyMatches⟩

/-- Actual symbolic bundles preserve every owner's retained handle and PQ bytes on all writer/signing failures. -/
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
  simp only [RegistrationNativePublicOwners.executeLocal,
    StateT.run, support_map] at pubSupport
  obtain ⟨reached, called, equal⟩ := pubSupport
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have kept := RegistrationNativeKemBirthLifecycle.bundle_metadata setup source wire index
    (owners.map RegistrationNativePublicOwners.restore) env reached native
  cases equal
  rw [pack_keys, kept, restore_keys]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.pack_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.pack_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.restore_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.restore_keys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.bundle_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.bundle_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.bundle_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication.bundle_keys
