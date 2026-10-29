-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconRootSource
import BeaconcryptCore.Computational.RegistrationNativeRootInputAliases

/-! Protection follows the actual first DH coordinate of a realized input. Server requests use their authenticated prekey operand; selected Beacon requests use their own selected scalar and retained converted Server pin. The Beacon statement does not identify its root with any designated Server session or require that session's identity/prekey to match the owner. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeProtectedInputs
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeRelatedFamily (Message Third input Protected)

/-- A successful Server descriptor whose actual static operand is the selected public prekey belongs to the protected literal-input slice. -/
theorem server (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (third : DhOutput) (bytes : Pqxdh.Bytes)
    (kind : message.third = .known third) (peer : message.staticPeer = dh.publicKey scalar)
    (realized : input joint dh seed scalar message = some bytes) :
    Protected (joint.staticDh seed (dh.publicKey scalar)) bytes := by
  apply (RegistrationNativeRelatedFamily.input_protected_iff joint dh seed scalar message bytes realized).mpr
  simp only [RegistrationNativeRelatedFamily.firstValue, kind, peer]

/-- The selected owner's own successful pinned descriptor is protected by its retained Server pin, independently of all other session identities and root coordinates. -/
theorem beacon (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (message : Message) (ephemeral : PeerEncoding) (bytes : Pqxdh.Bytes)
    (kind : message.third = .pinned ephemeral)
    (pin : message.staticPeer = (joint.publicKeys seed).convertedX25519)
    (realized : input joint dh seed scalar message = some bytes) :
    Protected (joint.staticDh seed (dh.publicKey scalar)) bytes := by
  apply (RegistrationNativeRelatedFamily.input_protected_iff joint dh seed scalar message bytes realized).mpr
  simp only [RegistrationNativeRelatedFamily.firstValue, kind, pin]
  exact (dh.agreement seed scalar).symm

/-- Actual native selected-owner input construction preserves this protection when the collected public conversion is the retained selected Server pin. No accepted-packet identity equality is required. -/
theorem beacon_source {joint : Primitives} (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    {Response : Type} (collected : PqxdhPhase2GapDhSource.Inputs Response)
    (references : PqxdhPhase2GapDhSource.References domain collected)
    (pin : PqxdhPhase2GapDhSource.peer collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input
      (PqxdhPhase2GapDhSource.concreteInputs dh scalar collected).finishInputs.shared_secrets = .ok (.Ok root)) :
    Protected (joint.staticDh seed (dh.publicKey scalar)) (absBytes root.bytes) :=
  beacon joint dh seed scalar (RegistrationNativeRelatedRoot.pinnedBeaconMessage collected)
    (PqxdhPhase2GapDhSource.peer collected.ephemeral) (absBytes root.bytes) rfl pin
    (RegistrationNativeBeaconRootSource.pinned_source dh domain seed scalar collected references root built)

end BeaconcryptCore.Computational.RegistrationNativeProtectedInputs

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProtectedInputs.server' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProtectedInputs.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProtectedInputs.beacon' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProtectedInputs.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProtectedInputs.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProtectedInputs.beacon_source
