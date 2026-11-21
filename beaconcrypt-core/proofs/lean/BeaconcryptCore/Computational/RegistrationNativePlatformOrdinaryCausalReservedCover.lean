-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRegistrationMarkCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReservedOwners
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover
open RegistrationNativeRawRegistrationJournal (Mark)
open RegistrationNativePlatformIdentityCtxMain (Full)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned native)
variable {n count : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}

def identities (joint : PqxdhJointIdentity.Primitives) (before : Full n KemSK Platform source) :
    List PqxdhEd25519EufCma.Ed25519PublicKey :=
  (native before).1.beacons.map fun owner => (joint.publicKeys owner.identitySeed).ed25519

/-- Original strict-prior causal failure under any final owner identifies a finite reserved alias, including repeated public keys and aliases created after the relevant accept. -/
theorem at_reserved (joint : PqxdhJointIdentity.Primitives) (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed) (router : PqxdhDynamicIdentityRouting.PublicState)
    (capacity : router.created ≤ count) (before : Full n KemSK Platform source) (owned : Owned joint before)
    (pool : before.2.1 = PqxdhDynamicIdentityRouting.sourceState seeds router) (entries : List Mark)
    (failed : RegistrationNativeRegistrationMarkCausal.At crypto wire (identities joint before) entries) :
    ∃ index : Fin count, ∃ prior packet session decoded owner,
      entries = prior ++ [.accept packet (some session)] ∧
      PqxdhDeploymentTranscript.acceptedKeys crypto (RegistrationRootInput.candidate packet) =
        some ((joint.publicKeys (seeds index)).ed25519, decoded) ∧
      RegistrationNativeRegistrationMarkCausal.published wire prior owner ≠ some decoded := by
  obtain ⟨prior, packet, session, identity, decoded, owner, split, accepted, found, unpublished⟩ := failed
  obtain ⟨index, matching⟩ := RegistrationNativePlatformIdentityCtxReservedOwners.native_key
    joint seeds router capacity before owned pool owner identity found
  exact ⟨index, prior, packet, session, decoded, owner, split, by simpa only [matching] using accepted, unpublished⟩

/-- The reserved alias is selected from the final same-run roster while the acceptance and publication evidence remain at their original earlier prefix. -/
theorem historical_reserved (joint : PqxdhJointIdentity.Primitives) (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed) (router : PqxdhDynamicIdentityRouting.PublicState)
    (capacity : router.created ≤ count) (before : Full n KemSK Platform source) (owned : Owned joint before)
    (pool : before.2.1 = PqxdhDynamicIdentityRouting.sourceState seeds router) (entries : List Mark)
    (failed : RegistrationNativeRegistrationMarkCausal.Historical crypto wire (identities joint before) entries) :
    ∃ index : Fin count, ∃ prior later packet session decoded owner,
      entries = prior ++ .accept packet (some session) :: later ∧
      PqxdhDeploymentTranscript.acceptedKeys crypto (RegistrationRootInput.candidate packet) =
        some ((joint.publicKeys (seeds index)).ed25519, decoded) ∧
      RegistrationNativeRegistrationMarkCausal.published wire prior owner ≠ some decoded := by
  obtain ⟨earlier, later, split, failed⟩ := failed
  obtain ⟨index, prior, packet, session, decoded, owner, earlierEq, accepted, unpublished⟩ :=
    at_reserved joint crypto wire seeds router capacity before owned pool earlier failed
  refine ⟨index, prior, later, packet, session, decoded, owner, ?_, accepted, unpublished⟩
  rw [split, earlierEq, List.append_assoc]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover.at_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover.at_reserved
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover.historical_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryCausalReservedCover.historical_reserved
