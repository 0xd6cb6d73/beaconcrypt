-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal

/-! The native changed-prekey event reads successful original native accept entries and the final actual generated owner roster. It deliberately includes later-created public-key aliases. Public opaque credentials and their private source realization define the same event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginEvents
variable {n : Nat} {KemSK Value : Type} {source : RegistrationNativeMldsa.Source}

def Changed (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (transcript : List RegistrationNativeInterface.Entry) (owners : RegistrationNativeBeaconFrontend.State source) : Prop :=
  ∃ packet ∈ RegistrationNativeIdentityFinalReports.packets wire transcript, ∃ owner ∈ owners,
    ∃ decoded : PqxdhEd25519EufCma.Phase1KeyTuple,
      PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify (RegistrationRootInput.candidate packet) =
        some ((joint.publicKeys owner.identitySeed).ed25519, decoded) ∧
      decoded.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic

open Classical in
noncomputable def event (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) : Bool :=
  decide (Changed joint wire observed.2.1.transcript observed.2.2.beacons)

theorem realized (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (transcript : List RegistrationNativeInterface.Entry) (pool : PqxdhDynamicIdentityPool.SourceState)
    (owners : RegistrationNativeIdentityFrontend.State source) (owned : RegistrationNativeIdentityRealization.Owned joint pool owners) :
    Changed joint wire transcript (RegistrationNativeIdentityRealization.owners pool owners) ↔
      RegistrationNativeIdentityOriginFinal.Changed joint wire transcript owners := by
  have identity : ∀ owner ∈ owners,
      joint.publicKeys (RegistrationNativeIdentityRealization.owner pool owner).identitySeed = owner.identity.publicIdentity := by
    intro owner member
    obtain ⟨seed, stored⟩ := owned owner member
    change joint.publicKeys (RegistrationNativeIdentityRealization.seedFor pool owner.identity) = owner.identity.publicIdentity
    rw [RegistrationNativeIdentityRealization.seed_found pool owner.identity seed stored.1]
    exact stored.2.symm
  constructor
  · rintro ⟨packet, packetPresent, selected, member, decoded, accepted, different⟩
    obtain ⟨owner, present, rfl⟩ := List.mem_map.mp member
    rw [identity owner present] at accepted
    exact ⟨packet, packetPresent, owner, present, decoded, accepted, different⟩
  · rintro ⟨packet, packetPresent, owner, present, decoded, accepted, different⟩
    refine ⟨packet, packetPresent, RegistrationNativeIdentityRealization.owner pool owner,
      List.mem_map.mpr ⟨owner, present, rfl⟩, decoded, ?_, different⟩
    rw [identity owner present]
    exact accepted

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginEvents.realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginEvents.realized
