-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerCollectedOperands
import BeaconcryptCore.Computational.RegistrationNativeBeaconDhReplies

/-! The native DH source laws identify honest public conversions and equate the actual optional scalar DH replies. These are primitive functional equations, without a protocol-root equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDhAgreement
open PqxdhServerAuthExperiment (Setup)
open PqxdhRootTableInitialization (rootArray)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- The typed public-key conversion of an actual source identity is its same correlated X25519 public value. -/
theorem converted (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (convertedKey : PqxdhBeaconPhase2Preparation.Word32)
    (accepted : RegistrationPublicConversion.convert setup.source.crypto (rootArray (setup.joint.publicKeys seed).ed25519) = .Some convertedKey) :
    PqxdhPhase2GapDhSource.peer convertedKey = (setup.joint.publicKeys seed).convertedX25519 := by
  have supplied := RegistrationPublicConversion.convert_sound setup.source.crypto _ _ accepted
  have honest := PqxdhJointIdentity.jointPublic_conversion setup.source.crypto setup.joint setup.secretOfSeed setup.wiring seed
  rw [PqxdhRootTableInitialization.rootArray_bytes, honest] at supplied
  apply List.Vector.toList_injective
  exact (Option.some.inj supplied).symm

/-- X25519 source commutation equates the complete optional replies, including rejection of zero output. -/
theorem scalar_comm (setup : Setup base KemSK) (left right : PqxdhJointGapDh.ScalarBytes) :
    setup.dh.dh left (setup.dh.publicKey right) = setup.dh.dh right (setup.dh.publicKey left) := by
  change PqxdhJointGapDh.sourceScalarDh setup.source.crypto left
      ⟨setup.source.crypto.xpub right.toList, setup.source.crypto.xpub_length _⟩ =
    PqxdhJointGapDh.sourceScalarDh setup.source.crypto right
      ⟨setup.source.crypto.xpub left.toList, setup.source.crypto.xpub_length _⟩
  simp only [PqxdhJointGapDh.sourceScalarDh, List.Vector.toList_mk,
    setup.source.crypto.dh_comm left.toList right.toList]

end BeaconcryptCore.Computational.RegistrationNativeDhAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDhAgreement.converted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDhAgreement.converted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDhAgreement.scalar_comm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDhAgreement.scalar_comm
