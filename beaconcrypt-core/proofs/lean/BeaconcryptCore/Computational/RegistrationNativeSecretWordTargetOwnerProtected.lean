-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconRoot

/-! The selected owner's first DH coordinate is protected by its own actual converted Server pin. This conclusion does not equate the owner's identity or prekey with any accepted Server-session key. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWord (Key)
variable {ι KemSK : Type} {base : OracleSpec ι}

/-- The successful native public conversion of the selected Server identity is the same published converted X25519 point. -/
theorem converted_pin (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (server converted : PqxdhBeaconPhase2Preparation.Word32)
    (pin : absBytes server = (setup.joint.publicKeys seed).ed25519.toList)
    (source : setup.source.crypto.xpkConv (absBytes server) = some (absBytes converted)) :
    PqxdhPhase2GapDhSource.peer converted = (setup.joint.publicKeys seed).convertedX25519 := by
  have actual := PqxdhJointIdentity.jointPublic_conversion setup.source.crypto setup.joint setup.secretOfSeed setup.wiring seed
  rw [pin] at source
  have bytes := Option.some.inj (source.symm.trans actual)
  apply Subtype.ext
  exact bytes

/-- A successful symbolic owner root is protected using its own retained converted pin, independently of the linked session's classical fields. -/
theorem beacon_inside (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (pin : PqxdhPhase2GapDhSource.peer pending.collected.plain.serverConverted = (setup.joint.publicKeys seed).convertedX25519)
    (key : Key) (realized : RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
      (RegistrationNativeSecretWordBeaconRoot.message pending) = some key) :
    RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head = true := by
  have input := congrArg (Option.map (RegistrationNativeSecretWord.eval candidate)) realized
  rw [RegistrationNativeSecretWordMessage.input_eval] at input
  have protectedInput := RegistrationNativeProtectedInputs.beacon setup.joint setup.dh seed scalar
    (RegistrationNativeSecretWordMessage.eval candidate (RegistrationNativeSecretWordBeaconRoot.message pending))
    (PqxdhPhase2GapDhSource.peer pending.collected.plain.ephemeral) (RegistrationNativeSecretWord.eval candidate key) rfl pin input
  rw [RegistrationNativeSecretWordProtection.inside_eval]
  exact decide_eq_true protectedInput
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected.converted_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected.converted_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected.beacon_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected.beacon_inside
