-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition
import BeaconcryptCore.Computational.PqxdhServerAuthExperiment

/-! Existing primitive signature correctness and the actual source wiring discharge recognition at a genuine source signature. This uses only the Ed functional fields of the supplied setup, and introduces no native-origin or hash-privacy assumption. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource
variable {I KemSK : Type} {base : OracleSpec I}

/-- The ordinary joint signature is valid under its own exposed public key by the existing source/primitive functional contracts. -/
theorem sign_correct (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (message : Pqxdh.Bytes) :
    setup.joint.verify (setup.joint.publicKeys seed).ed25519 message (setup.joint.sign seed message) = true := by
  have correct := setup.source.crypto.verify_sign (setup.secretOfSeed seed).toList message
  rw [← setup.wiring.edPublic, ← setup.wiring.attachedSign, setup.wiring.verifyAttached] at correct
  cases verified : setup.joint.verify (setup.joint.publicKeys seed).ed25519 message (setup.joint.sign seed message) with
  | true => rfl
  | false => simp only [verified, Bool.false_eq_true, ite_false, reduceCtorEq] at correct

/-- A hash address containing the actual source signature is recognized without any source signature-uniqueness premise. -/
theorem template (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (message leading trailing : Pqxdh.Bytes) :
    (RegistrationNativeIdentityRecognition.recognize setup.joint.verify (setup.joint.publicKeys seed).ed25519 message
      (leading ++ (setup.joint.sign seed message).toList ++ trailing)).isSome = true :=
  RegistrationNativeIdentityRecognition.template_recognized _ _ _ _ _ _ (sign_correct setup seed message)

end BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource.sign_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource.sign_correct
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource.template' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionSource.template
