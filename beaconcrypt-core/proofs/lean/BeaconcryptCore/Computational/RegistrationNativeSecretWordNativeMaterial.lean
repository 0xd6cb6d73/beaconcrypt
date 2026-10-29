-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection

/-! The actual native full-byte material operation agrees with the symbolic source at every evaluated key. Protection reads only its original first-DH coordinate. The literal native input equation also retains every failed optional DH computation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeKeyCompiler (KeySpec)

def material (source : FixedHkdfSha512NoSaltSource) (inside : Pqxdh.Bytes → Bool) (bytes : Pqxdh.Bytes) :
    OracleComp KeySpec PqxdhServerAuthKeySchedule.Output :=
  if inside bytes then KeySpec.query (.inr bytes)
  else pure (PqxdhServerAuthKeySchedule.fromRoot source (RegistrationNativeRelatedRoot.nativeRoot source bytes))

/-- Each evaluated symbolic material branch is exactly the native full-byte table or original known schedule branch. -/
theorem material_source (source : FixedHkdfSha512NoSaltSource) (target : Option PqxdhJointIdentity.DhOutput)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (key : Key) :
    RegistrationNativeSecretWordServiceSource.nativeMaterial source (RegistrationNativeSecretWordProtection.inside target) candidate key =
      material source (RegistrationNativeKeyFamilyPreparation.inside target) (RegistrationNativeSecretWord.eval candidate key) := by
  cases protectedInput : RegistrationNativeSecretWordProtection.inside target key.head with
  | false =>
      rw [RegistrationNativeSecretWordServiceSource.native_known source _ candidate key protectedInput]
      simp only [material, ← RegistrationNativeSecretWordProtection.inside_eval, protectedInput, Bool.false_eq_true, ite_false]
  | true =>
      rw [RegistrationNativeSecretWordServiceSource.native_protected source _ candidate key protectedInput]
      simp only [material, ← RegistrationNativeSecretWordProtection.inside_eval, protectedInput, ite_true]

/-- Literal native descriptors recover precisely the original optional full-byte input. -/
theorem input_literal (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (message : RegistrationNativeRelatedFamily.Message) :
    (RegistrationNativeSecretWordMessage.input joint dh seed scalar (RegistrationNativeSecretWordMessage.literal message)).map
      (RegistrationNativeSecretWord.eval candidate) = RegistrationNativeRelatedFamily.input joint dh seed scalar message := by
  simpa only [RegistrationNativeSecretWordMessage.eval_literal] using
    RegistrationNativeSecretWordMessage.input_eval joint dh seed scalar candidate (RegistrationNativeSecretWordMessage.literal message)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial.material_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial.material_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial.input_literal' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordNativeMaterial.input_literal
