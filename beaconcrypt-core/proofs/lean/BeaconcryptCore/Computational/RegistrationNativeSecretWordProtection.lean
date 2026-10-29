-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource

/-! Native protection reads the actual first DH coordinate inside the fixed160-byte head. It is independent of the opaque KEM word. This exact parsing fact supplies the concrete head predicate used by the symbolic service, while preserving the existing full-input protection rule unchanged. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
open RegistrationNativeSecretWord (Key)
open PqxdhKemIndCca (MlKemSharedSecret)
open PqxdhJointIdentity (DhOutput)

def inside (target : Option DhOutput) (head : RegistrationNativeSuffixKeyPrf.Prefix) : Bool :=
  decide (RegistrationNativeRelatedFamily.Protected target head.toList)

/-- Appending the final KEM field cannot alter the complete first DH coordinate. -/
theorem read_first (candidate : MlKemSharedSecret) (key : Key) :
    PqxdhJointGapDh.readDh 32 (RegistrationNativeSecretWord.eval candidate key) =
      PqxdhJointGapDh.readDh 32 key.head.toList := by
  have slice : ((RegistrationNativeSecretWord.eval candidate key).drop 32).take 32 =
      (key.head.toList.drop 32).take 32 := by
    simp [RegistrationNativeSecretWord.eval, List.drop_append, List.take_append]
  unfold PqxdhJointGapDh.readDh
  rw [slice]

/-- The concrete symbolic head classifier is exactly native protection on all literal192-byte evaluated inputs. -/
theorem inside_eval (target : Option DhOutput) (candidate : MlKemSharedSecret) (key : Key) :
    inside target key.head = RegistrationNativeKeyFamilyPreparation.inside target
      (RegistrationNativeSecretWord.eval candidate key) := by
  simp only [inside, RegistrationNativeKeyFamilyPreparation.inside,
    RegistrationNativeRelatedFamily.Protected, read_first]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection.read_first' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection.read_first
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection.inside_eval' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection.inside_eval
