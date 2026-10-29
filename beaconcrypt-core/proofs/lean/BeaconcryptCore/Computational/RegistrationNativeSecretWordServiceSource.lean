-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordService
import BeaconcryptCore.Computational.RegistrationNativeG3KeyService

/-! The alias service restores the actual direct G2 material computation under the real suffix-key interpretation. This is an exact open-program statement before any probabilistic alias or PRF estimate. The evaluated key table keeps literal192-byte addresses, and off-protected literals and atoms both recover the actual complete native schedule. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined material)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationNativeKeyCompiler (KeySpec)
open PqxdhKemIndCca (MlKemSharedSecret)
attribute [local irreducible] RegistrationNativeSuffixKeyPrf.value PqxdhServerAuthKeySchedule.fromRoot

def realize (source : FixedHkdfSha512NoSaltSource) (candidate : MlKemSharedSecret) :
    QueryImpl Combined (OracleComp KeySpec)
  | .inl (.inl coin) => KeySpec.query (.inl coin)
  | .inl (.inr key) => KeySpec.query (.inr (RegistrationNativeSecretWord.eval candidate key))
  | .inr head => pure (RegistrationNativeSuffixKeyPrf.value source candidate head)

def nativeMaterial (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret) (key : Key) :
    OracleComp KeySpec PqxdhServerAuthKeySchedule.Output :=
  if inside key.head then KeySpec.query (.inr (RegistrationNativeSecretWord.eval candidate key))
  else pure (RegistrationNativeSuffixKeyPrf.value source (key.word.eval candidate) key.head)

/-- Interpreting the symbolic table at evaluated bytes and the additional oracle at its real secret restores every actual material branch. -/
theorem material_source (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret) (key : Key) :
    simulateQ (realize source candidate) (material source inside key) = nativeMaterial source inside candidate key := by
  cases protectedInput : inside key.head with
  | true => simp only [material, nativeMaterial, protectedInput, ite_true, simulateQ_spec_query, realize]
  | false =>
      cases word : key.word <;>
        simp only [material, nativeMaterial, protectedInput, Bool.false_eq_true, ite_false, word,
          Word.eval, simulateQ_pure, simulateQ_spec_query, realize]

/-- A protected material operation is the same original full-byte key-table query after evaluation of the opaque word. -/
theorem native_protected (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret) (key : Key)
    (protectedInput : inside key.head = true) :
    nativeMaterial source inside candidate key = KeySpec.query (.inr (RegistrationNativeSecretWord.eval candidate key)) := by
  simp only [nativeMaterial, protectedInput, ite_true]

/-- Off-protected evaluation is literally the real root and complete108-byte source schedule on that192-byte input. -/
theorem native_known (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret) (key : Key)
    (outside : inside key.head = false) :
    nativeMaterial source inside candidate key = pure (PqxdhServerAuthKeySchedule.fromRoot source
      (RegistrationNativeRelatedRoot.nativeRoot source (RegistrationNativeSecretWord.eval candidate key))) := by
  simp only [nativeMaterial, outside, Bool.false_eq_true, ite_false]
  simp only [RegistrationNativeSuffixKeyPrf.value, RegistrationNativeSuffixKeyPrf.input, RegistrationNativeSecretWord.eval]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource.material_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource.material_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource.native_protected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource.native_protected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceSource.native_known
