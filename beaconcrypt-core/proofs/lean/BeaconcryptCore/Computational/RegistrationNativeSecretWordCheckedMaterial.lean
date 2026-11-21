-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparation

/-! Actual material components run on the same current environment and chronological signing receipts. Evaluation changes the private demand address only; checked optional inputs, raw first-record programs, publication, encoding and all installation failures are preserved. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial
open RegistrationNativeSecretWordMessage (Message input)
open RegistrationNativeSecretWordChecked (Spec native implementation)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value Auxiliary : Type}

/-- Both concrete checked embeddings execute the same complete environment program. -/
theorem effects (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ (native (KemSK := KemSK) source inside candidate input)
      (simulateQ RegistrationBeaconReferenceCompiler.effect work) =
      simulateQ (implementation source inside candidate input)
        (simulateQ RegistrationNativeSecretWordInterface.effect work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

/-- Native raw/sign/common components retain every current environment field and actual callback effect. -/
theorem common (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Message → Option RegistrationNativeSecretWord.Key) (hkdf : FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    simulateQ (native (KemSK := KemSK) source inside candidate input)
      ((RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect hkdf wire.frameWrite sign query).run before) =
      simulateQ (implementation source inside candidate input)
        ((RegistrationNativeCommonCompiler.common RegistrationNativeSecretWordInterface.effect hkdf wire.frameWrite sign query).run before) := by
  conv_lhs => rw [RegistrationNativeCommonCompiler.common_map]
  conv_rhs => rw [RegistrationNativeCommonCompiler.common_map]
  exact effects source inside candidate input _

/-- The actual Server service commutes with evaluated demand addresses and the exact native common interpreter. -/
theorem server_query (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (hkdf : FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n).Domain) (before : Environment) :
    simulateQ (native (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
      ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
          RegistrationServerOpenReferenceCompiler.demand hkdf wire.frameWrite sign)
        (RegistrationNativeSecretWordServerMaterial.realize candidate query)).run before) =
      simulateQ (implementation source inside candidate (input joint dh seed scalar))
        ((RegistrationNativeSecretWordServerCompiler.service hkdf wire sign query).run before) := by
  cases query with
  | inl message =>
      simp only [RegistrationNativeSecretWordServerMaterial.realize, simulateQ_spec_query,
        RegistrationNativeCommonCompiler.service, RegistrationServerOpenReferenceCompiler.demand,
        RegistrationNativeSecretWordServerCompiler.service, StateT.run_lift, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, native, QueryImpl.compose,
        RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.demand,
        implementation]
      rw [RegistrationNativeSecretWordCheckedInput.material_literal_eval]
  | inr query =>
      simp only [RegistrationNativeSecretWordServerMaterial.realize, simulateQ_spec_query,
        RegistrationNativeCommonCompiler.service, RegistrationNativeSecretWordServerCompiler.service]
      exact common source inside candidate (input joint dh seed scalar) hkdf wire sign query before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial.effects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial.common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial.common
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial.server_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial.server_query
