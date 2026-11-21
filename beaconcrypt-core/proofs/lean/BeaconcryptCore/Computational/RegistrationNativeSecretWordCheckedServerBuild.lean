-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial

/-! The actual one-use Server build and every publication callback restore exactly through checked material interpretation. The source equation retains the complete current environment and all remaining sessions; cancellation and every later failure are included. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild
open RegistrationNativeSecretWordMessage (Message input ServerState)
open RegistrationNativeSecretWordChecked (Spec native implementation)
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value : Type}

/-- Every adaptive material component runs in the same current chronological environment. -/
theorem material_program (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (hkdf : FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value) (before : Environment) :
    simulateQ (native (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
      ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
          RegistrationServerOpenReferenceCompiler.demand hkdf wire.frameWrite sign)
        (simulateQ (RegistrationNativeSecretWordServerMaterial.realize candidate) work)).run before) =
      simulateQ (implementation source inside candidate (input joint dh seed scalar))
        ((simulateQ (RegistrationNativeSecretWordServerCompiler.service hkdf wire sign) work).run before) := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, QueryImpl.simulateQ_mapStateTBase_run,
    ← QueryImpl.simulateQ_compose]
  congr 2
  funext query current
  change (simulateQ
      ((native source inside candidate (input joint dh seed scalar)).mapStateTBase
        (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
          RegistrationServerOpenReferenceCompiler.demand hkdf wire.frameWrite sign))
      (RegistrationNativeSecretWordServerMaterial.realize candidate query)).run current =
    simulateQ (implementation source inside candidate (input joint dh seed scalar))
      ((RegistrationNativeSecretWordServerCompiler.service hkdf wire sign query).run current)
  rw [← QueryImpl.simulateQ_mapStateTBase_run]
  exact RegistrationNativeSecretWordCheckedMaterial.server_query source inside candidate joint dh seed scalar hkdf wire sign query current

/-- Complete actual build equality includes the consumed handle, failure poststate, raw record, ML signing and dynamic publication. -/
theorem build (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (hkdf : FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire) (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (before : ServerState) (env : Environment) :
    simulateQ (native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
      (((RegistrationServerOpenReferenceCompiler.build hkdf wire checks sign handle application).run (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        simulateQ (implementation source inside candidate (input joint dh seed scalar))
          (((RegistrationNativeSecretWordServerCompiler.build hkdf wire checks sign handle application).run before).run env) := by
  have actual := congrArg (fun work =>
      simulateQ (native (n := n) (KemSK := KemSK) source inside candidate (input joint dh seed scalar))
        ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
          RegistrationServerOpenReferenceCompiler.demand hkdf wire.frameWrite sign) work).run env))
    (RegistrationNativeSecretWordServerMaterial.build_source candidate wire checks.reservePeer handle application before)
  rw [simulateQ_map, StateT.run_map, simulateQ_map,
    material_program source inside candidate joint dh seed scalar hkdf wire sign] at actual
  exact actual.symm

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild.material_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild.material_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerBuild.build
