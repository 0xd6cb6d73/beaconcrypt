-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedPreparationProgram

/-! The actual arbitrary-pin Beacon collection and checked preparation compose on the same complete environment. Its opaque word remains confined to the private root reference; binding, ciphertext, application and all optional admission outcomes retain their native source behavior. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordChecked (native implementation)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

/-- The original concrete indexed Beacon collector is restored with its entire reached environment. -/
theorem collect (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner : SelectedOwner source) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run before) =
      Prod.map (Option.map (RegistrationNativeSecretWordBeaconPrepare.eval candidate)) id <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated).run before) := by
  unfold native
  rw [QueryImpl.simulateQ_compose, RegistrationNativeSecretWordBeaconSource.collector_source, simulateQ_map]

attribute [local irreducible] RegistrationBeaconReferenceCompiler.collect
  RegistrationNativeSecretWordBeaconCompiler.collect RegistrationBeaconReferenceRoot.client
  RegistrationNativeSecretWordBeaconRoot.client native implementation

/-- Actual arbitrary-pin agreement preserves the full local state and all checked optional root failures. -/
theorem agreement (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner : SelectedOwner source) (oneTime : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run before) =
      Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) id <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated).run before) := by
  simp only [RegistrationBeaconReferenceCompiler.agreement, RegistrationNativeSecretWordBeaconCompiler.agreement,
    StateT.run_bind, simulateQ_bind, map_bind]
  rw [collect setup inside candidate seed scalar owner oneTime authenticated before, bind_map_left]
  apply bind_congr
  intro reached
  cases selected : reached.1 with
  | none =>
      simp only [Prod.map, selected, Option.map_none, StateT.run_pure, simulateQ_pure, map_pure,
        RegistrationNativeSecretWordBeaconRoot.restore]
  | some pending =>
      simp only [Prod.map, selected, Option.map_some, StateT.run_lift, bind_pure_comp, simulateQ_map,
        Functor.map_map]
      rw [RegistrationNativeSecretWordCheckedPreparationProgram.beacon setup.source inside candidate
        setup.joint setup.dh seed scalar authenticated pending]
      simp only [Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement.collect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement.agreement
