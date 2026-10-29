-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconPreparation
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconMaterial

/-! The complete selected-owner finish combines actual terminal consumption, mandatory response authentication, checked root preparation and actual native first-record completion. All optional failures keep the same consumed owner, World effects and complete environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordChecked (native implementation)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

/-- Both complete controllers perform the same actual World abort and preserve the same local state. -/
theorem abort (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner before : SelectedOwner source) (env : EnvState Auxiliary) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationBeaconReferenceFinish.abort owner).run before).run env) =
      simulateQ (implementation (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (((RegistrationNativeSecretWordBeaconCompiler.abort owner).run before).run env) := by
  simp only [RegistrationBeaconReferenceFinish.abort, RegistrationNativeSecretWordBeaconCompiler.abort,
    StateT.run_lift, bind_pure_comp, StateT.run_map, simulateQ_map]
  rw [RegistrationNativeSecretWordChecked.effect_source]
  rfl

attribute [local irreducible] RegistrationBeaconReferenceCompiler.finishPreparation
  RegistrationNativeSecretWordBeaconCompiler.finishPreparation RegistrationBeaconReferenceFinish.complete
  RegistrationNativeSecretWordBeaconCompiler.complete RegistrationBeaconReferenceFinish.abort
  RegistrationNativeSecretWordBeaconCompiler.abort native implementation

/-- The entire selected incoming controller has the exact actual source after interpreting its opaque word. -/
theorem finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary) :
    simulateQ (native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run env) =
      simulateQ (implementation (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
        (((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner).run env) := by
  simp only [RegistrationBeaconReferenceFinish.finish, RegistrationNativeSecretWordBeaconCompiler.finish,
    StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted control => rfl
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div =>
        simp only [moved, StateT.run_pure, simulateQ_pure]
    | ok aborted =>
      simp only [moved, StateT.run_bind, simulateQ_bind]
      rw [RegistrationNativeSecretWordCheckedBeaconPreparation.preparation setup source inside candidate seed scalar packet owner env,
        bind_map_left]
      apply bind_congr
      intro reached
      cases accepted : reached.1.1 with
      | fail error | div =>
          simp only [RegistrationNativeSecretWordBeaconRoot.restore, seqRight_eq_bind, StateT.run_bind,
            StateT.run_pure, simulateQ_bind, simulateQ_pure]
          rw [abort setup inside candidate seed scalar owner reached.1.2 reached.2]
      | ok ready =>
          cases ready with
          | none =>
              simp only [RegistrationNativeSecretWordBeaconRoot.restore, Option.map_none, seqRight_eq_bind,
                StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
              rw [abort setup inside candidate seed scalar owner reached.1.2 reached.2]
          | some ready =>
              simp only [RegistrationNativeSecretWordBeaconRoot.restore, Option.map_some]
              exact RegistrationNativeSecretWordCheckedBeaconMaterial.complete setup.source inside candidate
                setup.joint setup.dh seed scalar setup.source owner reached.1.2 ready reached.2
end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish.abort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish.abort
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconFinish.finish
