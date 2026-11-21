-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryAgreement
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial

/-! The actual Beacon consumes InitSent before optional packet admission, runs the real response authentication and only then prepares its checked private root reference. This source equation includes malformed optional packets, native errors and every reached owner/environment field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryPreparation
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativeSecretWordCheckedOrdinary (original symbolic)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationBeaconReferenceCompiler.agreement
  RegistrationNativeSecretWordBeaconCompiler.agreement original symbolic
  RegistrationResponseExecutor.begin RegistrationAuthenticationCompiler.callbacks

/-- Complete actual response preparation retains terminal-before-parse behavior and the entire reached source state. -/
theorem preparation (setup : Setup base KemSK) (localScalar : ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (env : EnvState Auxiliary) :
    simulateQ (original (n := n) setup localScalar inside candidate seed scalar)
      (((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner).run env) =
      (fun result => ((RegistrationNativeSecretWordBeaconRoot.restore candidate result.1.1, result.1.2), result.2)) <$>
        simulateQ (symbolic setup localScalar inside candidate seed scalar)
          (((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner).run env) := by
  simp only [RegistrationBeaconReferenceCompiler.finishPreparation,
    RegistrationNativeSecretWordBeaconCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted control => rfl
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div =>
        simp only [moved, StateT.run_pure, simulateQ_pure, map_pure]
        rfl
    | ok aborted =>
      simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_pure_comp,
        simulateQ_bind, bind_map_left, map_bind]
      rw [RegistrationNativeSecretWordCheckedOrdinary.effects setup localScalar inside seed scalar candidate]
      apply bind_congr
      intro checked
      cases checked with
      | fail error | div => simp only [StateT.run_pure, simulateQ_pure, map_pure, RegistrationNativeSecretWordBeaconRoot.restore]
      | ok checked =>
          cases checked with
          | Err error => simp only [StateT.run_pure, simulateQ_pure, map_pure, RegistrationNativeSecretWordBeaconRoot.restore, Option.map_none]
          | Ok authenticated =>
              simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, simulateQ_map, Functor.map_map]
              rw [RegistrationNativeSecretWordCheckedOrdinaryAgreement.agreement setup localScalar inside candidate seed scalar owner oneTime authenticated env]
              simp only [Functor.map_map, Prod.map, id_eq]
end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryPreparation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryPreparation.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryPreparation.preparation
