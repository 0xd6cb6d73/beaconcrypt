-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceWrapper

/-! The literal-source known-material continuation is the existing native source108 opening/install controller under the same concrete trusted callbacks. This equation is independent of how a fresh root was named and retains the complete private state and current mutable environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect trustedLift)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceCompletion (sourceComplete)
variable {ι KemSK Value Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem after_lift (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (result : RustM RegistrationNativePairedBeaconService.Result) :
    simulateQ (RegistrationBeaconReferenceNativeRecord.environment (KemSK := KemSK))
      (((RegistrationBeaconReferenceCompletion.after (QueryImpl.id' (EnvEffects n)) owner result :
        RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) =
      (((RegistrationBeaconReferenceCompletion.after RegistrationBeaconReferenceNativeRecord.environment owner result :
        RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
          (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) := by
  cases result with
  | fail error | div =>
      simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
        seqRight_eq_bind, StateT.run_map, StateT.run_lift, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, QueryImpl.id'_apply]
  | ok result => cases result with
    | Err error =>
        simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
          seqRight_eq_bind, StateT.run_map, StateT.run_lift, bind_pure_comp,
          simulateQ_map, simulateQ_spec_query, QueryImpl.id'_apply]
    | Ok completed =>
        simp only [RegistrationBeaconReferenceCompletion.after, StateT.run_bind,
          StateT.run_modify, pure_bind, StateT.run_pure, simulateQ_pure]

/-- The whole concrete completion AST is the existing native no-sign source controller, including its exact installation and owner phase. -/
theorem source_complete_lift (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput) :
    simulateQ (RegistrationBeaconReferenceNativeRecord.environment (KemSK := KemSK))
      (((sourceComplete setup.source wire.frameWrite owner ready root :
        RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) =
      (((RegistrationBeaconReferenceNativeKnown.factored setup wire owner ready.descriptor root :
        RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
          (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) := by
  simp only [sourceComplete, RegistrationBeaconReferenceNativeCompletion.knownEffects,
    RegistrationBeaconReferenceNativeKnown.factored, RegistrationBeaconReferenceNativeKnown.after,
    StateT.run_bind, StateT.run_lift, bind_pure_comp, simulateQ_bind, bind_map_left, bind_assoc]
  apply bind_congr
  intro result
  apply bind_congr
  intro completed
  exact after_lift owner current env completed

noncomputable def trusted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT (Private n KemSK) ProbComp) :=
  implementation setup wire route sign seed scalar ∘ₛ trustedLift

/-- The actual prepared-root continuation agrees with the native controller under the same literal callbacks, with every private coordinate retained. -/
theorem complete_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (owner current : SelectedOwner mlSource)
    (env : EnvState Auxiliary) (ready : RegistrationBeaconReferenceRoot.Ready)
    (root : PqxdhSecretInputKdf.RootOutput) (before : Private n KemSK)
    (prepared : before.extra.1 ready.reference = some root) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (trusted setup wire route sign seed scalar)
        (((RegistrationBeaconReferenceNativeKnown.factored setup wire owner ready.descriptor root :
          RegistrationBeaconReferenceCompletion.M (target := RegistrationNativeBeaconFrontend.Trusted n KemSK)
            (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  rw [RegistrationNativeOrdinaryFinishSourceCompletion.complete_known setup wire route sign seed scalar owner current env ready root before prepared,
    ← source_complete_lift setup wire owner current env ready root]
  simp only [trusted, QueryImpl.simulateQ_compose]
  have lifted : trustedLift (n := n) (KemSK := KemSK) ∘ₛ RegistrationBeaconReferenceNativeRecord.environment = effect := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, trustedLift]
  rw [← QueryImpl.simulateQ_compose trustedLift, lifted]
  exact (RegistrationNativeOrdinaryFinishSourceCompletion.effects_program setup wire route sign seed scalar _ before).symm

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative.source_complete_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative.source_complete_lift
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative.complete_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceNative.complete_native
