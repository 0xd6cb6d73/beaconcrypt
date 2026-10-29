-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceFrame
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation

/-! The complete post-agreement native owner continuation uses the actual returned memo cell. It retains failures and aborts and the native consumed-kernel opening/install controller. The source projection names only the existing owner-scalar and record-request analysis views; no memo equality or target-pin condition is imposed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec effect trustedLift)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeOrdinaryFinishSourceNative (trusted)
open RegistrationBeaconReferenceNativeContinuation (view sourceAfter afterPrepared)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {ι KemSK Value Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem environment_lift : trustedLift (n := n) (KemSK := KemSK) ∘ₛ
    RegistrationBeaconReferenceNativeRecord.environment = effect := by
  funext query
  simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
    simulateQ_spec_query, trustedLift]

private theorem abort_projection (owner current : RegistrationNativeBeaconFrontend.Owner mlSource)
    (env : EnvState Auxiliary) (value : Value) :
    view <$>
      (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
        RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource Value).run current).run env) =
      simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (((RegistrationBeaconReferenceCompletion.abort (QueryImpl.id' (EnvEffects n)) (eraseOwner owner) *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
            mlSource Value).run (eraseOwner current)).run (RegistrationBeaconReferenceNativeRecord.erase env)) := by
  simp only [RegistrationBeaconReferenceNativeOwner.abort, RegistrationBeaconReferenceCompletion.abort,
    seqRight_eq_bind, StateT.run_lift, bind_pure_comp, StateT.run_map,
    RegistrationBeaconReferenceNativeRecord.environment, simulateQ_map, simulateQ_spec_query,
    QueryImpl.id'_apply, Functor.map_map, view]
  rfl

private theorem public_abort (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary) (value : Value) :
    (((RegistrationBeaconReferenceFinish.abort owner *> pure value :
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
        mlSource Value).run current).run env) =
      simulateQ effect
        (((RegistrationBeaconReferenceCompletion.abort (QueryImpl.id' (EnvEffects n)) owner *> pure value :
          RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
            mlSource Value).run current).run env) := by
  simp only [RegistrationBeaconReferenceFinish.abort, RegistrationBeaconReferenceCompletion.abort,
    seqRight_eq_bind, StateT.run_map, StateT.run_lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, QueryImpl.id'_apply]

/-- Public and native terminal aborts preserve every private coordinate and the same reached full World. -/
theorem abort_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (env : EnvState Auxiliary)
    (value : Value) (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((RegistrationBeaconReferenceFinish.abort (eraseOwner owner) *> pure value :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource Value).run (eraseOwner current)).run (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map view id <$>
        (simulateQ (trusted setup wire route sign seed scalar)
          (((RegistrationBeaconReferenceNativeOwner.abort owner *> pure value :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource Value).run current).run env)).run before := by
  rw [public_abort]
  have source := congrArg (fun work => (simulateQ (trusted setup wire route sign seed scalar) work).run before)
    (abort_projection (n := n) (KemSK := KemSK) owner current env value)
  simp only [simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose] at source
  have lowered : trusted (n := n) setup wire route sign seed scalar ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment =
      implementation setup wire route sign seed scalar ∘ₛ effect := by
    funext query
    simp only [trusted, QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, trustedLift]
  rw [lowered, QueryImpl.simulateQ_compose] at source
  simpa only [Prod.map_def, id_eq] using source.symm

/-- A missing returned reference rejects before any opening, while retaining the actual terminal World abort. -/
theorem complete_missing (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : Private n KemSK)
    (missing : before.extra.1 ready.reference = none) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before =
      (simulateQ (implementation setup wire route sign seed scalar)
        (((RegistrationBeaconReferenceFinish.abort owner *> pure (.ok none) :
          RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
            mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, bind_map_left, RegistrationNativePairedBeaconService.admitted]
  have service : implementation (n := n) setup wire route sign seed scalar ∘ₛ
      RegistrationBeaconReferenceFinish.service =
      RegistrationNativeOrdinaryFinishSourceMaterial.service setup wire route sign seed scalar := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query]
    rfl
  rw [← QueryImpl.simulateQ_compose, service]
  simp only [simulateQ_spec_query]
  rw [RegistrationNativeOrdinaryFinishSourceMaterial.demand_run]
  simp only [missing, Option.map_none, pure_bind, simulateQ_pure, StateT.run_pure,
    RegistrationBeaconReferenceFinish.abort]

/-- Every post-agreement branch reconstructs the actual native owner continuation from the returned memo cell, including absent roots and all failures. -/
theorem continuation_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (owner current : RegistrationNativeBeaconFrontend.Owner mlSource) (env : EnvState Auxiliary)
    (authenticated : registration.AuthenticatedResponse)
    (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) (erased : Std.Array U8 357#usize)
    (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (((afterPrepared setup.source (eraseOwner owner) result :
        RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
          mlSource (RustM (Option Pqxdh.Bytes))).run (eraseOwner current)).run
            (RegistrationBeaconReferenceNativeRecord.erase env))).run before =
      Prod.map view id <$>
        (simulateQ (trusted setup wire route sign seed scalar)
          (((sourceAfter setup wire owner (restored before.extra.1 authenticated result) :
            RegistrationBeaconReferenceNativeOwner.M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before := by
  cases result with
  | fail error | div => exact abort_native setup wire route sign seed scalar owner current env _ before
  | ok result => cases result with
    | none => exact abort_native setup wire route sign seed scalar owner current env _ before
    | some ready =>
        cases memo : before.extra.1 ready.reference with
        | none =>
            simp only [afterPrepared, restored, memo, sourceAfter]
            rw [complete_missing setup wire route sign seed scalar (eraseOwner owner) (eraseOwner current)
              (RegistrationBeaconReferenceNativeRecord.erase env) ready before memo]
            exact abort_native setup wire route sign seed scalar owner current env _ before
        | some root =>
            simp only [afterPrepared, restored, memo, sourceAfter]
            rw [RegistrationNativeOrdinaryFinishSourceNative.complete_native setup wire route sign seed scalar
              (eraseOwner owner) (eraseOwner current) (RegistrationBeaconReferenceNativeRecord.erase env) ready root before memo]
            have actual := congrArg (fun work => (simulateQ (trusted setup wire route sign seed scalar) work).run before)
              (RegistrationBeaconReferenceNativeKnown.post_root (n := n) (KemSK := KemSK) setup wire erased owner current
                ready.descriptor root env)
            simpa only [simulateQ_map, StateT.run_map, Prod.map_def, id_eq,
              RegistrationBeaconReferenceRoot.atRoot, view] using actual.symm

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation.abort_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation.abort_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation.complete_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation.complete_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation.continuation_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceContinuation.continuation_native
