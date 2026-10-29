-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceKnown

/-! A finite native Beacon completion settles on the reached World rather than a captured environment. Its entire owner phase and environment are returned, including failure/abort paths, while private pool, memo and signing receipts are framed exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationNativeKemReferenceWorld (withWorld)
variable {ι KemSK Value Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Arbitrary ordinary effects preserve the actual pool and both chronological private histories. -/
theorem effects_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp (EnvEffects n) Value)
    (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed scalar)
      (simulateQ effect work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [← QueryImpl.simulateQ_compose]
  have step : implementation (n := n) setup wire route sign seed scalar ∘ₛ effect =
      fun query => withWorld (PqxdhRecordLiftWorld.effects query) := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query]
    rfl
  rw [step]
  exact RegistrationNativeKemReferenceWorld.world_program PqxdhRecordLiftWorld.effects work before

private theorem after_ast (owner current : SelectedOwner mlSource) (env : EnvState Auxiliary)
    (result : RustM RegistrationNativePairedBeaconService.Result) :
    (((RegistrationBeaconReferenceCompletion.after effect owner result :
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary)
        mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) =
      simulateQ effect
        (((RegistrationBeaconReferenceCompletion.after (QueryImpl.id' (EnvEffects n)) owner result :
          RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
            mlSource (RustM (Option Pqxdh.Bytes))).run current).run env) := by
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

noncomputable def sourceComplete (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (owner : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (root : PqxdhSecretInputKdf.RootOutput) :
    RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
      mlSource (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (StateT.lift
    (RegistrationBeaconReferenceNativeCompletion.knownEffects source writer owner ready.descriptor root))
  RegistrationBeaconReferenceCompletion.after (QueryImpl.id' (EnvEffects n)) owner completed

private theorem reference_settle (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready) :
    RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source owner ready = (do
      let completed ← StateT.lift (StateT.lift (simulateQ RegistrationBeaconReferenceFinish.service
        (RegistrationNativePairedBeaconService.admitted source owner.worldOwner owner.pin.binding.identity_key_id
          ready.descriptor ready.reference)))
      RegistrationBeaconReferenceCompletion.after effect owner completed) := by
  unfold RegistrationBeaconReferenceFinish.complete
  apply bind_congr
  intro result
  cases result with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

/-- Known material uses its freshly returned reference, actual source opening and complete reached owner/environment continuation. -/
theorem complete_known (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
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
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          (((sourceComplete setup.source wire.frameWrite owner ready root :
            RegistrationBeaconReferenceCompletion.M (target := EnvEffects n) (Auxiliary := Auxiliary)
              mlSource (RustM (Option Pqxdh.Bytes))).run current).run env)).run before.world := by
  rw [reference_settle]
  simp only [sourceComplete, StateT.run_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, map_bind, bind_map_left]
  have services : implementation (n := n) setup wire route sign seed scalar ∘ₛ
      RegistrationBeaconReferenceFinish.service =
      RegistrationNativeOrdinaryFinishSourceMaterial.service setup wire route sign seed scalar := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query]
    rfl
  rw [← QueryImpl.simulateQ_compose, services,
    RegistrationNativeOrdinaryFinishSourceKnown.admitted_known setup wire route sign seed scalar owner ready root before prepared]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨completed, reached⟩
  rw [after_ast]
  exact effects_program setup wire route sign seed scalar _ { before with world := reached }

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion.effects_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion.effects_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion.complete_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourceCompletion.complete_known
