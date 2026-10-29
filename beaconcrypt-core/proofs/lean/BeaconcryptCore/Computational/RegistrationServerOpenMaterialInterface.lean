-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialBuildSource
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler
import BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix

/-! The open finite Server service evaluates local publication on the current environment receipts. Closing its private known-root lookup and World effects gives the same complete local source service, with no counter projection at this layout step. Unused prepare/publication/KEM callbacks remain arbitrary because this component never calls them. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenMaterialInterface
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

noncomputable def callbacks (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra) : Callbacks n KemSK Extra :=
  { services with demand := fun message => pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot hkdf (roots message)))) }

def project (before : Environment × Private n KemSK Extra) : RegistrationServerRootCompiler.Local n :=
  RegistrationWorldAgreementCompiler.join before.1 before.2.world

noncomputable def source (setup : Setup base KemSK) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n)
      (StateT (Environment × Private n KemSK Extra) ProbComp) := fun query =>
  RegistrationNativeKemReferencePrefix.lower setup (callbacks setup.source roots services)
    (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      RegistrationServerOpenReferenceCompiler.demand setup.source writer sign query)

private theorem lower_run (setup : Setup base KemSK) (services : Callbacks n KemSK Extra)
    (work : StateT Environment (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Value)
    (before : Environment × Private n KemSK Extra) :
    (RegistrationNativeKemReferencePrefix.lower setup services work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (implementation setup services) (work.run before.1)).run before.2 := rfl

private theorem effect_program (setup : Setup base KemSK) (roots : RegistrationServerReferenceRestore.Roots)
    (services : Callbacks n KemSK Extra) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : Private n KemSK Extra) :
    (simulateQ (implementation setup (callbacks setup.source roots services))
      (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [← QueryImpl.simulateQ_compose]
  have same : implementation setup (callbacks setup.source roots services) ∘ₛ
      RegistrationBeaconReferenceCompiler.effect = RegistrationNativeKemReferenceWorld.effect := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceCompiler.effect,
      simulateQ_spec_query, implementation, RegistrationNativeKemReferenceWorld.handler]
  rw [same]
  exact RegistrationNativeKemReferenceWorld.world_program PqxdhRecordLiftWorld.effects work before

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  rw [bind_pure_comp]

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

/-- The actual closed open-service query retains its exact reply, current receipts and full World in the local source interpretation. -/
theorem query (setup : Setup base KemSK) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (roots : RegistrationServerReferenceRestore.Roots) (services : Callbacks n KemSK Extra)
    (query : (RegistrationNativePairedServerService.PublicSpec n).Domain)
    (before : Environment × Private n KemSK Extra) :
    Prod.map id project <$> (source setup writer sign roots services query).run before =
      (RegistrationServerMaterialSourceState.service setup.source writer sign roots query).run (project before) := by
  change Prod.map id project <$>
    (RegistrationNativeKemReferencePrefix.lower setup (callbacks setup.source roots services)
      (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
        RegistrationServerOpenReferenceCompiler.demand setup.source writer sign query)).run before = _
  rw [lower_run, Functor.map_map]
  cases query with
  | inl message =>
      simp only [RegistrationNativeCommonCompiler.service,
        simulateQ_map, simulateQ_spec_query,
        RegistrationServerOpenReferenceCompiler.demand, implementation, RegistrationNativeKemReferenceWorld.handler,
        callbacks, StateT.run, RegistrationServerMaterialSourceState.service, state_lift_apply, state_map_apply, state_pure_apply,
        map_pure, Prod.map_def, id_eq]
  | inr query =>
      cases query with
      | inl publication =>
          simp only [RegistrationNativeCommonCompiler.service,
            RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
            StateT.run, simulateQ_map, state_map_apply, Functor.map_map]
          have native := effect_program setup roots services
            ((RegistrationBoundSourceCompiler.compiler setup.source writer sign publication).run before.1.receipts) before.2
          simp only [StateT.run] at native
          rw [native]
          simp only [RegistrationServerMaterialSourceState.service, RegistrationServerKnownStageWorldSource.common,
            RegistrationServerPublicationWorldCompiler.publication, StateT.run, Functor.map_map,
            Prod.map_def, id_eq, project, RegistrationWorldAgreementCompiler.join]
      | inr effect =>
          simp only [RegistrationNativeCommonCompiler.service,
            RegistrationNativeCommonCompiler.common, StateT.run_lift, bind_pure_comp,
            simulateQ_map, StateT.run_map, Functor.map_map]
          have native := effect_program setup roots services ((PqxdhRecordLiftInterface.EnvEffects n).query effect) before.2
          simp only [simulateQ_spec_query] at native
          rw [native]
          simp only [RegistrationServerMaterialSourceState.service, RegistrationServerKnownStageWorldSource.common,
            RegistrationServerPublicationWorldCompiler.effect, StateT.run, Functor.map_map,
            Prod.map_def, id_eq, project, RegistrationWorldAgreementCompiler.join]

end BeaconcryptCore.Computational.RegistrationServerOpenMaterialInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenMaterialInterface.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenMaterialInterface.query
