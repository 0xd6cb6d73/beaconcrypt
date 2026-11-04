-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel
import BeaconcryptCore.Computational.RegistrationAgreementEntryReadiness
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The reached-field Beacon source model has exactly two possible private captures: no converted identity, or the actual converted opaque identity. Its complete RNG is retained unchanged. The corresponding private readiness flag is erased using the actual Core schedule, without an agreement-success premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementCapture
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 Keys)
open AdapterPublicAgreementInterpreter (Capture)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementCommonModel (Model)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable def capture {R : Type} (model : Model (m := m) setup view) (keys : Keys)
    (rng : R) (flag : Bool) : Capture R :=
  ⟨rng, if flag then .Some ⟨model.representation.converted (view.edSecret keys.identity_secret)⟩ else .None, .None⟩

noncomputable def implementation (model : Model (m := m) setup view) (keys : Keys) : QueryImpl Spec m
  | .convertPublic key => pure (RegistrationPublicConversion.convert setup.source.crypto key)
  | .convertSecret _ => pure true
  | .generate _ => pure .None
  | .encapsulate _ => pure .None
  | .decapsulate input => AdapterPublicAgreementCommonModel.decapsulate model input keys.beacon_kem
  | .dh request => pure (AdapterPublicAgreementCommonModel.dh model keys (capture model keys () true) request)
  | .root request => pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request))

noncomputable section

theorem query {R : Type} (model : Model (m := m) setup view) (keys : Keys)
    (rng : R) (flag : Bool) (request : Request) :
    (AdapterPublicAgreementCommonModel.implementation model keys request).run (capture model keys rng flag) =
      Prod.map id (capture model keys rng) <$>
        (RegistrationAgreementIdentityGuard.implementation (implementation model keys) request).run flag := by
  cases request with
  | convertPublic key =>
    simp only [AdapterPublicAgreementCommonModel.implementation, implementation,
      RegistrationAgreementIdentityGuard.implementation, StateT.run_lift, StateT.run_pure, pure_bind, map_pure]
    rfl
  | convertSecret role =>
    simp only [AdapterPublicAgreementCommonModel.implementation,
      RegistrationAgreementIdentityGuard.secret_run, implementation, StateT.run_bind,
      StateT.run_modify, StateT.run_pure, pure_bind, map_pure, capture]
    rfl
  | generate role =>
    simp only [AdapterPublicAgreementCommonModel.implementation, implementation,
      RegistrationAgreementIdentityGuard.implementation, StateT.run_lift, StateT.run_pure, pure_bind, map_pure]
    rfl
  | encapsulate input =>
    simp only [AdapterPublicAgreementCommonModel.implementation, implementation,
      RegistrationAgreementIdentityGuard.implementation, StateT.run_lift, StateT.run_pure, pure_bind, map_pure]
    rfl
  | decapsulate input =>
    simp only [AdapterPublicAgreementCommonModel.implementation, implementation,
      RegistrationAgreementIdentityGuard.implementation, StateT.run_lift, bind_pure_comp, Functor.map_map]
    rfl
  | dh request =>
    rcases request with ⟨role, publicKey⟩
    cases flag <;> cases role <;>
      simp only [AdapterPublicAgreementCommonModel.implementation, implementation,
        RegistrationAgreementIdentityGuard.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, capture, Bool.false_eq_true, ↓reduceIte,
        StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind]
    all_goals simp only [StateT.run, Bool.false_eq_true, ↓reduceIte, map_pure]
    all_goals rfl
  | root request =>
    simp only [AdapterPublicAgreementCommonModel.implementation, implementation,
      RegistrationAgreementIdentityGuard.implementation, StateT.run_lift, StateT.run_pure, pure_bind, map_pure]
    rfl

theorem program {R Value : Type} (model : Model (m := m) setup view) (keys : Keys)
    (rng : R) (flag : Bool) (work : OracleComp Spec Value) :
    (simulateQ (AdapterPublicAgreementCommonModel.implementation model keys) work).run (capture model keys rng flag) =
      Prod.map id (capture model keys rng) <$>
        (simulateQ (RegistrationAgreementIdentityGuard.implementation (implementation model keys)) work).run flag := by
  induction work using OracleComp.inductionOn generalizing flag with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query model keys rng flag request]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨reply, after⟩
    exact ih reply after

theorem beacon {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (model : Model (m := m) setup view) (keys : Keys)
    (authenticated : registration.AuthenticatedResponse) (rng : R) :
    ((do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT m) generator phase keys rng) :
      RustT m (agreement.AgreementEffect × R)).run =
      (fun result => do let completed ← result; .ok (completed, rng)) <$>
        simulateQ (implementation model keys) (RegistrationAgreementExecutor.beacon authenticated) := by
  rw [AdapterPublicAgreementCommonModel.beacon_execute (generator := generator) model keys authenticated rng]
  change (fun result => do let completed ← result.1; .ok (completed, result.2.rng)) <$>
      (simulateQ (AdapterPublicAgreementCommonModel.implementation model keys)
        (RegistrationAgreementExecutor.beacon authenticated)).run (capture model keys rng false) = _
  rw [program]
  simp only [Functor.map_map]
  rw [← RegistrationAgreementEntryReadiness.beacon (implementation model keys) authenticated,
    Functor.map_map]
  rfl
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementCapture

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCapture.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCapture.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCapture.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCapture.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementCapture.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementCapture.beacon
