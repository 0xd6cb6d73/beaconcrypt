-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk
import BeaconcryptCore.Computational.RegistrationNativeMldsaProfile

/-! Free ML count normalization preserves the actual complete native callback and adaptive original-ledger run under the explicit accounting view. Every callback instance is derived from its actual reified controller or original closed source body; no whole-program invisibility premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaProgram (Spec)
open RegistrationNativeMldsaCountRules (Correct)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaMainView (project)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) Value)
    (good : Correct RegistrationNativeMldsaCountServer.serverProject work) :
    Correct (project (KemSK := KemSK)) (RegistrationNativeMldsaProfile.server work) := by
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, { project before with server := result.2 })) <$> computation)
      (good.1 before.server)
    simp only [RegistrationNativeMldsaProfile.server, StateT.run, Functor.map_map, Prod.map, id_eq,
      project, RegistrationNativeMldsaMainView.uniform, RegistrationNativePublicSourceState.nativeView,
      RegistrationServerMaterialSourceState.nativeView, RegistrationServerRecordWorldSource.project,
      RegistrationNativeKemServerState.maskServer, RegistrationNativeMldsaCountServer.serverProject,
      RegistrationNativeMldsaCountServer.localProject, RegistrationNativeMldsaWorldView.project] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, { project before with server := result.2 })) <$> computation)
      (good.2 before.server)
    simp only [RegistrationNativeMldsaProfile.server, StateT.run, transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq, project, RegistrationNativeMldsaMainView.uniform,
      RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
      RegistrationServerRecordWorldSource.project, RegistrationNativeKemServerState.maskServer,
      RegistrationNativeMldsaCountServer.serverProject, RegistrationNativeMldsaCountServer.localProject,
      RegistrationNativeMldsaWorldView.project] at same ⊢
    exact same

/-- Every actual free native callback satisfies both original and count-normalized continuation equations. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Correct (project (n := n))
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) := by
  cases query with
  | inl coin =>
      exact RegistrationNativeMldsaCountRules.closed _ _
        (RegistrationNativeMldsaMainView.handler setup checks wire route representation created credential _)
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativeMldsaCountCreation.create setup checks representation created edPin mlPin keyId
    | bundle index => exact RegistrationNativeMldsaCountBundle.sourceBundle setup checks wire representation created index
    | build handle application =>
        exact server _
          (RegistrationNativeMldsaCountServerSdk.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
          checks wire.encodeResponse handle application)
    | _ =>
        exact RegistrationNativeMldsaCountRules.closed _ _
          (RegistrationNativeMldsaMainView.handler setup checks wire route representation created credential _)

/-- Arbitrary adaptive typed programs inherit the count-normalization law from actual source-derived callbacks. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Correct (project (n := n))
      (simulateQ (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) work) :=
  RegistrationNativeMldsaCountRules.simulate project RegistrationNativeMldsaMainView.idempotent _
    (handler setup checks wire route representation created credential) work

def observed (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) :=
  (result.1, (result.2.1, project result.2.2))

/-- The original free compiled run ignores the same omitted input accounting coordinates while retaining the literal ledger. -/
theorem run_original (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    observed <$> RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work before =
      observed <$> RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work (project before) := by
  have same := congrArg (fun computation => (fun result => (result.1.1, (result.1.2, result.2))) <$> computation)
    ((program setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).1 before)
  simp only [RegistrationNativeMldsaProfile.run, observed, Functor.map_map, Prod.map, id_eq] at same ⊢
  exact same

/-- Normalizing named ML draw receipts preserves the complete original compiled ledger run, its literal test bit and projected native poststate. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    observed <$> transform (RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work before) =
      observed <$> RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work (project before) := by
  have same := congrArg (fun computation => (fun result => (result.1.1, (result.1.2, result.2))) <$> computation)
    ((program setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).2 before)
  simp only [RegistrationNativeMldsaProfile.run, transform, simulateQ_map,
    observed, Functor.map_map, Prod.map, id_eq] at same ⊢
  exact same
end BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.run_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.run_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountRun.run
