-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView
import BeaconcryptCore.Computational.RegistrationNativeMainView
import BeaconcryptCore.Computational.RegistrationNativeKemDispatcherCompiler

/-! The complete actual native handler ignores private uniform, native-call, Env coin and record-kind accounting inputs. The view retains all protocol control, keys, pools, signing/agreement histories, cache, record state and original secrecy ledger. These are source-input independence laws; changing an external primitive reply or its private receipt is a separate comparison. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaMainView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemCounterIndependence (Stable)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def uniform (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeExperiment.State n KemSK source :=
  { before with server := RegistrationNativeKemServerState.maskServer before.server }

def project (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeExperiment.State n KemSK source :=
  uniform (RegistrationNativePublicSourceState.nativeView before)

private theorem commute (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativePublicSourceState.nativeView (uniform before) =
      uniform (RegistrationNativePublicSourceState.nativeView before) := rfl

/-- The complete ML analysis view is idempotent and leaves source state unchanged after its first application. -/
theorem idempotent (before : RegistrationNativeExperiment.State n KemSK source) : project (project before) = project before := by
  simp only [project, uniform, RegistrationNativePublicSourceState.nativeView,
    RegistrationServerMaterialSourceState.nativeView, RegistrationServerRecordWorldSource.project,
    RegistrationNativeKemServerState.maskServer, RegistrationNativeKemWorldUniform.mask,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, Function.update_idem]

/-- Exact source opening of every native callback derives uniform-input independence while retaining its complete private KEM pool. -/
theorem uniform_handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Stable (uniform (n := n)) (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query) := by
  intro before
  have first := RegistrationNativeKemDispatcherCompiler.handler_source setup checks wire route representation created credential query before
  have second := RegistrationNativeKemDispatcherCompiler.handler_source setup checks wire route representation created credential query (uniform before)
  have sameInput : RegistrationNativeKemAcceptCompiler.nativeProject (uniform before) =
      RegistrationNativeKemAcceptCompiler.nativeProject before := rfl
  rw [sameInput] at second
  have same := congrArg (fun work => (fun (result : RegistrationNativeRawAdapter.TypedSpec.Range query ×
      (RegistrationNativeKemServerState.State n source × PqxdhLiveKemBirth.Pool KemSK)) =>
        (result.1, RegistrationNativeKemServerState.toNative result.2.1 result.2.2)) <$> work) (first.trans second.symm)
  simp only [Functor.map_map, Prod.map, id_eq, RegistrationNativeKemAcceptCompiler.nativeProject,
    RegistrationNativeKemServerState.project, RegistrationNativeKemServerState.mask,
    RegistrationNativeKemServerState.ofNative, RegistrationNativeKemServerState.toNative, uniform] at same ⊢
  exact same

private theorem compose_stable {S Answer : Type} (first second : S → S)
    (commuting : ∀ before, first (second before) = second (first before)) (work : StateT S ProbComp Answer)
    (left : Stable first work) (right : Stable second work) : Stable (fun before => second (first before)) work := by
  intro before
  have initial := congrArg (fun action => Prod.map id second <$> action) (left before)
  have following := congrArg (fun action => Prod.map id first <$> action) (right (first before))
  simp only [Functor.map_map, Prod.map, id_eq] at initial following ⊢
  simp only [commuting] at following
  exact initial.trans following

/-- Every complete actual typed callback preserves its exact projected outcome under the explicitly omitted accounting inputs. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Stable (project (n := n)) (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query) :=
  compose_stable RegistrationNativePublicSourceState.nativeView uniform commute _
    (RegistrationNativeMainView.handler_input setup checks wire route representation created credential query)
    (uniform_handler setup checks wire route representation created credential query)

/-- Arbitrary adaptive typed programs preserve complete projected state through the source-proved callback laws. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Stable (project (n := n)) (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work) :=
  RegistrationNativeKemCounterIndependence.program_stable project idempotent _
    (handler setup checks wire route representation created credential) work

def observed (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) :=
  (result.1, (result.2.1, project result.2.2))

/-- The complete unchanged original ledger run retains its literal test bit and outcome under the source accounting-input view. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    observed <$> RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before =
      observed <$> RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work (project before) := by
  have same := congrArg (fun computation => (fun result => (result.1.1, (result.1.2, result.2))) <$> computation)
    (program setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before)
  simp only [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run,
    observed, Functor.map_map, Prod.map, id_eq] at same ⊢
  exact same
end BeaconcryptCore.Computational.RegistrationNativeMldsaMainView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.uniform_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.uniform_handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaMainView.run
