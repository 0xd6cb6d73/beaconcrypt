-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountServer
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptView
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishView
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountBundle
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountCreation

/-! Actual corrected platform callbacks retain their complete projected Native state and external platform state under original-input and normalized ML count equations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaCountRules (Correct)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((), change before) := rfl

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Value)
    (good : Correct RegistrationNativeMldsaCountServer.serverProject work) :
    Correct (RegistrationNativeMldsaMainView.project (KemSK := KemSK) (source := source)) (RegistrationNativePlatformExperiment.server (source := source) work) := by
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result =>
      (result.1, ({ RegistrationNativeMldsaMainView.project before.1 with server := result.2.1 }, result.2.2))) <$> computation)
      (good.1 (before.1.server, before.2))
    simp only [RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.server,
      StateT.run, map_apply, Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project,
      RegistrationNativeMldsaMainView.project, RegistrationNativeMldsaMainView.uniform,
      RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
      RegistrationServerRecordWorldSource.project, RegistrationNativeKemServerState.maskServer,
      RegistrationNativeMldsaCountServer.serverProject, RegistrationNativeMldsaCountServer.localProject,
      RegistrationNativeMldsaWorldView.project] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result =>
      (result.1, ({ RegistrationNativeMldsaMainView.project before.1 with server := result.2.1 }, result.2.2))) <$> computation)
      (good.2 (before.1.server, before.2))
    simp only [RegistrationNativePlatformPackedState.pack, RegistrationNativePlatformExperiment.server,
      StateT.run, map_apply, RegistrationNativeMldsaCountMap.transform, simulateQ_map,
      Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project,
      RegistrationNativeMldsaMainView.project, RegistrationNativeMldsaMainView.uniform,
      RegistrationNativePublicSourceState.nativeView, RegistrationServerMaterialSourceState.nativeView,
      RegistrationServerRecordWorldSource.project, RegistrationNativeKemServerState.maskServer,
      RegistrationNativeMldsaCountServer.serverProject, RegistrationNativeMldsaCountServer.localProject,
      RegistrationNativeMldsaWorldView.project] at same ⊢
    exact same

private theorem lift_bind {S V W : Type} (work : StateT S (StateT Platform ProbComp) V)
    (next : V → StateT S (StateT Platform ProbComp) W) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (work >>= next) =
      (RegistrationNativePlatformMldsaProgram.lift work >>= fun value => RegistrationNativePlatformMldsaProgram.lift (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run_bind, simulateQ_bind]
  rfl
private theorem lift_server (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value) :
    RegistrationNativePlatformMldsaProgram.lift (source := source)
      (RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := source) work) =
      RegistrationNativePlatformExperiment.server (RegistrationNativePlatformMldsaProgram.lift work) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativePlatformExperiment.server, StateT.run, map_apply, RegistrationNativeMldsaProgram.lift, simulateQ_map]

private theorem project_parsed (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeMldsaMainView.project { before with parsedAccepts := before.parsedAccepts + 1 } =
      { RegistrationNativeMldsaMainView.project before with parsedAccepts := before.parsedAccepts + 1 } := rfl

private theorem parsed : Correct (source := source) (Platform := Platform) (RegistrationNativeMldsaMainView.project (n := n) (source := source) (KemSK := KemSK))
    (RegistrationNativePlatformMldsaProgram.lift
      (modify fun state => { state with parsedAccepts := state.parsedAccepts + 1 })) := by
  apply RegistrationNativePlatformMldsaCountRules.closed
  intro before
  simp only [RegistrationNativePlatformPackedState.pack, StateT.run, modify_apply, pure_apply, map_pure,
    RegistrationNativePlatformMldsaCountRules.project, Prod.map, id_eq, project_parsed,
    RegistrationNativeMldsaMainView.idempotent]
  rfl

private def NonBuild : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.build _ _) => False
  | _ => True

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem nonBuild (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : NonBuild query) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query) := by
  have native (work : RegistrationNativeExperiment.M n KemSK source (RegistrationNativeRawAdapter.TypedSpec.Range query))
      (stable : RegistrationNativeKemCounterIndependence.Stable RegistrationNativeMldsaMainView.project work) :
      Correct (source := source) (Platform := Platform) (RegistrationNativeMldsaMainView.project (n := n) (source := source))
        (RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformExperiment.liftNative RegistrationNativePlatformMldsaProgram.coins work)) :=
    RegistrationNativePlatformMldsaCountRules.native _ _ stable
  cases query with
  | inl coin => exact native _ (RegistrationNativeMldsaMainView.handler setup checks wire route representation created credential _)
  | inr query => cases query with
    | build _ _ => exact ordinary.elim
    | create edPin mlPin keyId =>
      exact RegistrationNativePlatformMldsaCountRules.inject _ _
        (RegistrationNativeMldsaCountCreation.create setup checks representation created edPin mlPin keyId)
    | bundle index => exact RegistrationNativePlatformMldsaCountBundle.sourceBundle setup checks representation created writer index
    | finish index packet => exact RegistrationNativePlatformFinishView.count setup checks representation created wire index packet
    | accept packet =>
      simp only [RegistrationNativePlatformMldsaProfile.handler, RegistrationNativePlatformExperiment.handler]
      rw [lift_bind]
      apply RegistrationNativePlatformMldsaCountRules.bind RegistrationNativeMldsaMainView.project _ _ parsed
      intro _parsed
      rw [lift_server]
      exact server _ (RegistrationNativePlatformAcceptView.accept setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration
        route source.verify representation created packet)
    | _ => exact native _ (RegistrationNativeMldsaMainView.handler setup checks wire route representation created credential _)

/-- Every actual corrected callback has both count equations, including all stateful first-record and source publication failures. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query) := by
  cases query with
  | inl coin => exact nonBuild setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer _ trivial
  | inr query => cases query with
    | build handle application =>
      simp only [RegistrationNativePlatformMldsaProfile.handler]
      apply RegistrationNativePlatformMldsaCountRules.bind RegistrationNativeMldsaMainView.project _ _
        (server _ (RegistrationNativePlatformMldsaCountServer.build credential setup (RegistrationNativeWire.ledgerCodec wire)
          view failure allocation erased reservePeer helper writer handle application))
      intro _result
      exact RegistrationNativePlatformMldsaCountRules.pure RegistrationNativeMldsaMainView.project RegistrationNativeMldsaMainView.idempotent _
    | _ => exact nonBuild setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer _ trivial

/-- Arbitrary adaptive typed work preserves the full projected Native state and exact public platform state under both source count equations. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Correct (RegistrationNativeMldsaMainView.project (n := n) (source := source))
      (simulateQ (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer) work) :=
  RegistrationNativePlatformMldsaCountRules.simulate _ RegistrationNativeMldsaMainView.idempotent _
    (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer) work

def observed (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source) × Platform) :=
  ((result.1.1, RegistrationNativeMldsaMainView.project result.1.2), result.2)

/-- Original corrected execution is independent of omitted accounting inputs while retaining its literal compiled ledger and external poststate. -/
theorem run_original (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    observed <$> ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode work before).run previous) =
      observed <$> ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode work (RegistrationNativeMldsaMainView.project before)).run previous) := by
  have same := congrArg (fun action => (fun result => ((result.1, result.2.1), result.2.2)) <$> action)
    ((program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).1 (before, previous))
  simp only [RegistrationNativePlatformMldsaProfile.run, RegistrationNativePlatformPackedState.pack,
    StateT.run, Functor.map_map, Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project] at same ⊢
  exact same

/-- Normalizing each named ML draw receipt retains the exact original compiled ledger/test bit and complete projected Native/platform poststate. -/
theorem run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    observed <$> RegistrationNativeMldsaCountMap.transform
      ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode work before).run previous) =
      observed <$> ((RegistrationNativePlatformMldsaProfile.run setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode work (RegistrationNativeMldsaMainView.project before)).run previous) := by
  have same := congrArg (fun action => (fun result => ((result.1, result.2.1), result.2.2)) <$> action)
    ((program setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)).2 (before, previous))
  simp only [RegistrationNativePlatformMldsaProfile.run, RegistrationNativePlatformPackedState.pack,
    StateT.run, RegistrationNativeMldsaCountMap.transform, simulateQ_map, Functor.map_map,
    Prod.map, id_eq, RegistrationNativePlatformMldsaCountRules.project] at same ⊢
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.run_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.run_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRun.run
