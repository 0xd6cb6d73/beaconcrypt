-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuildMetricView
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishView
import BeaconcryptCore.Computational.RegistrationNativeScalarEagerView
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryScalarEager
/-! The actual corrected runtime callbacks ignore the named instrumentation input while retaining true uniform counters and all source operational state. Stateful terminal writer gates remain public P actions after the exact attempted private send. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRuntimeMetricView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (nativeView)
open RegistrationStateView (Stable pure_stable bind_stable)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem closed (coins : QueryImpl unifSpec m)
    (work : StateT (RegistrationNativeExperiment.State n KemSK source) ProbComp A) (stable : Stable nativeView work) :
    Stable nativeView (RegistrationNativePlatformExperiment.liftNative coins work) := by
  intro before
  have actual := congrArg (simulateQ coins) (stable before)
  simpa only [RegistrationNativePlatformExperiment.liftNative, StateT.run, simulateQ_map] using actual

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) m A)
    (stable : Stable RegistrationServerMaterialSourceState.nativeView work) :
    Stable (nativeView (KemSK := KemSK) (mlSource := source)) (RegistrationNativePlatformExperiment.server work) := by
  intro before
  have actual := congrArg (fun action => (fun result => (result.1,
    {nativeView before with server := result.2})) <$> action) (stable before.server)
  simpa only [RegistrationNativePlatformExperiment.server, StateT.run, Functor.map_map, nativeView,
    Prod.map_def, id_eq, Function.comp_def] using actual

private theorem parsed : Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := source))
    (modify fun before : RegistrationNativeExperiment.State n KemSK source =>
      {before with parsedAccepts := before.parsedAccepts + 1} : StateT _ m Unit) := by
  intro before
  simp only [StateT.run_modify, map_pure, nativeView, Prod.map_def, id_eq, RegistrationNativeServerViewAccept.view_idempotent]

private theorem external (work : m A) : Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := source)) (StateT.lift work) := by
  intro before
  simp only [StateT.run_lift, map_bind, map_pure, Prod.map_def, id_eq, RegistrationNativeMainViewLift.view_idempotent]

end Generic

private theorem after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform (Option RawCtxSourceSend.Encrypted))
    (stable : Stable nativeView work) :
    Stable nativeView (RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work) :=
  bind_stable _ _ _ stable (fun _ => external _)

private theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := source))
      (RegistrationNativePlatformOrdinaryExperiment.record setup wire reserve route query source) := by
  cases query with
  | inl query => cases query with
    | inl send =>
      rcases send with ⟨plaintext, keyId⟩
      rw [RegistrationNativePlatformOrdinaryExperimentRouting.server_send]
      exact after reserve _ (closed _ _ (RegistrationNativeMainView.record_input setup _ route _))
    | inr raw =>
      rw [RegistrationNativePlatformOrdinaryExperimentRouting.server_raw]
      exact closed _ _ (RegistrationNativeMainView.record_input setup _ route _)
  | inr query =>
    rcases query with ⟨owner, request⟩
    cases request with
    | inl plaintext =>
      rw [RegistrationNativePlatformOrdinaryExperimentRouting.beacon_send]
      exact after reserve _ (closed _ _ (RegistrationNativeMainView.record_input setup _ route _))
    | inr raw =>
      rw [RegistrationNativePlatformOrdinaryExperimentRouting.beacon_raw]
      exact closed _ _ (RegistrationNativeMainView.record_input setup _ route _)

def NonBundle : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.bundle _) => False
  | _ => True

/-- Every actual runtime callback except effectful Init publication follows its derived instrumentation-input law. -/
theorem nonbundle [primitive : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (nonBundle : NonBundle query) :
    Stable nativeView (RegistrationNativePlatformOrdinaryScalarEager.handler (n := n) setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected scalar query) := by
  cases query with
  | inl coin => exact closed _ _ (RegistrationNativeMainView.handler_input setup checks _ route representation created credential (.inl coin))
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact closed _ _ (RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
        (RegistrationNativeScalarEagerView.create_stable setup selected scalar edPin mlPin keyId))
    | bundle owner => exact nonBundle.elim
    | accept packet =>
      change Stable nativeView (do
        modify fun before : RegistrationNativeExperiment.State n KemSK source => {before with parsedAccepts := before.parsedAccepts + 1}
        RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks reserveRegistration
          route source.verify representation created packet))
      exact bind_stable _ _ _ parsed (fun _ => server _ (RegistrationNativePlatformSourceAcceptMetricView.accept _ setup _ checks reserveRegistration route source.verify representation created packet))
    | build handle application =>
      change Stable nativeView (RegistrationNativePlatformPublicFrontend.responseBytes <$>
        RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup
          (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) view failure allocation erased reservePeer
          (RegistrationNativeMldsa.owned source credential) helper writer handle application))
      rw [map_eq_bind_pure_comp]
      exact bind_stable _ _ _ (server _ (RegistrationNativePlatformSourceBuildMetricView.build _ setup _ view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer handle application)) (fun _ => pure_stable _ RegistrationNativeMainViewLift.view_idempotent _)
    | finish owner packet =>
      exact closed _ _ (RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
        (RegistrationNativePlatformFinishView.finish_stable setup _ owner packet))
    | hmac key bytes => exact closed _ _ (RegistrationNativeMainView.handler_input setup checks _ route representation created credential (.inr (.hmac key bytes)))
    | hash bytes => exact closed _ _ (RegistrationNativeMainView.handler_input setup checks _ route representation created credential (.inr (.hash bytes)))
    | serverSend keyId plaintext => exact record setup wire reserveFrame route (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record setup wire reserveFrame route (.inl (.inr raw))
    | beaconSend owner plaintext => exact record setup wire reserveFrame route (.inr (owner, .inl plaintext))
    | beaconRaw owner raw => exact record setup wire reserveFrame route (.inr (owner, .inr raw))
end BeaconcryptCore.Computational.RegistrationNativePlatformRuntimeMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRuntimeMetricView.nonbundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRuntimeMetricView.nonbundle
