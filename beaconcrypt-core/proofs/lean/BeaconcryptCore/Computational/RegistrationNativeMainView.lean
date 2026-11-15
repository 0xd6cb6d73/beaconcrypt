-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMainViewBeacon

/-! Full native Main execution retains its complete original ledger, raw transcript, generated owner roster, KEM pool and actual protocol outcome under the explicit private native/coin/record-kind instrumentation view. This theorem does not equate omitted resource bills; their bounds are transported separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMainView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePublicSourceState (nativeView)
open RegistrationStateView (Stable)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Actual established-record operations retain all outer admission refusals and every reached full native state. -/
theorem record_input (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) :
    Stable (nativeView (mlSource := mlSource) (n := n)) (RegistrationNativeExperiment.record setup wire route query mlSource) := by
  cases query with
  | inl query =>
      exact RegistrationNativeMainViewLift.world_input _
        (RegistrationNativeWorldViewRecords.guarded_input setup (ledgerCodec wire) route (.inr (.inr (.inl query))))
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query with
      | inl plaintext =>
        intro before
        cases found : before.beacons[owner]? with
        | none => simp only [RegistrationNativeExperiment.record, StateT.run, nativeView, found,
            map_pure, Prod.map, id_eq, RegistrationNativeServerViewAccept.view_idempotent]
        | some selected =>
          have law := RegistrationNativeMainViewLift.world_input _
            (RegistrationNativeWorldViewRecords.guarded_input setup (ledgerCodec wire) route
              (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) before
          simpa only [RegistrationNativeExperiment.record, StateT.run, nativeView, found] using law
      | inr raw =>
        intro before
        cases found : before.beacons[owner]? with
        | none => simp only [RegistrationNativeExperiment.record, StateT.run, nativeView, found,
            map_pure, Prod.map, id_eq, RegistrationNativeServerViewAccept.view_idempotent]
        | some selected =>
          have law := RegistrationNativeMainViewLift.world_input _
            (RegistrationNativeWorldViewRecords.guarded_input setup (ledgerCodec wire) route
              (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) before
          simpa only [RegistrationNativeExperiment.record, StateT.run, nativeView, found] using law

private theorem parsed_input : Stable (nativeView (n := n) (KemSK := KemSK) (mlSource := mlSource))
    (modify fun (state : RegistrationNativeExperiment.State n KemSK mlSource) => { state with parsedAccepts := state.parsedAccepts + 1 } : RegistrationNativeExperiment.M n KemSK mlSource Unit) := by
  intro before
  simp only [StateT.run_modify, map_pure, Prod.map, id_eq, nativeView,
    RegistrationNativeServerViewAccept.view_idempotent]

/-- Every actual native typed operation preserves the same complete protocol result and retained poststate. -/
theorem handler_input (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Stable (nativeView (n := n)) (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential query) := by
  cases query with
  | inl coin => exact RegistrationNativeMainViewLift.world_input _ (RegistrationNativeWorldViewEffects.effects_input (.inl coin))
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
          (RegistrationNativeBeaconEnvCreate.create_stable setup edPin mlPin keyId)
    | bundle owner =>
        exact RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
          (RegistrationNativeBeaconEnvBundle.bundle_stable setup wire owner)
    | accept packet =>
        unfold RegistrationNativeExperiment.handler
        apply RegistrationStateView.bind_stable
        · exact parsed_input
        · intro result
          exact RegistrationNativeMainViewLift.server_input _
            (RegistrationNativeServerViewAccept.accept_input setup (ledgerCodec wire) checks route mlSource.verify representation created packet)
    | build session application =>
        exact RegistrationNativeMainViewLift.server_input _
          (RegistrationNativeServerViewBuild.build_input setup (ledgerCodec wire) checks
            (RegistrationNativeMldsa.owned mlSource credential) wire.encodeResponse session application)
    | finish owner packet =>
        exact RegistrationNativeMainViewBeacon.beacon_input setup checks representation created _
          (RegistrationNativeBeaconEnvFinish.finish_stable setup wire owner packet)
    | hmac key message => exact RegistrationStateView.pure_stable _ RegistrationNativeMainViewLift.view_idempotent _
    | hash bytes => exact RegistrationNativeMainViewLift.world_input _ (RegistrationNativeWorldViewEffects.effects_input (.inr (.hash bytes)))
    | serverSend keyId plaintext => exact record_input setup wire route (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record_input setup wire route (.inl (.inr raw))
    | beaconSend owner plaintext => exact record_input setup wire route (.inr (owner, .inl plaintext))
    | beaconRaw owner raw => exact record_input setup wire route (.inr (owner, .inr raw))

/-- Arbitrary adaptive native typed execution preserves all retained state from its actual per-operation source laws. -/
theorem program_input (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) :
    Stable (nativeView (n := n))
      (simulateQ (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential) work) :=
  RegistrationStateView.program_stable _ RegistrationNativeMainViewLift.view_idempotent _
    (handler_input setup checks wire route representation created credential) work

def observedView (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK mlSource)) :=
  (result.1, (result.2.1, nativeView result.2.2))

/-- The whole original raw-CBOR native experiment retains its exact hidden-bit and fresh-message ledger under the explicit private source view. -/
theorem full_input (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    observedView <$> RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work before =
      observedView <$> RegistrationNativeExperiment.run setup checks wire route representation created mlSource credential bounds mode work (nativeView before) := by
  have law := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution)
    (program_input setup checks wire route representation created credential
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work) before)
  simp only [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run,
    observedView, Functor.map_map, Prod.map, id_eq] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativeMainView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainView.record_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainView.record_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainView.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainView.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainView.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainView.program_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMainView.full_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMainView.full_input
