-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy
/-! Actual pure pin selection, complete-message preflight, live peer occupancy and transcript-AD hashing are preserved before root-reference material demand. The private interpretation reconstructs the consumed token while retaining every reached shared state and source failure. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePlatformServerMaterialState (State close restore service bind_close pure_close lift_close)
variable {n : Nat} {ι KemSK Reader Response E : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem pure_restore {A : Type} (roots : Roots) (value : A) (before : State n) :
    Prod.map id (restore roots) <$> (close (pure value : StateT RegistrationServerMaterialFrontend.State (StateT (Local n) m) A)).run before =
      pure (value, restore roots before) := by
  rw [pure_close, map_pure]
  rfl

private theorem lift_bind {A B : Type} (work : StateT (Local n) m A)
    (next : A → StateT RegistrationServerMaterialFrontend.State (StateT (Local n) m) B) :
    (fun before => do let value ← work; (next value).run before) =
      (StateT.lift work >>= next) := by
  funext before
  change (do let value ← work; (next value).run before) = (StateT.lift work >>= next).run before
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]

omit [LawfulMonad m] in
private theorem world_run {A : Type} (work : StateT (Local n) m A) (current : RegistrationServerFrontendCompiler.State n) :
    (RegistrationNativePlatformServerSdk.world work).run current =
      (fun result => (result.1, { current with world := result.2 })) <$> work.run current.world := rfl

/-- Pure full-pin selection precedes each public lookup; restoring a private token affects neither admission nor the reached occupancy/reservation effects. -/
theorem after_pin (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (reserve : m Bool)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) (control : pqxdh.ServerState) (ready : RegistrationServerReferenceRoot.Ready)
    (application : Slice U8) (current : RustM (core.option.Option session.ServerAuthenticationPin)) (before : State n) :
    Prod.map id (restore roots) <$>
      (close (RegistrationNativePlatformServerMaterialFrontend.afterPin (RegistrationNativePlatformServerMaterialState.adHash coins) (StateT.lift reserve)
        (fun keyId => RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))
        (service coins setup codec sealing hash signing helper writer roots) control ready application current)).run before =
      (RegistrationNativePlatformCompletionSdk.afterPin (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (StateT.lift reserve)
        (RegistrationNativePlatformCompletionSdk.nativePresent coins)
        (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer)
        control (RegistrationServerReferenceRestore.token roots ready) application current).run (restore roots before) := by
  cases current with
  | fail error => exact pure_restore roots (RustM.fail error : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before
  | div => exact pure_restore roots (RustM.div : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before
  | ok current => cases current with
    | none => exact pure_restore roots (RustM.ok none : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before
    | some pin =>
      unfold RegistrationNativePlatformCompletionSdk.afterPin RegistrationNativePlatformServerMaterialFrontend.afterPin
      dsimp! only
      rw [show RegistrationServerReferenceRestore.token roots ready =
        peer.ConsumedRegistration.mk (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference)) from rfl,
        RegistrationServerReferenceSourceLookup.begin_root]
      cases looked : peer.begin_completion_lookup control pin (RegistrationServerMaterialFrontend.token ready) application with
      | fail error =>
        exact pure_restore roots (RustM.fail error : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before
      | div =>
        exact pure_restore roots (RustM.div : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before
      | ok answer => cases answer with
        | Err previous =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk]
          exact pure_restore roots (RustM.ok none : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before
        | Ok lookup =>
          simp only [RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk,
            peer.CompletionLookup.request]
          have key_id : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots ready.reference)).key_id = lookup.key_id := rfl
          rw [key_id]
          by_cases preflight : RegistrationServerSdkSource.preflight application lookup.key_id = true
          · simp only [ite_eq_left preflight]
            rw [lift_bind, bind_close, StateT.run_bind, lift_close]
            simp only [RegistrationNativePlatformCompletionSdk.nativePresent, StateT.run_bind, world_run,
              map_bind, bind_map_left]
            apply bind_congr
            rintro ⟨occupied, currentLocal⟩
            exact RegistrationNativePlatformServerMaterialOccupancy.native coins setup codec sealing hash reserve signing helper writer roots
              control lookup ready.reference occupied (before.1, currentLocal)
          · simp only [ite_eq_right preflight]
            exact pure_restore roots (RustM.ok none : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) before

private theorem pin_run (coins : QueryImpl unifSpec m) (roots : Roots) (before : State n) :
    (RegistrationNativePlatformSourceBuild.pin coins).run (restore roots before) =
      (fun result => (result.1, restore roots (before.1, result.2))) <$>
        (RegistrationNativePlatformServerMaterialState.pin coins before.1.pin).run before.2 := by
  simp only [RegistrationNativePlatformSourceBuild.pin, RegistrationNativePlatformServerMaterialState.pin,
    StateT.run, Functor.map_map, restore, RegistrationServerReferenceRestore.restore]

/-- The complete actual source pin/lookup/preflight/occupancy/reservation/material/commit path restores the same private native token and full shared state. -/
theorem complete (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (reserve : m Bool)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8) (before : State n) :
    Prod.map id (restore roots) <$>
      (close (RegistrationNativePlatformServerMaterialFrontend.complete
        (RegistrationNativePlatformServerMaterialState.adHash coins)
        (RegistrationNativePlatformServerMaterialState.pin coins) (StateT.lift reserve)
        (fun keyId => RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))
        (service coins setup codec sealing hash signing helper writer roots) ready application)).run before =
      (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (RegistrationNativePlatformSourceBuild.pin coins)
        (StateT.lift reserve) (RegistrationNativePlatformCompletionSdk.nativePresent coins)
        (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer)
        (RegistrationServerReferenceRestore.token roots ready) application).run (restore roots before) := by
  rw [RegistrationNativePlatformCompletionSdk.complete_run, pin_run coins roots before]
  simp only [close, RegistrationNativePlatformServerMaterialFrontend.complete, StateT.run,
    StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨current, currentLocal⟩
  have same := after_pin coins setup codec sealing hash reserve signing helper writer roots
    before.1.control ready application current (before.1, currentLocal)
  simpa only [close, StateT.run, Functor.map_map, restore, RegistrationServerReferenceRestore.restore] using same

/-- The literal source SDK build consumes the same public one-use reference before cancellation or every later stateful failure, then executes the full corrected material frontend. -/
theorem build (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (reserve : m Bool)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) (handle : Nat) (application : Option (Slice U8)) (before : State n) :
    Prod.map id (restore roots) <$>
      (close (RegistrationNativePlatformServerMaterialFrontend.build
        (RegistrationNativePlatformServerMaterialState.adHash coins)
        (RegistrationNativePlatformServerMaterialState.pin coins) (StateT.lift reserve)
        (fun keyId => RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))
        (service coins setup codec sealing hash signing helper writer roots) handle application)).run before =
      (RegistrationNativePlatformSourceBuild.buildSource coins setup codec sealing hash reserve signing helper writer
        handle application).run (restore roots before) := by
  have taken := RegistrationServerReferenceRestore.take roots handle before.1 before.2
  change RegistrationServerSdkSource.take handle (restore roots before) =
    ((RegistrationServerMaterialFrontend.take handle before.1).1.map (RegistrationServerReferenceRestore.token roots),
      restore roots ((RegistrationServerMaterialFrontend.take handle before.1).2, before.2)) at taken
  simp only [close, StateT.run, RegistrationNativePlatformServerMaterialFrontend.build,
    RegistrationNativePlatformSourceBuild.buildSource, RegistrationNativePlatformCompletionSdk.build]
  rw [taken]
  cases selected : RegistrationServerMaterialFrontend.take handle before.1 with
  | mk ready current => cases ready with
    | none => exact pure_restore roots (RustM.ok none : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) (current, before.2)
    | some ready => cases application with
      | none => exact pure_restore roots (RustM.ok none : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)) (current, before.2)
      | some application =>
        change Prod.map id (restore roots) <$>
          (close (RegistrationNativePlatformServerMaterialFrontend.complete
            (RegistrationNativePlatformServerMaterialState.adHash coins)
            (RegistrationNativePlatformServerMaterialState.pin coins) (StateT.lift reserve)
            (fun keyId => RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))
            (service coins setup codec sealing hash signing helper writer roots) ready application)).run (current, before.2) = _
        exact complete coins setup codec sealing hash reserve signing helper writer roots ready application (current, before.2)

end BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialPin.build
