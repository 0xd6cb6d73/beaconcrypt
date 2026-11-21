-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup
/-! The corrected source occupancy and reservation cuts preserve public lookup admission while restoring only the previously prepared private root. Native accounting, failed reservations and the complete platform state remain exact. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePlatformServerMaterialState (State close restore service bind_close pure_close lift_close)
variable {n : Nat} {ι KemSK Reader Response E : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

omit [LawfulMonad m] in
private theorem bind_apply {S A B : Type} (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let reached ← work before; next reached.1 reached.2) := rfl

omit [LawfulMonad m] in
private theorem pure_apply {S A : Type} (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem rust_map_eq {Input Output : Type} (f : Input → Output) (action : RustM Input) :
    f <$> action = (match action with
      | .fail error => .fail error
      | .div => .div
      | .ok value => .ok (f value)) := by
  cases action <;> rfl

private theorem result (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (reserve : m Bool)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) (control : pqxdh.ServerState)
    (reference : RegistrationNativeRelatedFamily.Message)
    (action : RegistrationServerAdHash.Result)
    (role : ∀ initial, action = .ok (.Ok initial) → initial.pending =
      PqxdhInitialRatchetComplementarity.serverPending (PqxdhRootTableInitialization.rootArray (roots reference)))
    (before : State n) :
    Prod.map id (restore roots) <$>
      (close (RegistrationNativePlatformServerMaterialFrontend.afterResult (StateT.lift reserve)
        (service coins setup codec sealing hash signing helper writer roots) control reference
        (RegistrationPublicationKernelErasure.mapOk RegistrationBoundKeySchedule.publicInitial <$> action))).run before =
      ((match (generalizing := false) action with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok initial) => do
        let admitted ← StateT.lift reserve
        if admitted then
          RegistrationNativePlatformCompletionSdk.fromInitial
            (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer)
            control initial
        else pure (.ok none)) : StateT (RegistrationServerFrontendCompiler.State n) m
        (RustM (Option (U64 × alloc.vec.Vec U8)))).run (restore roots before) := by
  cases action with
  | fail error | div =>
    simp only [rust_map_eq, RegistrationNativePlatformServerMaterialFrontend.afterResult, pure_close, map_pure]
    rfl
  | ok answer => cases answer with
    | Err previous =>
      simp only [rust_map_eq, RegistrationPublicationKernelErasure.mapOk,
        RegistrationNativePlatformServerMaterialFrontend.afterResult, pure_close, map_pure]
      rfl
    | Ok selected =>
      simp only [rust_map_eq, RegistrationPublicationKernelErasure.mapOk,
        RegistrationNativePlatformServerMaterialFrontend.afterResult]
      rw [bind_close, StateT.run_bind, lift_close]
      simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, map_bind, bind_map_left]
      apply bind_congr
      intro admitted
      cases admitted with
      | false => simp only [Bool.false_eq_true, ite_false, pure_close, map_pure]; rfl
      | true =>
        simp only [ite_true]
        exact RegistrationNativePlatformServerMaterialState.initial coins setup codec sealing hash signing helper writer roots
          control selected reference (role selected rfl) before

/-- The actual root-restored occupancy result and source reservation use this same public reference continuation at every outcome. -/
theorem native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (reserve : m Bool)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) (control : pqxdh.ServerState) (lookup : peer.CompletionLookup)
    (reference : RegistrationNativeRelatedFamily.Message) (occupied : Bool) (before : State n) :
    Prod.map id (restore roots) <$>
      (close (RegistrationNativePlatformServerMaterialFrontend.afterOccupancy (RegistrationNativePlatformServerMaterialState.adHash coins) (StateT.lift reserve)
        (service coins setup codec sealing hash signing helper writer roots) control lookup reference occupied)).run before =
      (RegistrationNativePlatformCompletionSdk.afterOccupancy (RegistrationNativePlatformCompletionSdk.nativeAdHash coins) (StateT.lift reserve)
        (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer)
        control (RegistrationServerReferenceSourceLookup.withRoot lookup (roots reference)) occupied).run (restore roots before) := by
  have publicEq := RegistrationServerReferenceSourceLookup.resume_public lookup (roots reference) occupied
  unfold RegistrationNativePlatformServerMaterialFrontend.afterOccupancy
    RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases selectedRun : lookup.resume occupied with
  | fail error | div =>
    simp only [selectedRun, rust_map_eq] at publicEq
    cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots reference)).resume occupied <;>
      simp_all only [reduceCtorEq, RustM.fail.injEq]
    all_goals simp only [pure_close, map_pure]; rfl
  | ok selectedResult => cases selectedResult with
    | Err previous =>
      cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots reference)).resume occupied with
      | fail error | div => simp [actual, selectedRun, rust_map_eq] at publicEq
      | ok answer => cases answer with
        | Ok pending => simp [actual, selectedRun, rust_map_eq, RegistrationPublicationKernelErasure.mapOk] at publicEq
        | Err previous => simp only [pure_close, map_pure]; rfl
    | Ok pending =>
      cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots reference)).resume occupied with
      | fail error | div => simp [actual, selectedRun, rust_map_eq] at publicEq
      | ok answer => cases answer with
        | Err previous => simp [actual, selectedRun, rust_map_eq, RegistrationPublicationKernelErasure.mapOk] at publicEq
        | Ok restored =>
          have same : RegistrationBoundKeySchedule.publicAd pending = RegistrationBoundKeySchedule.publicAd restored := by
            simpa only [selectedRun, actual, RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk,
              RustM.ok.injEq, core.result.Result.Ok.injEq] using publicEq.symm
          rw [bind_close, StateT.run_bind, lift_close]
          simp only [map_bind, bind_map_left]
          have changed := congrArg
            (fun work : StateT (Local n) m
                (RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) =>
              work.run before.2 >>= fun reached =>
                Prod.map id (restore roots) <$>
                  (close (RegistrationNativePlatformServerMaterialFrontend.afterResult (StateT.lift reserve)
                    (service coins setup codec sealing hash signing helper writer roots) control reference reached.1)).run
                    (before.1, reached.2))
            (RegistrationNativePlatformServerMaterialState.adHash_public coins pending restored same)
          simp only [StateT.run_map, bind_map_left] at changed
          rw [changed]
          unfold RegistrationNativePlatformServerMaterialState.adHash
            RegistrationNativePlatformCompletionSdk.nativeAdHash RegistrationNativePlatformServerSdk.adHash
            RegistrationNativePlatformServerCompletion.adHash RegistrationNativePlatformServerCompletion.adHashWith
            RegistrationServerAdHash.runWith
          cases requested : restored.request with
          | fail error =>
            simp only [StateT.run, bind_apply, pure_apply, pure_bind,
              RegistrationNativePlatformServerSdk.world, map_pure]
            exact result coins setup codec sealing hash reserve signing helper writer roots control reference (.fail error)
              (by intro initial impossible; cases impossible) before
          | div =>
            simp only [StateT.run, bind_apply, pure_apply, pure_bind,
              RegistrationNativePlatformServerSdk.world, map_pure]
            exact result coins setup codec sealing hash reserve signing helper writer roots control reference .div
              (by intro initial impossible; cases impossible) before
          | ok request =>
            simp only [StateT.run, bind_apply, pure_apply, pure_bind, bind_assoc,
              RegistrationNativePlatformServerSdk.world, bind_map_left]
            apply bind_congr
            rintro ⟨digest, current⟩
            have role : ∀ initial,
                restored.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) = .ok (.Ok initial) →
                  initial.pending = PqxdhInitialRatchetComplementarity.serverPending
                    (PqxdhRootTableInitialization.rootArray (roots reference)) := by
              intro initial resumed
              exact RegistrationServerReferenceSourceLookup.resume_role lookup (roots reference) occupied
                restored (RegistrationAuthenticationShared.digestArray digest) initial actual resumed
            have transported := result coins setup codec sealing hash reserve signing helper writer roots control reference
              (restored.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) role (before.1, current)
            cases resumed : restored.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
            | fail error | div => simpa only [resumed, StateT.run, restore, RegistrationServerReferenceRestore.restore] using transported
            | ok outcome => cases outcome <;> simpa only [resumed, StateT.run, restore, RegistrationServerReferenceRestore.restore] using transported

end BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy.native
