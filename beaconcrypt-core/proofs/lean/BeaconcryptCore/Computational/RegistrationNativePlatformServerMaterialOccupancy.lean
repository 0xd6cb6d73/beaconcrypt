-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
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
      (close (RegistrationNativePlatformServerMaterialFrontend.afterOccupancy (StateT.lift reserve)
        (service coins setup codec sealing hash signing helper writer roots) control lookup reference occupied)).run before =
      (RegistrationNativePlatformCompletionSdk.afterOccupancy (StateT.lift reserve)
        (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer)
        control (RegistrationServerReferenceSourceLookup.withRoot lookup (roots reference)) occupied).run (restore roots before) := by
  unfold RegistrationNativePlatformServerMaterialFrontend.afterOccupancy
  rw [← RegistrationServerReferenceSourceLookup.resume_public lookup (roots reference) occupied]
  cases actual : (RegistrationServerReferenceSourceLookup.withRoot lookup (roots reference)).resume occupied with
  | fail error =>
    simp only [RegistrationNativePlatformCompletionSdk.afterOccupancy, actual]
    change Prod.map id (restore roots) <$> (close (pure (RustM.fail error : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)))).run before = _
    rw [pure_close, map_pure]
    rfl
  | div =>
    simp only [RegistrationNativePlatformCompletionSdk.afterOccupancy, actual]
    change Prod.map id (restore roots) <$> (close (pure (RustM.div : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)))).run before = _
    rw [pure_close, map_pure]
    rfl
  | ok result => cases result with
    | Err previous =>
      simp only [RegistrationNativePlatformCompletionSdk.afterOccupancy, actual]
      change Prod.map id (restore roots) <$> (close (pure (RustM.ok none : RegistrationNativePlatformServerMaterialFrontend.Result (alloc.vec.Vec U8)))).run before = _
      rw [pure_close, map_pure]
      rfl
    | Ok selected =>
      simp only [RawCtxMaterialInterpretation.rust_map_ok, RegistrationPublicationKernelErasure.mapOk,
        RegistrationNativePlatformServerMaterialFrontend.afterResult, RegistrationNativePlatformCompletionSdk.afterOccupancy, actual]
      rw [bind_close, StateT.run_bind, lift_close]
      simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, map_bind, bind_map_left]
      apply bind_congr
      intro admitted
      cases admitted with
      | false => simp only [Bool.false_eq_true, ite_false, pure_close, map_pure]; rfl
      | true =>
        simp only [ite_true]
        exact RegistrationNativePlatformServerMaterialState.initial coins setup codec sealing hash signing helper writer roots
          control selected reference (RegistrationServerReferenceSourceLookup.resume_role lookup (roots reference) occupied selected actual) before

end BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialOccupancy.native
