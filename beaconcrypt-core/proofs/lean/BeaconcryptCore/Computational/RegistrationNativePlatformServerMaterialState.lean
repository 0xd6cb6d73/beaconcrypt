-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialFrontend
import BeaconcryptCore.Computational.RegistrationServerReferenceRestore
/-! Private interpretation restores the exact earlier root only at a source initializer. The executable frontend holds public one-use references while the complete Local World and platform effects stay threaded through the common outer monad. Native accounting is retained literally. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRootCompiler (Local)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePlatformServerMaterialFrontend (Service)
variable {n : Nat} {Value Next ι KemSK Reader Response E : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev State (n : Nat) := RegistrationServerMaterialFrontend.State × Local n

def restore (roots : Roots) (before : State n) : RegistrationServerFrontendCompiler.State n :=
  RegistrationServerReferenceRestore.restore roots before.1 before.2

def close (work : StateT RegistrationServerMaterialFrontend.State (StateT (Local n) m) Value) :
    StateT (State n) m Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2

noncomputable def pin (coins : QueryImpl unifSpec m) (current : session.ServerAuthenticationPin) :
    StateT (Local n) m (RustM (core.option.Option session.ServerAuthenticationPin)) := fun before =>
  (fun result => (result.1, { before with world := (result.2, before.world.2) })) <$>
    simulateQ coins ((RegistrationNativeServerPinRecompute.native current.binding current.public_key).run before.world.1)

noncomputable def service (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (_codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) : Service (StateT (Local n) m) (alloc.vec.Vec U8) := fun control initial reference => do
  modify (fun before => RegistrationNativePlatformPrivateKdfState.ratchetState
    (RegistrationNativePlatformPrivateKdfState.initialState before))
  RegistrationNativePlatformPairedServerService.knownStage sealing hash (RegistrationNativePlatformSourceBuild.write helper)
    (RegistrationNativePlatformServerCompletion.outgoing coins signing) (RegistrationNativePlatformSourceBuild.encode writer)
    (RegistrationNativePlatformPairedServerService.nativeEffects coins) control initial
    (PqxdhServerAuthKeySchedule.fromRoot setup.source (roots reference))

/-- Nested frontend/local interpretation retains the same value and common poststate through arbitrary adaptive continuations. -/
theorem bind_close (work : StateT RegistrationServerMaterialFrontend.State (StateT (Local n) m) Value)
    (next : Value → StateT RegistrationServerMaterialFrontend.State (StateT (Local n) m) Next) :
    close (work >>= next) = (close work >>= fun value => close (next value)) := by
  funext before
  simp only [close, StateT.run, StateT.monad_bind_def, StateT.bind, map_bind, bind_map_left]

omit [LawfulMonad m] in
private theorem bind_apply {S A B : Type} (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem lift_apply {S A : Type} (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

omit [LawfulMonad m] in
private theorem modify_apply {S : Type} (update : S → S) (before : S) :
    (modify update : StateT S m Unit) before = pure ((), update before) := rfl

private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit [LawfulMonad m] in
private theorem pure_apply {S A : Type} (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

/-- Pure frontend steps retain the complete private and platform state. -/
theorem pure_close (value : Value) (before : State n) :
    (close (pure value : StateT RegistrationServerMaterialFrontend.State (StateT (Local n) m) Value)).run before =
      pure (value, before) := by
  simp only [close, StateT.run, pure_apply, map_pure]

/-- An effectful frontend operation uses the same current private Local and retains its public reference state. -/
theorem lift_close (work : StateT (Local n) m Value) (before : State n) :
    (close (StateT.lift work)).run before =
      (fun result => (result.1, (before.1, result.2))) <$> work.run before.2 := by
  simp only [close, StateT.run, lift_apply, map_apply, Functor.map_map, Prod.map, id_eq]


/-- An actual reached source initializer uses the earlier private root and the same complete stateful material service, then commits exactly the public control/reply. -/
theorem initial (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sealing : record_effects.AeadSealRequest → StateT (Local n) m
      (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT (Local n) m RegistrationNativePlatformCommitment.HashReply)
    (signing : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (roots : Roots) (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf)
    (reference : RegistrationNativeRelatedFamily.Message)
    (role : pending.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray (roots reference))) (before : State n) :
    Prod.map id (restore roots) <$> (close (do
      let published ← StateT.lift (service coins setup codec sealing hash signing helper writer roots
        control (RegistrationBoundKeySchedule.publicInitial pending) reference)
      fun current => pure (RegistrationNativePlatformServerMaterialFrontend.finish published current))).run before =
      (RegistrationNativePlatformCompletionSdk.fromInitial
        (RegistrationNativePlatformSourceBuild.finishSource coins setup codec sealing hash signing helper writer)
        control pending).run (restore roots before) := by
  have world_run {A : Type} (work : StateT (Local n) m A) (current : RegistrationServerFrontendCompiler.State n) :
      (RegistrationNativePlatformServerSdk.world work).run current =
        (fun result => (result.1, { current with world := result.2 })) <$> work.run current.world := rfl
  rw [RegistrationNativePlatformCompletionSdk.fromInitial, StateT.run_bind, world_run]
  rw [RegistrationNativePlatformPairedServerService.finish_source coins setup codec sealing hash signing helper writer
    control pending (roots reference) role (restore roots before).world]
  simp only [close, StateT.run, bind_apply, lift_apply, service, modify_apply,
    pure_bind, map_bind, bind_map_left, Functor.map_map]
  simp only [map_apply, pure_apply, map_pure, bind_map_left]
  apply bind_congr
  rintro ⟨published, current⟩
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.bind_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.bind_close

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.pure_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.pure_close

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.lift_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.lift_close

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialState.initial
