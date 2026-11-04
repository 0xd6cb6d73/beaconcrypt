-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret

/-! Literal source Server publication preserves validity of every chronological signing receipt. The complete local/World lens and effectful writer are interpreted exactly; source hash-before-sign alignment is derived by the checked journal, and no complete-publication validity law is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerPublicationCached
open BeaconcryptCore.Refinement
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform Value Next : Type}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private def lens (work : StateT (RegistrationWorldSigning.State n) (StateT Platform ProbComp) Value) :
    StateT (Local n) (StateT Platform ProbComp) Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

private theorem lens_pure (value : Value) :
    lens (pure value : StateT (RegistrationWorldSigning.State n) (StateT Platform ProbComp) Value) = pure value := by
  funext before
  simp only [lens, StateT.run_pure, map_pure]
  rfl

private theorem lens_bind (work : StateT (RegistrationWorldSigning.State n) (StateT Platform ProbComp) Value)
    (next : Value → StateT (RegistrationWorldSigning.State n) (StateT Platform ProbComp) Next) :
    lens (work >>= next) = (lens work >>= fun value => lens (next value)) := by
  funext before previous
  simp only [lens, StateT.run, bind_apply, map_apply, map_bind, bind_map_left]
  rfl

private theorem lens_hom : Cslib.IsMonadHom (StateT (RegistrationWorldSigning.State n) (StateT Platform ProbComp))
    (StateT (Local n) (StateT Platform ProbComp)) lens := .mk' lens_pure lens_bind

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private def encoder
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) :
    StateT (RegistrationWorldSigning.State n) (StateT Platform ProbComp) (RustM (Option (alloc.vec.Vec U8))) :=
  StateT.lift (RegistrationNativePlatformSourceCompletion.encodeWith writer view)

private theorem encoder_frame
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) (before : RegistrationWorldSigning.State n) (previous : Platform)
    (result : (RustM (Option (alloc.vec.Vec U8)) × RegistrationWorldSigning.State n) × Platform)
    (supported : result ∈ support (((encoder writer view).run before).run previous)) :
    RegistrationNativePlatformJournalSafe.Frame before result.1.2 := by
  simp only [encoder, StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  exact ⟨rfl, le_refl _⟩

/-- Actual source dynamic response publication preserves the cached-history invariant at its exact Local and external poststates. -/
theorem program
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (pending : registration.ServerResponseHash) (before : Local n) (previous : Platform)
    (result : (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) × Local n) × Platform)
    (cached : RegistrationSigningShared.Cached (RegistrationWorldSigning.project before.world))
    (supported : result ∈ support (((RegistrationNativePlatformServerPublication.program
      (RegistrationNativePlatformServerCompletion.outgoing coins sign) (RegistrationNativePlatformSourceBuild.encode writer) pending).run before).run previous)) :
    RegistrationSigningShared.Cached (RegistrationWorldSigning.project result.1.2.world) := by
  have interpreted := RegistrationNativePlatformBuildInterpret.Publication.program (lens_hom (n := n))
    (fun query => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing (n := n) sign query)) (encoder writer) pending
  have outgoingEq : (fun query => lens (n := n) (Platform := Platform) (RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing (n := n) sign query))) =
      RegistrationNativePlatformServerCompletion.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) coins sign := by
    funext query before
    simp only [lens, RegistrationNativePlatformInterpret.state, RegistrationNativePlatformServerCompletion.outgoing,
      RegistrationNativePlatformServerCompletion.liftNative, RegistrationNativePlatformServerCompletion.nativeOutgoing,
      StateT.run, simulateQ_map]
  have encodeEq : (fun view => lens (encoder writer view)) = RegistrationNativePlatformSourceBuild.encode (n := n) writer := by
    funext view before previous
    simp only [lens, encoder, RegistrationNativePlatformSourceBuild.encode, StateT.run,
      lift_apply, map_apply, Functor.map_map]
    rfl
  rw [outgoingEq, encodeEq] at interpreted
  rw [← interpreted] at supported
  simp only [lens, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact RegistrationNativePlatformJournalCachedPublication.server sign (encoder writer) (encoder_frame writer) pending before.world cached previous inner called

end BeaconcryptCore.Computational.RegistrationNativePlatformServerPublicationCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublicationCached.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublicationCached.program
