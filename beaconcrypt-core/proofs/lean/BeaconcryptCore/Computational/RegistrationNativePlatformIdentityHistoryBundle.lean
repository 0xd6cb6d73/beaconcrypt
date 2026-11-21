-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun

/-! The entire actual effectful opaque bundle ignores earlier raw Ed signature slots, from owner lookup and supplied/random one-time dispatch through the source writer and lifecycle commit. Current signatures, every failed branch, all other owner fields and the complete shared P state remain exact. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativePlatformIdentityProgram (M)
open RegistrationNativePlatformIdentityHistoryView (Stable pack view)
variable {n : Nat} {I KemSK Auxiliary Platform E Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem pure_stable (placeholder : Ed25519Signature) (value : Value) :
    Stable placeholder (pure value : M n KemSK Auxiliary Platform source Value) := by
  rintro ⟨⟨before, env⟩, platform⟩
  simp only [pack, StateT.run, pure_apply, map_pure, view, Prod.map_def, id_eq,
    RegistrationNativeIdentityHistoryLifecycle.owners_idempotent]

private theorem pack_bind (work : M n KemSK Auxiliary Platform source Value)
    (next : Value → M n KemSK Auxiliary Platform source Next) :
    pack (work >>= next) = (pack work >>= fun value => pack (next value)) := by
  funext before
  simp only [pack, StateT.run, bind_apply, map_bind, bind_map_left]

private theorem bind_stable (placeholder : Ed25519Signature) (work : M n KemSK Auxiliary Platform source Value)
    (next : Value → M n KemSK Auxiliary Platform source Next)
    (initial : Stable placeholder work) (following : ∀ value, Stable placeholder (next value)) :
    Stable placeholder (work >>= next) := by
  change RegistrationNativePlatformViewStable.Stable (view placeholder) (pack (work >>= next))
  rw [pack_bind]
  exact RegistrationNativePlatformViewStable.bind_stable _ _ _ initial following

private theorem effect_stable (placeholder : Ed25519Signature) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable placeholder (RegistrationNativePlatformIdentityProgram.native
      (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query) :
        M n KemSK Auxiliary Platform source _) := by
  apply RegistrationNativePlatformIdentityHistoryView.native
  rintro ⟨before, env⟩
  simp only [RegistrationNativeIdentityHistoryView.pack, RegistrationNativeIdentityFrontend.effect, StateT.run,
    lift_apply, map_apply, Functor.map_map, RegistrationNativeIdentityHistoryView.project, Prod.map_def, id_eq,
    RegistrationNativeIdentityHistoryLifecycle.owners_idempotent]

/-- Every actual publication outcome keeps the private history view through its real phase/owner-slot commit. -/
theorem next (placeholder : Ed25519Signature) (index : Nat) (before : RegistrationNativeIdentityFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (result : RegistrationNativePlatformIdentityBundle.Reply) :
    Stable placeholder (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) index before oneTime result) := by
  cases result with
  | fail error | div => exact pure_stable placeholder _
  | ok result => cases result with
    | Err error => exact pure_stable placeholder _
    | Ok published =>
      exact bind_stable placeholder _ _
        (RegistrationNativePlatformIdentityHistoryView.native placeholder _ (RegistrationNativeIdentityHistoryLifecycle.phase_stable placeholder _ _))
        (fun _ => bind_stable placeholder _ _ (effect_stable placeholder _) (fun _ => pure_stable placeholder _))

/-- The source writer and native phase commit retain the full platform poststate while ignoring earlier signature slots. -/
theorem bundled (placeholder : Ed25519Signature) (setup : Setup base KemSK) (index : Nat)
    (before : RegistrationNativeIdentityFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Stable placeholder (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index before oneTime writer) := by
  unfold RegistrationNativePlatformIdentityBundle.bundled
  exact bind_stable placeholder _ _
    (RegistrationNativePlatformIdentityHistoryView.program placeholder setup index before writer _)
    (RegistrationNativePlatformIdentityHistoryBundle.next placeholder index before oneTime)

private theorem captured (placeholder : Ed25519Signature) (setup : Setup base KemSK) (index : Nat)
    (before : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index
      (RegistrationNativeIdentityHistoryView.owner placeholder before) writer =
      RegistrationNativePlatformIdentityBundleRun.start setup index before writer := rfl

/-- Supplied and randomly sampled one-time dispatch retain the same actual source behavior under the prior-history view. -/
theorem start (placeholder : Ed25519Signature) (setup : Setup base KemSK) (index : Nat)
    (before : RegistrationNativeIdentityFrontend.Owner source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Stable placeholder (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index before writer) := by
  cases phase : before.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact bind_stable placeholder _ _
      (RegistrationNativePlatformIdentityHistoryView.native placeholder _ (RegistrationNativeIdentityHistoryLifecycle.sample_stable placeholder _))
      (fun oneTime => bundled placeholder setup index before oneTime writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using
      bundled (n := n) (Auxiliary := Auxiliary) placeholder setup index before scalar writer
  | initSent pending scalar | established completed | aborted aborted =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase] using
      (pure_stable (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) (Platform := Platform) placeholder (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- The full actual stateful bundle, including failed lookup and failed writers, is independent of earlier raw signature slots. -/
theorem bundle (placeholder : Ed25519Signature) (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Stable placeholder (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  rintro ⟨⟨before, env⟩, platform⟩
  cases found : before[index]? with
  | none =>
    have viewed : (RegistrationNativeIdentityHistoryView.owners placeholder before)[index]? = none := by
      simp only [RegistrationNativeIdentityHistoryView.owners, List.getElem?_map, found, Option.map_none]
    simp only [pack, RegistrationNativePlatformIdentityBundleRun.bundle, StateT.run, bind_apply,
      get_apply, pure_apply, pure_bind, found, view, viewed, map_pure, Prod.map_def, id_eq,
      RegistrationNativeIdentityHistoryLifecycle.owners_idempotent]
  | some selected =>
    have viewed : (RegistrationNativeIdentityHistoryView.owners placeholder before)[index]? =
        some (RegistrationNativeIdentityHistoryView.owner placeholder selected) := by
      simp only [RegistrationNativeIdentityHistoryView.owners, List.getElem?_map, found, Option.map_some]
    have actual := start (n := n) (Auxiliary := Auxiliary) placeholder setup index selected writer ((before, env), platform)
    simpa only [pack, RegistrationNativePlatformIdentityBundleRun.bundle, StateT.run, bind_apply,
      get_apply, pure_apply, pure_bind, found, view, viewed, captured] using actual

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.next
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.bundled
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryBundle.bundle
