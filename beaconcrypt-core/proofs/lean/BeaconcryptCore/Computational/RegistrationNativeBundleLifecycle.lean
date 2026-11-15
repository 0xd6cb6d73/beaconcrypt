-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleTerminal
/-! The literal native bundle program factors at its actual scalar sample, complete signing/publication and terminal phase update. Every result and failed writer prefix is retained. Individual actual callbacks discharge the restricted interpreter laws; no whole source-controller or successful-install premise is supplied. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativePlatformFrontend (interpret Work AllowedBundle)
variable {n : Nat} {I KemSK E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Front" => RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK))
local notation "Allowed" => AllowedBundle (E := E) (n := n) (KemSK := KemSK)
local notation "Legacy" => RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State

noncomputable def terminal (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) : Front (RustM (Option (alloc.vec.Vec U8))) :=
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending scalar))
      let _ ← RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
      pure (.ok (some finished.encoded))

theorem phase_work (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    RegistrationNativeLocalStatePatch.Work (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK)
      (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) index phase) := by
  intro owners env
  exact allQueriesSatisfy_pure _ _

theorem terminal_work (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :
    Work Allowed (terminal (E := E) (n := n) (KemSK := KemSK) index owner scalar published) := by
  cases published with
  | fail error | div => exact RegistrationNativePlatformFrontend.pure_work _ _
  | ok result => cases result with
    | Err previous => exact RegistrationNativePlatformFrontend.pure_work _ _
    | Ok finished =>
        unfold terminal
        apply RegistrationNativePlatformFrontend.bind_work _ _ _
          (RegistrationNativePlatformFrontend.legacy_work _ (phase_work index _))
        intro _
        apply RegistrationNativePlatformFrontend.bind_work _ _ _
          (RegistrationNativePlatformFrontend.legacy_work _ (RegistrationNativeLocalStatePatch.effect_work _))
        intro _
        exact RegistrationNativePlatformFrontend.pure_work _ _

noncomputable def publish {κ : Type} {base : OracleSpec κ}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) : Front (RustM (Option (alloc.vec.Vec U8))) := do
  let published ← RegistrationNativePlatformBeaconPublication.begin
    (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
    (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin
  terminal index owner scalar published

theorem publish_work (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) : Work Allowed (publish (E := E) (n := n) setup index owner scalar) :=
  RegistrationNativePlatformFrontend.bind_work _ _ _
    (RegistrationNativePlatformFrontend.publication_work setup index owner _ _ _ _) (terminal_work index owner scalar)

variable (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)

omit [LawfulMonad m] in
theorem get_bind (next : List (Owner source) → Front A) (before : Native) :
    (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (do let owners ← get; next owners)).run before =
      (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
        (next before.beacons)).run before := by
  rw [RegistrationNativePlatformFrontend.run_interpret, RegistrationNativePlatformFrontend.run_interpret]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]

theorem publish_interpret (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) :
    interpret (RegistrationNativePlatformExperiment.bundleHandler (n := n) coins setup checks representation created source writer)
      (publish setup index owner scalar) = (do
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner)
        (RegistrationNativeBundleInterpretation.encoder coins setup checks representation created writer)
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin
      interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
        (terminal index owner scalar published)) := by
  unfold publish
  rw [RegistrationNativePlatformFrontend.bind_interpret _ _
    (RegistrationNativePlatformFrontend.bundle_atomic coins setup checks representation created writer) _ _
    (terminal_work index owner scalar), RegistrationNativeBundleInterpretation.publication]

theorem fresh (index : Nat) (owner : Owner source) (before : Native)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .fresh) :
    (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.program E setup source index)).run before =
      ((do
        let scalar ← interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
          (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
            (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))
        interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
          (publish setup index owner scalar)) : RegistrationNativePlatformExperiment.M n KemSK source m _).run before := by
  unfold RegistrationNativePlatformGenericBundle.program RegistrationNativePlatformGenericBundle.bundle
  rw [get_bind]
  simp only [selected, phase]
  have law := congrArg (fun action : RegistrationNativePlatformExperiment.M n KemSK source m (RustM (Option (alloc.vec.Vec U8))) => action.run before)
    (RegistrationNativePlatformFrontend.bind_interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (AllowedBundle (E := E) (n := n) (KemSK := KemSK))
      (RegistrationNativePlatformFrontend.bundle_atomic coins setup checks representation created writer)
      (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))
      (publish setup index owner) (publish_work setup index owner))
  refine Eq.trans ?_ law
  apply congrArg (fun work : Front (RustM (Option (alloc.vec.Vec U8))) =>
    (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before)
  apply bind_congr
  intro scalar
  unfold publish
  apply bind_congr
  intro published
  cases published with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

omit [LawfulMonad m] in
theorem with_coins (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .freshWithCoins scalar) :
    (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.program E setup source index)).run before =
      (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
        (publish setup index owner scalar)).run before := by
  unfold RegistrationNativePlatformGenericBundle.program RegistrationNativePlatformGenericBundle.bundle
  rw [get_bind]
  simp only [selected, phase, pure_bind]
  apply congrArg (fun work : Front (RustM (Option (alloc.vec.Vec U8))) =>
    (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before)
  unfold publish
  apply bind_congr
  intro published
  cases published with
  | fail error | div => rfl
  | ok result => cases result <;> rfl


def value (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) : RustM (Option (alloc.vec.Vec U8)) :=
  match published with
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok none
  | .ok (.Ok finished) => .ok (some finished.encoded)

def after (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (before : Native) : Native :=
  match published with
  | .ok (.Ok finished) => RegistrationNativeBundleTerminal.after index owner finished.pending scalar before
  | _ => before

theorem terminal_install (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8)) :
    terminal (E := E) (n := n) (KemSK := KemSK) index owner scalar (.ok (.Ok finished)) =
      RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBundleTerminal.install index owner scalar finished) := by
  simp only [terminal, RegistrationNativeBundleTerminal.install,
    RegistrationNativePlatformGenericBundle.liftLegacy_bind, RegistrationNativePlatformGenericBundle.liftLegacy_pure]

theorem terminal_exact (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (before : Native)
    (ready : RegistrationNativeBundleTerminal.Ready before.server.world.world.1 owner.worldOwner) :
    (interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (terminal index owner scalar published)).run before = pure (value published, after index owner scalar published before) := by
  cases published with
  | fail error | div => simp only [terminal, RegistrationNativePlatformFrontend.pure_interpret, StateT.run_pure, value, after]
  | ok result => cases result with
    | Err previous => simp only [terminal, RegistrationNativePlatformFrontend.pure_interpret, StateT.run_pure, value, after]
    | Ok finished =>
        rw [terminal_install]
        exact RegistrationNativeBundleTerminal.install_interpret coins setup checks representation created writer index owner scalar finished before ready

end BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.phase_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.phase_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.terminal_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.terminal_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.publish_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.publish_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.get_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.get_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.publish_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.publish_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.with_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.terminal_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.terminal_install

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.terminal_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleLifecycle.terminal_exact
