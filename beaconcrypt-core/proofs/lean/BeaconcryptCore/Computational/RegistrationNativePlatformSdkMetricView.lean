-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk
import BeaconcryptCore.Computational.RegistrationNativeServerViewBuild
/-! Literal moved-token, pin, occupancy, reservation and completion control transports the narrow native instrumentation view. The generic proof consumes only individual operation laws, retaining complete optional failure and common-monad poststates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView
open RegistrationServerFrontendCompiler (State)
open RegistrationServerMaterialSourceState (nativeView)
open RegistrationStateView (Stable pure_stable bind_stable)
open RegistrationNativeServerViewAccept (view_idempotent)
open RegistrationNativePlatformCompletionSdk (AdHash Completion)
variable {n : Nat} {Value Encoded : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The actual SDK World lens retains every control field under the literal Local view. -/
theorem world (work : StateT (RegistrationServerRootCompiler.Local n) m Value)
    (stable : Stable RegistrationServerRecordWorldSource.project work) :
    Stable nativeView (RegistrationNativePlatformServerSdk.world work) := by
  intro before
  have actual := congrArg (fun action => (fun result => (result.1,
    { nativeView before with world := result.2 })) <$> action) (stable before.world)
  simpa only [RegistrationNativePlatformServerSdk.world, StateT.run, Functor.map_map, nativeView,
    Prod.map_def, id_eq, Function.comp_def] using actual

private theorem commit (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Stable (nativeView (n := n)) (RegistrationNativePlatformServerSdk.commit (m := m) result) := by
  intro before
  cases result with
  | fail error | div => simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, nativeView,
      map_pure, Prod.map_def, id_eq, RegistrationNativeLocalView.project_idempotent]
  | ok result => cases result <;> simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, nativeView,
      map_pure, Prod.map_def, id_eq, RegistrationNativeLocalView.project_idempotent]

private theorem initial (finish : Completion n m Encoded)
    (stable : ∀ control pending, Stable RegistrationServerRecordWorldSource.project (finish control pending))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Stable nativeView (RegistrationNativePlatformCompletionSdk.fromInitial finish control pending) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_stable _ _ _ (world _ (stable control pending)) commit

private theorem after (deriveAd : AdHash n m)
    (adStable : ∀ pending, Stable nativeView (deriveAd pending)) (reserve : StateT (State n) m Bool) (finish : Completion n m Encoded)
    (reserveStable : Stable nativeView reserve)
    (finishStable : ∀ control pending, Stable RegistrationServerRecordWorldSource.project (finish control pending))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Stable nativeView (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_stable _ view_idempotent _
  | ok result => cases result with
    | Err previous => exact pure_stable _ view_idempotent _
    | Ok pending =>
      apply bind_stable _ _ _ (adStable pending)
      intro reply
      cases reply with
      | fail error | div => exact pure_stable _ view_idempotent _
      | ok result => cases result with
        | Err previous => exact pure_stable _ view_idempotent _
        | Ok prepared =>
          apply bind_stable _ _ _ reserveStable
          intro allowed
          cases allowed with
          | false => exact pure_stable _ view_idempotent _
          | true => exact initial finish finishStable control prepared

private theorem afterPin (deriveAd : AdHash n m)
    (adStable : ∀ pending, Stable nativeView (deriveAd pending)) (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool)
    (finish : Completion n m Encoded) (reserveStable : Stable nativeView reserve)
    (presentStable : ∀ keyId, Stable nativeView (present keyId))
    (finishStable : ∀ control pending, Stable RegistrationServerRecordWorldSource.project (finish control pending))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (reply : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Stable nativeView (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application reply) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases reply with
  | fail error | div => exact pure_stable _ view_idempotent _
  | ok result => cases result with
    | none => exact pure_stable _ view_idempotent _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_stable _ view_idempotent _
      | ok result => cases result with
        | Err previous => exact pure_stable _ view_idempotent _
        | Ok lookup =>
          dsimp only
          cases requested : lookup.request with
          | fail error | div => exact pure_stable _ view_idempotent _
          | ok keyId =>
            dsimp only
            split
            · exact bind_stable _ _ _ (presentStable keyId) (after deriveAd adStable reserve finish reserveStable finishStable control lookup)
            · exact pure_stable _ view_idempotent _

private def control : StateT (State n) m pqxdh.ServerState := fun before => pure (before.control, before)
private theorem control_stable : Stable nativeView (control (n := n) (m := m)) := by
  intro before
  simp only [control, StateT.run, map_pure, nativeView, Prod.map_def, id_eq, RegistrationNativeLocalView.project_idempotent]

omit [LawfulMonad m] in
private theorem bind_apply {S A B : Type} (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit [LawfulMonad m] in
private theorem get_apply {S : Type} (before : S) : (get : StateT S m S) before = pure (before, before) := rfl

private theorem complete (deriveAd : AdHash n m)
    (adStable : ∀ pending, Stable nativeView (deriveAd pending)) (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool) (finish : Completion n m Encoded)
    (pinStable : Stable nativeView pin) (reserveStable : Stable nativeView reserve)
    (presentStable : ∀ keyId, Stable nativeView (present keyId))
    (finishStable : ∀ control pending, Stable RegistrationServerRecordWorldSource.project (finish control pending))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Stable nativeView (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  have shape : RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application = (do
      let current ← control
      let reply ← pin
      RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish current token application reply) := by
    funext before
    simp only [RegistrationNativePlatformCompletionSdk.complete, bind_apply, get_apply, control, pure_bind]
  rw [shape]
  exact bind_stable _ _ _ control_stable (fun current =>
    bind_stable _ _ _ pinStable (afterPin deriveAd adStable reserve present finish reserveStable presentStable finishStable current token application))

/-- Actual moved-handle consumption and all later source SDK gates preserve the named instrumentation view. -/
theorem build (deriveAd : AdHash n m)
    (adStable : ∀ pending, Stable nativeView (deriveAd pending)) (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool) (finish : Completion n m Encoded)
    (pinStable : Stable nativeView pin) (reserveStable : Stable nativeView reserve)
    (presentStable : ∀ keyId, Stable nativeView (present keyId))
    (finishStable : ∀ control pending, Stable RegistrationServerRecordWorldSource.project (finish control pending))
    (handle : Nat) (application : Option (Slice U8)) :
    Stable nativeView (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  intro before
  unfold RegistrationNativePlatformCompletionSdk.build
  dsimp only [StateT.run]
  rw [RegistrationNativeServerViewBuild.take_view]
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk token current =>
    cases token with
    | none => simp only [Prod.map_def, id_eq, map_pure, view_idempotent]
    | some token => cases application with
      | none => simp only [Prod.map_def, id_eq, map_pure, view_idempotent]
      | some application => exact complete deriveAd adStable pin reserve present finish pinStable reserveStable presentStable finishStable token application current
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkMetricView.build
