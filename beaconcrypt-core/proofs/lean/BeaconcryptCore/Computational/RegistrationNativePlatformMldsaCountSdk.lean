-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountRules
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer

/-! Exact corrected SDK control composition for private ML count normalization. The source reads only retained control before the actual stateful pin callback; all reservations, moved handles, optional failures and external poststates remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformMldsaCountRules (Correct project)
open RegistrationNativePlatformPackedState (pack)
open RegistrationNativeMldsaCountServer (localProject serverProject)
open RegistrationNativePlatformCompletionSdk (Completion)
variable {n : Nat} {Platform Value Encoded : Type} {source : RegistrationNativeMldsa.Source}

private theorem local_idempotent (before : RegistrationServerRootCompiler.Local n) : localProject (localProject before) = localProject before := by
  simp only [localProject, RegistrationNativeMldsaWorldView.idempotent]
private theorem server_idempotent (before : RegistrationServerFrontendCompiler.State n) : serverProject (serverProject before) = serverProject before := by
  simp only [serverProject, local_idempotent]
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

/-- The actual SDK World lens retains both complete count equations and all external state. -/
theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (M source Platform) Value)
    (good : Correct localProject work) : Correct serverProject (RegistrationNativePlatformServerSdk.world work) := by
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, ({ before.1 with world := result.2.1 }, result.2.2))) <$> computation)
      (good.1 (before.1.world, before.2))
    simp only [pack, RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, Functor.map_map,
      Prod.map, id_eq, project, serverProject] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, ({ before.1 with world := result.2.1 }, result.2.2))) <$> computation)
      (good.2 (before.1.world, before.2))
    simp only [pack, RegistrationNativePlatformServerSdk.world, StateT.run, map_apply,
      RegistrationNativeMldsaCountMap.transform, simulateQ_map, Functor.map_map,
      Prod.map, id_eq, project, serverProject] at same ⊢
    exact same

private theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Correct (source := source) (Platform := Platform) (serverProject (n := n))
      (RegistrationNativePlatformServerSdk.commit published) := by
  constructor <;> intro before
  all_goals
    cases published with
    | fail error | div =>
      simp only [pack, RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
        RegistrationNativeMldsaCountMap.transform, simulateQ_pure, map_pure, project, Prod.map, id_eq, server_idempotent]
    | ok answer => cases answer <;>
      simp only [pack, RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
        RegistrationNativeMldsaCountMap.transform, simulateQ_pure, map_pure, project, Prod.map, id_eq, serverProject, local_idempotent]

/-- Actual source publication commit changes retained SDK control only. -/
theorem fromInitial (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Correct localProject (finish control initial))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Correct serverProject (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ (world _ (allowed control initial)) commit

/-- Every actual occupancy and reservation branch preserves the same checked count laws. -/
theorem afterOccupancy (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Correct serverProject reserve) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Correct localProject (finish control initial))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Correct serverProject (RegistrationNativePlatformCompletionSdk.afterOccupancy reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
  | ok answer => cases answer with
    | Err prior => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
    | Ok initial =>
      apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ reserved
      intro admitted
      cases admitted with
      | false => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
      | true => exact fromInitial finish allowed control initial

/-- Exact pin, lookup, size and occupancy failures preserve the same source control and platform state. -/
theorem afterPin (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Correct serverProject reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (presence : ∀ keyId, Correct serverProject (present keyId))
    (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Correct localProject (finish control initial))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Correct serverProject (RegistrationNativePlatformCompletionSdk.afterPin reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
  | ok optional => cases optional with
    | none => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
      | ok answer => cases answer with
        | Err prior => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
          | ok keyId =>
            dsimp only
            split
            · exact RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ (presence keyId)
                (afterOccupancy reserve reserved finish allowed control lookup)
            · exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _

private def readControl : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) pqxdh.ServerState :=
  fun before => pure (before.control, before)
private theorem read_correct : Correct (serverProject (n := n)) (readControl (source := source) (Platform := Platform)) := by
  constructor <;> intro before <;>
    simp only [pack, readControl, StateT.run, pure_apply, RegistrationNativeMldsaCountMap.transform,
      simulateQ_pure, map_pure, project, Prod.map, id_eq, serverProject, local_idempotent]

private theorem complete_shape
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (finish : Completion n (M source Platform) Encoded) (token : peer.ConsumedRegistration) (application : Slice U8) :
    RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application = (do
      let control ← readControl
      let selected ← pin
      RegistrationNativePlatformCompletionSdk.afterPin reserve present finish control token application selected) := by
  funext before previous
  simp only [RegistrationNativePlatformCompletionSdk.complete, readControl, bind_apply, get_apply, pure_apply, pure_bind]

/-- Actual completion reads only retained control before executing its stateful pin and lookup continuation. -/
theorem complete
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Correct serverProject pin) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Correct serverProject reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (presence : ∀ keyId, Correct serverProject (present keyId)) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Correct localProject (finish control initial))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Correct serverProject (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application) := by
  rw [complete_shape]
  apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ read_correct
  intro control
  exact RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ pinned
    (afterPin reserve reserved present presence finish allowed control token application)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_correct (handle : Nat) :
    Correct (serverProject (n := n)) (take (source := source) (Platform := Platform) handle) := by
  constructor <;> intro before
  all_goals
    cases found : before.1.sessions[handle]? with
    | none =>
      simp only [pack, take, RegistrationServerSdkSource.take, StateT.run, pure_apply, project, Prod.map, id_eq,
        serverProject, found, RegistrationNativeMldsaCountMap.transform, simulateQ_pure, map_pure, local_idempotent]
    | some stored => cases stored <;>
      simp only [pack, take, RegistrationServerSdkSource.take, StateT.run, pure_apply, project, Prod.map, id_eq,
        serverProject, found, RegistrationNativeMldsaCountMap.transform, simulateQ_pure, map_pure, local_idempotent]

private theorem build_shape
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (finish : Completion n (M source Platform) Encoded) (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application = (do
      let token ← take handle
      match token, application with
      | some token, some application => RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application
      | _, _ => pure (.ok none)) := by
  funext before previous
  simp only [RegistrationNativePlatformCompletionSdk.build, take, bind_apply, pure_apply, pure_bind, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk token current => cases token <;> cases application <;> rfl

/-- The complete actual SDK build retains moved-token, source pin, reservation and commit behavior under both count equations. -/
theorem build
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Correct serverProject pin) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (reserved : Correct serverProject reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M source Platform) Bool)
    (presence : ∀ keyId, Correct serverProject (present keyId)) (finish : Completion n (M source Platform) Encoded)
    (allowed : ∀ control initial, Correct localProject (finish control initial))
    (handle : Nat) (application : Option (Slice U8)) :
    Correct serverProject (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application) := by
  rw [build_shape]
  apply RegistrationNativePlatformMldsaCountRules.bind serverProject _ _ (take_correct handle)
  intro token
  cases token with
  | none => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
  | some token => cases application with
    | none => exact RegistrationNativePlatformMldsaCountRules.pure serverProject server_idempotent _
    | some application => exact complete pin pinned reserve reserved present presence finish allowed token application

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaCountSdk.build
