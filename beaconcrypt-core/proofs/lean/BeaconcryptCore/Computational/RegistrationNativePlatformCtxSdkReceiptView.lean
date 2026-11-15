-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk
/-! The literal SDK build ignores earlier raw ML receipt payloads while preserving moved-token effects, control, all remaining native state, and the same persistent platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView
open BeaconcryptCore.Refinement
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCtxRunner (M)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {Platform A B Encoded : Type}

def serverView (before : State n) : State n :=
  {before with world := RegistrationNativePlatformIdentityReceiptView.view before.world}

def view (before : State n × Platform) : State n × Platform := (serverView before.1, before.2)

def Stable (work : M (State n) Platform A) : Prop :=
  RegistrationNativePlatformViewStable.Stable view (pack work)

private theorem idempotent (before : State n × Platform) : view (view before) = view before := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Pure SDK outcomes retain every projected state coordinate. -/
theorem pure_stable (value : A) : Stable (pure value : M (State n) Platform A) := by
  unfold Stable
  rw [RegistrationNativePlatformPackedState.pure_pack]
  exact RegistrationNativePlatformViewStable.pure_stable view idempotent value

/-- Adaptive source sequencing keeps the reached platform and projected SDK state. -/
theorem bind_stable (work : M (State n) Platform A) (next : A → M (State n) Platform B)
    (first : Stable work) (following : ∀ value, Stable (next value)) : Stable (work >>= next) := by
  unfold Stable at *
  rw [RegistrationNativePlatformPackedState.bind_pack]
  exact RegistrationNativePlatformViewStable.bind_stable view _ _ first following

/-- Lifting an actual Local source callback retains every outer SDK field and external poststate. -/
theorem world_stable (work : M (Local n) Platform A)
    (law : RegistrationNativePlatformCtxReceiptView.Stable work) :
    Stable (RegistrationNativePlatformCtxSdk.world work) := by
  rintro ⟨before, previous⟩
  have same := congrArg (fun distribution => (fun result =>
    (result.1, ({before with world := result.2.1}, result.2.2))) <$> distribution) (law (before.world, previous))
  simpa only [RegistrationNativePlatformCtxSdk.world, RegistrationNativePlatformServerSdk.world,
    pack, StateT.run, state_map_apply, Functor.map_map,
    RegistrationNativePlatformCtxReceiptView.view, view, serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq] using same

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

/-- Every source commitment branch changes only its actual retained control field. -/
theorem commit_stable (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Stable (RegistrationNativePlatformServerSdk.commit result : M (State n) Platform _) := by
  rintro ⟨before, previous⟩
  cases result with
  | fail error => simp only [RegistrationNativePlatformServerSdk.commit, pack, StateT.run,
      state_pure_apply, map_pure, view, serverView, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]
  | div => simp only [RegistrationNativePlatformServerSdk.commit, pack, StateT.run,
      state_pure_apply, map_pure, view, serverView, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]
  | ok result => cases result <;>
      simp only [RegistrationNativePlatformServerSdk.commit, pack, StateT.run,
        state_pure_apply, map_pure, view, Prod.map_def, id_eq] <;> rfl

/-- Reading actual public control cannot inspect the erased receipt bytes. -/
theorem control_stable :
    Stable ((fun before => pure (before.control, before)) : M (State n) Platform pqxdh.ServerState) := by
  rintro ⟨before, previous⟩
  simp only [pack, StateT.run, state_pure_apply, map_pure, view, serverView,
    RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

private theorem complete_control {m : Type → Type} [Monad m] [LawfulMonad m]
    (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n m)
    (pin : StateT (State n) m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (State n) m Bool) (present : U64 → StateT (State n) m Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n m Encoded)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application = (do
      let control ← (fun before => pure (before.control, before) : StateT (State n) m pqxdh.ServerState)
      let current ← pin
      RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application current) := by
  funext before
  simp only [RegistrationNativePlatformCompletionSdk.complete, state_bind_apply, state_get_apply, pure_bind]


private theorem take_view (handle : Nat) (before : State n) :
    RegistrationServerSdkSource.take handle (serverView before) =
      ((RegistrationServerSdkSource.take handle before).1, serverView (RegistrationServerSdkSource.take handle before).2) := by
  unfold RegistrationServerSdkSource.take
  simp only [serverView]
  cases before.sessions[handle]? with
  | none => rfl
  | some result => cases result <;> rfl

section Controller
variable (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)))
variable (ad_law : ∀ pending, Stable (deriveAd pending))
variable (pin : M (State n) Platform (RustM (core.option.Option session.ServerAuthenticationPin)))
variable (reserve : M (State n) Platform Bool) (present : U64 → M (State n) Platform Bool)
variable (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
variable (pin_law : Stable pin) (reserve_law : Stable reserve)
variable (present_law : ∀ keyId, Stable (present keyId))
variable (finish_law : ∀ control pending, Stable (RegistrationNativePlatformServerSdk.world (finish control pending)))

include finish_law in
/-- The literal completion commits the same projected returned state. -/
theorem fromInitial_stable (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Stable (RegistrationNativePlatformCompletionSdk.fromInitial finish control pending) :=
  bind_stable _ _ (finish_law control pending) (fun result => commit_stable result)

include ad_law reserve_law finish_law in
/-- Reservation and every completion-lookup failure retain their actual poststate. -/
theorem afterOccupancy_stable (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Stable (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error => exact pure_stable _
  | div => exact pure_stable _
  | ok result => cases result with
    | Err previous => exact pure_stable _
    | Ok pending =>
      apply bind_stable _ _ (ad_law pending)
      intro hashed
      cases hashed with
      | fail error | div => exact pure_stable _
      | ok answer => cases answer with
        | Err previous => exact pure_stable _
        | Ok initial =>
          apply bind_stable _ _ reserve_law
          intro admitted
          cases admitted
          · exact pure_stable _
          · exact fromInitial_stable finish finish_law control initial

include ad_law reserve_law present_law finish_law in
/-- Actual pin lookup, preflight and occupancy use no earlier receipt payloads. -/
theorem afterPin_stable (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Stable (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application current) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases current with
  | fail error => exact pure_stable _
  | div => exact pure_stable _
  | ok result => cases result with
    | none => exact pure_stable _
    | some current =>
      dsimp only
      cases peer.begin_completion_lookup control current token application with
      | fail error => exact pure_stable _
      | div => exact pure_stable _
      | ok result => cases result with
        | Err previous => exact pure_stable _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error => exact pure_stable _
          | div => exact pure_stable _
          | ok keyId =>
            dsimp only
            split
            · apply bind_stable _ _ (present_law keyId)
              intro occupied
              exact afterOccupancy_stable (deriveAd := deriveAd) (ad_law := ad_law) reserve finish reserve_law finish_law control lookup occupied
            · exact pure_stable _

include ad_law pin_law reserve_law present_law finish_law in
/-- The complete actual finish gate retains the same projected SDK and external state. -/
theorem complete_stable (token : peer.ConsumedRegistration) (application : Slice U8) :
    Stable (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  rw [complete_control]
  apply bind_stable _ _ control_stable
  intro control
  apply bind_stable _ _ pin_law
  intro current
  exact afterPin_stable (deriveAd := deriveAd) (ad_law := ad_law) reserve present finish reserve_law present_law finish_law control token application current

include ad_law pin_law reserve_law present_law finish_law in
/-- Taking the actual linear token precedes every later branch, including failed completion. -/
theorem build_stable (handle : Nat) (application : Option (Slice U8)) :
    Stable (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  rintro ⟨before, previous⟩
  have moved := take_view handle before
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk selected current =>
    rw [taken] at moved
    cases selected with
    | none =>
      simp only [pack, RegistrationNativePlatformCompletionSdk.build, StateT.run,
        view, taken, moved, state_pure_apply, map_pure, Prod.map_def, id_eq]
      rfl
    | some token => cases application with
      | none =>
        simp only [pack, RegistrationNativePlatformCompletionSdk.build, StateT.run,
          view, taken, moved, state_pure_apply, map_pure, Prod.map_def, id_eq]
        rfl
      | some application =>
        have same := complete_stable (deriveAd := deriveAd) (ad_law := ad_law) pin reserve present finish pin_law reserve_law present_law finish_law token application (current, previous)
        simpa only [pack, RegistrationNativePlatformCompletionSdk.build, StateT.run,
          view, taken, moved] using same
end Controller
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.pure_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.pure_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.bind_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.bind_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.world_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.world_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.commit_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.commit_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.control_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.control_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.fromInitial_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.fromInitial_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.afterOccupancy_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.afterOccupancy_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.afterPin_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.afterPin_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.complete_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.complete_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.build_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView.build_stable
