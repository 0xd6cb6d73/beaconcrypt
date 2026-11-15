-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxPin
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
/-! The literal SDK controller commutes with physical hash restoration at each callback and pure control step. Its stored independent source roots remain auxiliary state for the joint-Ed reduction; this is not the root-hiding confidentiality client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling
open RegistrationServerFrontendCompiler (State)
open RegistrationNativePlatformCtxRunner (M Full interpret)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {Platform A B Encoded : Type}

abbrev Native (n : Nat) (Platform : Type) := StateT (State n) (StateT Platform ProbComp)

def replace (cache : RegistrationNativePlatformCtxBackend.Cache) (before : State n) : State n :=
  {before with
    world := RegistrationNativePlatformCtxLocal.attach before.world (RegistrationNativePlatformCtxCacheFrame.replace cache before.world.world.1)}

def realize (before : Full (State n) Platform) : State n × Platform := (replace before.2.1 before.1.1, before.1.2)

def Coupled (left : M (State n) Platform A) (right : Native n Platform A) : Prop :=
  ∀ before : Full (State n) Platform, Prod.map id realize <$> (interpret left).run before = (pack right).run (realize before)

/-- Pure results retain the exact physical source state. -/
theorem pure_source (value : A) : Coupled (pure value : M (State n) Platform A) (pure value) := by
  intro before
  rw [RegistrationNativePlatformCtxRunner.pure_run, RegistrationNativePlatformPackedState.pure_pack]
  simp only [StateT.run_pure, map_pure]
  rfl

/-- Individual callback couplings compose through arbitrary source continuations. -/
theorem bind_source (left : M (State n) Platform A) (right : Native n Platform A)
    (nextLeft : A → M (State n) Platform B) (nextRight : A → Native n Platform B)
    (first : Coupled left right) (later : ∀ value, Coupled (nextLeft value) (nextRight value)) :
    Coupled (left >>= nextLeft) (right >>= nextRight) := by
  intro before
  rw [RegistrationNativePlatformCtxRunner.bind_run, RegistrationNativePlatformPackedState.bind_pack]
  simp only [StateT.run_bind, map_bind]
  rw [← first before, bind_map_left]
  apply bind_congr
  intro result
  exact later result.1 result.2

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

/-- Publication commits modify the same control field on every actual Rust branch. -/
theorem commit_source (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Coupled (RegistrationNativePlatformServerSdk.commit result : M (State n) Platform _)
      (RegistrationNativePlatformServerSdk.commit result) := by
  intro before
  cases result with
  | fail error => simp only [RegistrationNativePlatformServerSdk.commit, interpret, StateT.run,
      state_pure_apply, simulateQ_pure, map_pure, pack, Prod.map_def, id_eq]
  | div => simp only [RegistrationNativePlatformServerSdk.commit, interpret, StateT.run,
      state_pure_apply, simulateQ_pure, map_pure, pack, Prod.map_def, id_eq]
  | ok result => cases result <;>
      simp only [RegistrationNativePlatformServerSdk.commit, interpret, StateT.run,
        state_pure_apply, simulateQ_pure, map_pure, pack, Prod.map_def, id_eq] <;> rfl

/-- Reading only actual public control is unaffected by private physical cache restoration. -/
theorem control_source :
    Coupled ((fun before => pure (before.control, before)) : M (State n) Platform pqxdh.ServerState)
      (fun before => pure (before.control, before)) := by
  intro before
  simp only [interpret, StateT.run, state_pure_apply, simulateQ_pure, map_pure, pack, Prod.map_def, id_eq]
  rfl

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

private theorem take_replace (cache : RegistrationNativePlatformCtxBackend.Cache) (handle : Nat) (before : State n) :
    RegistrationServerSdkSource.take handle (replace cache before) =
      ((RegistrationServerSdkSource.take handle before).1, replace cache (RegistrationServerSdkSource.take handle before).2) := by
  unfold RegistrationServerSdkSource.take
  simp only [replace]
  cases before.sessions[handle]? with
  | none => rfl
  | some result => cases result <;> rfl

section Controller
variable (deriveAdLeft : RegistrationNativePlatformCompletionSdk.AdHash n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)))
variable (deriveAdRight : RegistrationNativePlatformCompletionSdk.AdHash n (StateT Platform ProbComp))
variable (ad : ∀ pending, Coupled (deriveAdLeft pending) (deriveAdRight pending))
variable (pinLeft : M (State n) Platform (RustM (core.option.Option session.ServerAuthenticationPin)))
variable (pinRight : Native n Platform (RustM (core.option.Option session.ServerAuthenticationPin)))
variable (reserveLeft : M (State n) Platform Bool) (reserveRight : Native n Platform Bool)
variable (presentLeft : U64 → M (State n) Platform Bool) (presentRight : U64 → Native n Platform Bool)
variable (finishLeft : RegistrationNativePlatformCompletionSdk.Completion n (StateT Platform (OracleComp RegistrationNativePlatformCtxBackend.Spec)) Encoded)
variable (finishRight : RegistrationNativePlatformCompletionSdk.Completion n (StateT Platform ProbComp) Encoded)
variable (pin : Coupled pinLeft pinRight) (reserve : Coupled reserveLeft reserveRight)
variable (present : ∀ keyId, Coupled (presentLeft keyId) (presentRight keyId))
variable (finish : ∀ control pending, Coupled (RegistrationNativePlatformServerSdk.world (finishLeft control pending))
    (RegistrationNativePlatformServerSdk.world (finishRight control pending)))

include finish in
/-- The actual source completion commits the same returned state after its same physical stage. -/
theorem fromInitial_source (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Coupled (RegistrationNativePlatformCompletionSdk.fromInitial finishLeft control pending)
      (RegistrationNativePlatformCompletionSdk.fromInitial finishRight control pending) := by
  exact bind_source _ _ _ _ (finish control pending) (fun result => commit_source result)

include ad reserve finish in
/-- Reservation and each completion-lookup outcome retain the actual reached state. -/
theorem afterOccupancy_source (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Coupled (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAdLeft reserveLeft finishLeft control lookup occupied)
      (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAdRight reserveRight finishRight control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error => exact pure_source _
  | div => exact pure_source _
  | ok result => cases result with
    | Err previous => exact pure_source _
    | Ok pending =>
      apply bind_source _ _ _ _ (ad pending)
      intro hashed
      cases hashed with
      | fail error | div => exact pure_source _
      | ok answer => cases answer with
        | Err previous => exact pure_source _
        | Ok initial =>
          apply bind_source _ _ _ _ reserve
          intro admitted
          cases admitted
          · exact pure_source _
          · exact fromInitial_source finishLeft finishRight finish control initial

include ad reserve present finish in
/-- The exact lookup, public preflight and occupancy branches introduce no hidden cache dependence. -/
theorem afterPin_source (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Coupled (RegistrationNativePlatformCompletionSdk.afterPin deriveAdLeft reserveLeft presentLeft finishLeft control token application current)
      (RegistrationNativePlatformCompletionSdk.afterPin deriveAdRight reserveRight presentRight finishRight control token application current) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases current with
  | fail error => exact pure_source _
  | div => exact pure_source _
  | ok result => cases result with
    | none => exact pure_source _
    | some current =>
      dsimp only
      cases peer.begin_completion_lookup control current token application with
      | fail error => exact pure_source _
      | div => exact pure_source _
      | ok result => cases result with
        | Err previous => exact pure_source _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error => exact pure_source _
          | div => exact pure_source _
          | ok keyId =>
            dsimp only
            split
            · apply bind_source _ _ _ _ (present keyId)
              intro occupied
              exact afterOccupancy_source (deriveAdLeft := deriveAdLeft) (deriveAdRight := deriveAdRight) (ad := ad) reserveLeft reserveRight finishLeft finishRight reserve finish control lookup occupied
            · exact pure_source _

include ad pin reserve present finish in
/-- The complete actual SDK finish gate preserves full native and platform state under the physical interpretation. -/
theorem complete_source (token : peer.ConsumedRegistration) (application : Slice U8) :
    Coupled (RegistrationNativePlatformCompletionSdk.complete deriveAdLeft pinLeft reserveLeft presentLeft finishLeft token application)
      (RegistrationNativePlatformCompletionSdk.complete deriveAdRight pinRight reserveRight presentRight finishRight token application) := by
  rw [complete_control, complete_control]
  apply bind_source _ _ _ _ control_source
  intro control
  apply bind_source _ _ _ _ pin
  intro current
  exact afterPin_source (deriveAdLeft := deriveAdLeft) (deriveAdRight := deriveAdRight) (ad := ad) reserveLeft reserveRight presentLeft presentRight finishLeft finishRight reserve present finish control token application current

include ad pin reserve present finish in
/-- The literal SDK build moves its token before all later failures and retains the exact same source/controller state. -/
theorem build_source (handle : Nat) (application : Option (Slice U8)) :
    Coupled (RegistrationNativePlatformCompletionSdk.build deriveAdLeft pinLeft reserveLeft presentLeft finishLeft handle application)
      (RegistrationNativePlatformCompletionSdk.build deriveAdRight pinRight reserveRight presentRight finishRight handle application) := by
  intro before
  have physicalTake := take_replace before.2.1 handle before.1.1
  cases taken : RegistrationServerSdkSource.take handle before.1.1 with
  | mk selected current =>
    rw [taken] at physicalTake
    cases selected with
    | none =>
      simp only [interpret, RegistrationNativePlatformCompletionSdk.build, StateT.run, realize,
        taken, physicalTake, state_pure_apply, simulateQ_pure, map_pure, pack, Prod.map_def, id_eq]
    | some token => cases application with
      | none =>
        simp only [interpret, RegistrationNativePlatformCompletionSdk.build, StateT.run, realize,
          taken, physicalTake, state_pure_apply, simulateQ_pure, map_pure, pack, Prod.map_def, id_eq]
      | some application =>
        have same := complete_source (deriveAdLeft := deriveAdLeft) (deriveAdRight := deriveAdRight) (ad := ad) pinLeft pinRight reserveLeft reserveRight presentLeft presentRight finishLeft finishRight
          pin reserve present finish token application ((current, before.1.2), before.2)
        simpa only [interpret, RegistrationNativePlatformCompletionSdk.build, StateT.run, realize,
          taken, physicalTake, pack] using same
end Controller
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.pure_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.bind_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.commit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.commit_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.control_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.control_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.fromInitial_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.fromInitial_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.afterOccupancy_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.afterOccupancy_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.afterPin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.afterPin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkCoupling.build_source
