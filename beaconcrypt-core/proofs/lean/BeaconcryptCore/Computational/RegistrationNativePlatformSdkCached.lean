-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk

/-! Actual corrected SDK control preserves cached native signing receipts through the same source pin, occupancy, reservation and completion calls. Each concrete leaf must establish its actual operational cache invariant; no private-table, generated-key or authentication conclusion is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached
open RegistrationNativePlatformCompletionSdk (AdHash Completion)
variable {n : Nat} {Platform Value Next Encoded State : Type}

def localProject (before : RegistrationServerRootCompiler.Local n) := (before.world.2, before.world.1.primitive.2)

def serverProject (before : RegistrationServerFrontendCompiler.State n) := (before.world.world.2, before.world.world.1.primitive.2)

def Keeps (cache : State → RegistrationSigningShared.State)
    (work : StateT State (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, RegistrationSigningShared.Cached (cache before) →
    result ∈ support ((work.run before).run previous) → RegistrationSigningShared.Cached (cache result.1.2)

private theorem pure_keeps (cache : State → RegistrationSigningShared.State) (value : Value) :
    Keeps (Platform := Platform) cache (pure value) := by
  intro before previous result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps (cache : State → RegistrationSigningShared.State)
    (work : StateT State (StateT Platform ProbComp) Value)
    (next : Value → StateT State (StateT Platform ProbComp) Next)
    (first : Keeps cache work) (rest : ∀ value, Keeps cache (next value)) : Keeps cache (work >>= next) := by
  intro before previous result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first before previous middle prior called) continued

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

/-- The actual SDK World lens retains cached signing receipts and the literal external poststate. -/
theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Value)
    (allowed : Keeps localProject work) : Keeps serverProject (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result prior supported
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact allowed before.world previous inner prior called

/-- Pure successful and failed source publication commit retains the signing projection exactly. -/
theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (Platform := Platform) (serverProject (n := n)) (RegistrationNativePlatformServerSdk.commit published) := by
  intro before previous result prior supported
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact prior
  | ok answer => cases answer <;>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported <;>
    cases supported <;> exact prior

/-- Actual source completion and commit preserve cached signing receipts. -/
theorem fromInitial (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localProject (finish control initial))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps serverProject (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_keeps serverProject _ _ (world _ (allowed control initial)) (commit)

/-- Every occupancy and reservation branch preserves cached signing receipts through the actual source continuation. -/
theorem afterOccupancy (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverProject (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverProject reserve) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localProject (finish control initial))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps serverProject (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps serverProject _
  | ok answer => cases answer with
    | Err prior => exact pure_keeps serverProject _
    | Ok pending =>
      apply bind_keeps serverProject _ _ (hashed pending)
      intro reply
      cases reply with
      | fail error | div => exact pure_keeps serverProject _
      | ok result => cases result with
        | Err previous => exact pure_keeps serverProject _
        | Ok initial =>
          apply bind_keeps serverProject _ _ reserved
          intro admitted
          cases admitted with
          | false => exact pure_keeps serverProject _
          | true => exact fromInitial finish allowed control initial

/-- Actual pin, lookup and preflight failures retain all earlier cache entries. -/
theorem afterPin (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverProject (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverProject reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverProject (present keyId))
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localProject (finish control initial))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps serverProject (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact pure_keeps serverProject _
  | ok optional => cases optional with
    | none => exact pure_keeps serverProject _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_keeps serverProject _
      | ok answer => cases answer with
        | Err prior => exact pure_keeps serverProject _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => exact pure_keeps serverProject _
          | ok keyId =>
            dsimp only
            split
            · exact bind_keeps serverProject _ _ (presence keyId)
                (afterOccupancy deriveAd hashed reserve reserved finish allowed control lookup)
            · exact pure_keeps serverProject _

private theorem get_keeps : Keeps (serverProject (n := n))
    (get : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) _) := by
  intro before previous result prior supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

/-- The complete source SDK control read and pin execution preserve cached signing receipts. -/
theorem complete
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverProject (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverProject pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverProject reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverProject (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localProject (finish control initial))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps serverProject (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_keeps serverProject _ _ (get_keeps)
  intro before
  exact bind_keeps serverProject _ _ pinned
    (fun selected => afterPin deriveAd hashed reserve reserved present presence finish allowed before.control token application selected)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_keeps (handle : Nat) : Keeps (serverProject (n := n)) (take (Platform := Platform) handle) := by
  intro before previous result prior supported
  simp only [take, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : before.sessions[handle]? with
  | none => simpa only [serverProject, RegistrationServerSdkSource.take, found] using prior
  | some stored => cases stored <;> simpa only [serverProject, RegistrationServerSdkSource.take, found] using prior

private theorem build_shape
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded) (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application = (do
      let token ← take handle
      match token, application with
      | some token, some application => RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application
      | _, _ => pure (.ok none)) := by
  funext before previous
  simp only [RegistrationNativePlatformCompletionSdk.build, take, bind_apply, pure_apply, pure_bind, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk token current => cases token <;> cases application <;> rfl

/-- All actual moved-token build branches preserve the shared cache through failed reservation, publication and installation. -/
theorem build
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverProject (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverProject pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverProject reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverProject (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localProject (finish control initial))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps serverProject (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  rw [build_shape]
  apply bind_keeps serverProject _ _ (take_keeps handle)
  intro token
  cases token with
  | none => exact pure_keeps serverProject _
  | some token => cases application with
    | none => exact pure_keeps serverProject _
    | some application => exact complete deriveAd hashed pin pinned reserve reserved present presence finish allowed token application
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached



/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.commit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCached.build
