-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk

/-! Actual SDK control preserves a single shared cache whenever its literal pin, occupancy, reservation and completion calls do. Pure commit and moved-token consumption retain the cache exactly. This source-control lemma includes every failure and external poststate; concrete source callbacks are instantiated separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache
open RegistrationNativePlatformCompletionSdk (AdHash Completion)
variable {n : Nat} {Platform Value Next Encoded State : Type}

def localCache (before : RegistrationServerRootCompiler.Local n) := before.world.1.primitive.2

def serverCache (before : RegistrationServerFrontendCompiler.State n) := before.world.world.1.primitive.2

def Keeps (cache : State → CtxRomAuth.CtxRO.QueryCache)
    (work : StateT State (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → cache before ≤ cache result.1.2

private theorem pure_keeps (cache : State → CtxRomAuth.CtxRO.QueryCache) (value : Value) :
    Keeps (Platform := Platform) cache (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact le_refl _

private theorem bind_keeps (cache : State → CtxRomAuth.CtxRO.QueryCache)
    (work : StateT State (StateT Platform ProbComp) Value)
    (next : Value → StateT State (StateT Platform ProbComp) Next)
    (first : Keeps cache work) (rest : ∀ value, Keeps cache (next value)) : Keeps cache (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (first before previous middle called).trans (rest middle.1.1 middle.1.2 middle.2 result continued)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

/-- The actual SDK World lens retains every earlier shared-cache entry and the literal external poststate. -/
theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Value)
    (allowed : Keeps localCache work) : Keeps serverCache (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact allowed before.world previous inner called

/-- Pure successful and failed source publication commit retains the cache exactly. -/
theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (Platform := Platform) (serverCache (n := n)) (RegistrationNativePlatformServerSdk.commit published) := by
  intro before previous result supported
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact le_refl _
  | ok answer => cases answer <;>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported <;>
    cases supported <;> exact le_refl _

/-- Actual source completion and commit preserve every earlier shared-cache entry. -/
theorem fromInitial (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localCache (finish control initial))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_keeps serverCache _ _ (world _ (allowed control initial)) (commit)

/-- Every occupancy and reservation branch preserves cache extension through the actual source continuation. -/
theorem afterOccupancy (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverCache (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localCache (finish control initial))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps serverCache _
  | ok answer => cases answer with
    | Err prior => exact pure_keeps serverCache _
    | Ok pending =>
      apply bind_keeps serverCache _ _ (hashed pending)
      intro reply
      cases reply with
      | fail error | div => exact pure_keeps serverCache _
      | ok result => cases result with
        | Err previous => exact pure_keeps serverCache _
        | Ok initial =>
          apply bind_keeps serverCache _ _ reserved
          intro admitted
          cases admitted with
          | false => exact pure_keeps serverCache _
          | true => exact fromInitial finish allowed control initial

/-- Actual pin, lookup and preflight failures retain all earlier cache entries. -/
theorem afterPin (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverCache (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverCache (present keyId))
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localCache (finish control initial))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact pure_keeps serverCache _
  | ok optional => cases optional with
    | none => exact pure_keeps serverCache _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_keeps serverCache _
      | ok answer => cases answer with
        | Err prior => exact pure_keeps serverCache _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => exact pure_keeps serverCache _
          | ok keyId =>
            dsimp only
            split
            · exact bind_keeps serverCache _ _ (presence keyId)
                (afterOccupancy deriveAd hashed reserve reserved finish allowed control lookup)
            · exact pure_keeps serverCache _

private theorem get_keeps : Keeps (serverCache (n := n))
    (get : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) _) := by
  intro before previous result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact le_refl _

/-- The complete source SDK control read and pin execution preserve cache extension. -/
theorem complete
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (hashed : ∀ pending, Keeps serverCache (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverCache pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverCache (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localCache (finish control initial))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_keeps serverCache _ _ (get_keeps)
  intro before
  exact bind_keeps serverCache _ _ pinned
    (fun selected => afterPin deriveAd hashed reserve reserved present presence finish allowed before.control token application selected)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_keeps (handle : Nat) : Keeps (serverCache (n := n)) (take (Platform := Platform) handle) := by
  intro before previous result supported
  simp only [take, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : before.sessions[handle]? with
  | none => simp only [serverCache, RegistrationServerSdkSource.take, found]; exact le_refl _
  | some stored => cases stored <;> simp only [serverCache, RegistrationServerSdkSource.take, found] <;> exact le_refl _

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
    (hashed : ∀ pending, Keeps serverCache (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverCache pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverCache (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localCache (finish control initial))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  rw [build_shape]
  apply bind_keeps serverCache _ _ (take_keeps handle)
  intro token
  cases token with
  | none => exact pure_keeps serverCache _
  | some token => cases application with
    | none => exact pure_keeps serverCache _
    | some application => exact complete deriveAd hashed pin pinned reserve reserved present presence finish allowed token application
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.commit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkCache.build
