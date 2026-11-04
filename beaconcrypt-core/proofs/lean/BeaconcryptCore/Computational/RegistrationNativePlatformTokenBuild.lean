-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept
import BeaconcryptCore.Computational.RegistrationNativeTokenSource
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt

/-! Complete actual source response build only consumes existing tokens. Allocation, source writer, reservation, pin hashing and later failed publication/install retain the real table effects; no successful completion or source-state equality premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild.SDK
open RegistrationNativePlatformCompletionSdk (Completion)
variable {n : Nat} {Platform Value Next Encoded State : Type}

private def serverCache (before : RegistrationServerFrontendCompiler.State n) := before.sessions

private def Keeps (cache : State → List (Option peer.ConsumedRegistration))
    (work : StateT State (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → ∀ token, some token ∈ cache result.1.2 → some token ∈ cache before

private theorem pure_keeps (cache : State → List (Option peer.ConsumedRegistration)) (value : Value) :
    Keeps (Platform := Platform) cache (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact fun _ present => present

private theorem bind_keeps (cache : State → List (Option peer.ConsumedRegistration))
    (work : StateT State (StateT Platform ProbComp) Value)
    (next : Value → StateT State (StateT Platform ProbComp) Next)
    (first : Keeps cache work) (rest : ∀ value, Keeps cache (next value)) : Keeps cache (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  intro token present
  exact first before previous middle called token (rest middle.1.1 middle.1.2 middle.2 result continued token present)

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
private theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Value)
    : Keeps serverCache (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  exact fun _ present => present

/-- Pure successful and failed source publication commit retains the cache exactly. -/
private theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (Platform := Platform) (serverCache (n := n)) (RegistrationNativePlatformServerSdk.commit published) := by
  intro before previous result supported
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact fun _ present => present
  | ok answer => cases answer <;>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported <;>
    cases supported <;> exact fun _ present => present

/-- Actual source completion and commit preserve every earlier shared-cache entry. -/
private theorem fromInitial (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_keeps serverCache _ _ (world _) (commit)

/-- Every occupancy and reservation branch preserves cache extension through the actual source continuation. -/
private theorem afterOccupancy (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.afterOccupancy reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps serverCache _
  | ok answer => cases answer with
    | Err prior => exact pure_keeps serverCache _
    | Ok initial =>
      apply bind_keeps serverCache _ _ reserved
      intro admitted
      cases admitted with
      | false => exact pure_keeps serverCache _
      | true => exact fromInitial finish control initial

/-- Actual pin, lookup and preflight failures retain all earlier cache entries. -/
private theorem afterPin (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverCache (present keyId))
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.afterPin reserve present finish control token application pin) := by
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
                (afterOccupancy reserve reserved finish control lookup)
            · exact pure_keeps serverCache _

private theorem get_keeps : Keeps (serverCache (n := n))
    (get : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) _) := by
  intro before previous result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact fun _ present => present

/-- The complete source SDK control read and pin execution preserve cache extension. -/
private theorem complete
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverCache pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverCache (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_keeps serverCache _ _ (get_keeps)
  intro before
  exact bind_keeps serverCache _ _ pinned
    (fun selected => afterPin reserve reserved present presence finish before.control token application selected)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_keeps (handle : Nat) : Keeps (serverCache (n := n)) (take (Platform := Platform) handle) := by
  intro before previous result supported
  simp only [take, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  intro token present
  exact RegistrationNativeTokenSource.take_present handle before token present

private theorem build_shape
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded) (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application = (do
      let token ← take handle
      match token, application with
      | some token, some application => RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application
      | _, _ => pure (.ok none)) := by
  funext before previous
  simp only [RegistrationNativePlatformCompletionSdk.build, take, bind_apply, pure_apply, pure_bind, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk token current => cases token <;> cases application <;> rfl

/-- All actual moved-token build branches preserve the shared cache through failed reservation, publication and installation. -/
private theorem build
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverCache pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverCache reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverCache (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps serverCache (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application) := by
  rw [build_shape]
  apply bind_keeps serverCache _ _ (take_keeps handle)
  intro token
  cases token with
  | none => exact pure_keeps serverCache _
  | some token => cases application with
    | none => exact pure_keeps serverCache _
    | some application => exact complete pin pinned reserve reserved present presence finish token application
end BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild.SDK



namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks Codec)
variable {n : Nat} {E Platform Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem pin_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    SDK.Keeps (SDK.serverCache (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, SDK.map_apply, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  exact fun _ present => present

private theorem reserve_keeps (work : StateT Platform ProbComp Value) :
    SDK.Keeps (SDK.serverCache (n := n)) (StateT.lift work) := by
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  exact fun _ present => present

private theorem present_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (keyId : U64) :
    SDK.Keeps (SDK.serverCache (n := n)) (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId) := SDK.world _

/-- Complete actual source response build preserves its configured pin on every failure and success, for arbitrary actual completion and external state. -/
theorem build [primitive : AdapterSealPrimitive.Operations]
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer handle application).run before).run previous)) :
    ∀ token, RegistrationNativeTokenSource.Present token result.1.2 → RegistrationNativeTokenSource.Present token before := by
  apply SDK.build _ (pin_keeps coins) _ (reserve_keeps reservePeer) _ (present_keeps coins) _ handle application before previous result supported


end BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild.build
