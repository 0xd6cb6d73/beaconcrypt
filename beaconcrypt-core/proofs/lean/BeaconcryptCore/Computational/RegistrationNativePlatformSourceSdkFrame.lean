-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceLocalFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk
/-! The literal SDK moved-token, pin, occupancy, reservation, completion and commit control preserves the supplied observation whenever its reached individual operations preserve it. The instantiated source corollary retains the actual agreement auxiliary state and request history through every failure and success. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame
open RegistrationNativePlatformCompletionSdk (Completion AdHash)
variable {n : Nat} {Platform Value Next Encoded : Type}
def Keeps {S F : Type} (observe : S → F) (work : StateT S (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result next, (result, next) ∈ support ((work.run before).run previous) → observe result.2 = observe before
private theorem pure_keeps {S F : Type} (observe : S → F) (value : Value) :
    Keeps (Platform := Platform) observe (pure value : StateT S (StateT Platform ProbComp) Value) := by
  intro before previous result next supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  rw [congrArg Prod.snd supported.1]
private theorem bind_keeps {S F : Type} (observe : S → F)
    (work : StateT S (StateT Platform ProbComp) Value) (next : Value → StateT S (StateT Platform ProbComp) Next)
    (first : Keeps observe work) (rest : ∀ value, Keeps observe (next value)) : Keeps observe (work >>= next) := by
  intro before previous result platform supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨value, middle⟩, current⟩, reached, continued⟩ := supported
  exact (rest value middle current result platform continued).trans (first before previous (value, middle) current reached)
def localFields (before : RegistrationServerRootCompiler.Local n) := RegistrationNativePlatformSourceLocalFrame.fields before
def serverFields (before : RegistrationServerFrontendCompiler.State n) := localFields before.world

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

/-- The SDK World lens retains the local agreement coordinates and complete platform state. -/
private theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Value)
    (allowed : Keeps localFields work) :
    Keeps serverFields (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result next supported
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact allowed before.world previous inner.1 inner.2 called

/-- Every publication commit leaves the local agreement coordinates unchanged. -/
private theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (Platform := Platform) (serverFields (n := n)) (RegistrationNativePlatformServerSdk.commit published) := by
  intro before previous result next supported
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rw [congrArg Prod.snd supported.1]
  | ok answer => cases answer <;>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported <;>
    rcases supported with ⟨same, _⟩ <;> cases same <;> rfl

/-- Completion and commit preserve the agreement frame on every source outcome. -/
private theorem fromInitial (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localFields (finish control initial))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps serverFields (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_keeps serverFields _ _ (world _ (allowed control initial)) (commit)

/-- Occupancy and stateful reservation preserve the agreement frame. -/
private theorem afterOccupancy (deriveAd : AdHash n (StateT Platform ProbComp))
    (adFrame : ∀ pending, Keeps serverFields (deriveAd pending))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverFields reserve) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localFields (finish control initial))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps serverFields (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps serverFields _
  | ok answer => cases answer with
    | Err prior => exact pure_keeps serverFields _
    | Ok pending =>
      apply bind_keeps serverFields _ _ (adFrame pending)
      intro hashed
      cases hashed with
      | fail error | div => exact pure_keeps serverFields _
      | ok answer => cases answer with
        | Err previous => exact pure_keeps serverFields _
        | Ok initial =>
          apply bind_keeps serverFields _ _ reserved
          intro admitted
          cases admitted with
          | false => exact pure_keeps serverFields _
          | true => exact fromInitial finish allowed control initial

/-- Pin, lookup and preflight branches retain the agreement frame. -/
private theorem afterPin (deriveAd : AdHash n (StateT Platform ProbComp))
    (adFrame : ∀ pending, Keeps serverFields (deriveAd pending))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverFields reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverFields (present keyId))
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localFields (finish control initial))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps serverFields (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact pure_keeps serverFields _
  | ok optional => cases optional with
    | none => exact pure_keeps serverFields _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_keeps serverFields _
      | ok answer => cases answer with
        | Err prior => exact pure_keeps serverFields _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => exact pure_keeps serverFields _
          | ok keyId =>
            dsimp only
            split
            · exact bind_keeps serverFields _ _ (presence keyId)
                (afterOccupancy deriveAd adFrame reserve reserved finish allowed control lookup)
            · exact pure_keeps serverFields _

private theorem get_keeps : Keeps (serverFields (n := n))
    (get : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) _) := by
  intro before previous result next supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  rw [congrArg Prod.snd supported.1]

/-- The literal SDK control read and pin execution preserve the agreement frame. -/
private theorem complete
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (adFrame : ∀ pending, Keeps serverFields (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverFields pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverFields reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverFields (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localFields (finish control initial))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps serverFields (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_keeps serverFields _ _ (get_keeps)
  intro before
  exact bind_keeps serverFields _ _ pinned
    (fun selected => afterPin deriveAd adFrame reserve reserved present presence finish allowed before.control token application selected)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_keeps (handle : Nat) : Keeps (serverFields (n := n)) (take (Platform := Platform) handle) := by
  intro before previous result next supported
  simp only [take, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  rw [congrArg Prod.snd supported.1]
  cases found : before.sessions[handle]? with
  | none => simp only [RegistrationServerSdkSource.take, found]
  | some stored => cases stored <;> simp only [RegistrationServerSdkSource.take, found]; rfl

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

/-- All moved-token build branches preserve the agreement frame through failed reservation, publication and installation. -/
theorem build
    (deriveAd : AdHash n (StateT Platform ProbComp))
    (adFrame : ∀ pending, Keeps serverFields (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverFields pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverFields reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverFields (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (allowed : ∀ control initial, Keeps localFields (finish control initial))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps serverFields (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  rw [build_shape]
  apply bind_keeps serverFields _ _ (take_keeps handle)
  intro token
  cases token with
  | none => exact pure_keeps serverFields _
  | some token => cases application with
    | none => exact pure_keeps serverFields _
    | some application => exact complete deriveAd adFrame pin pinned reserve reserved present presence finish allowed token application

private theorem nativeAdHash_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (pending : registration.ServerAdHash) :
    Keeps (serverFields (n := n)) (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending) := by
  apply world
  intro before previous result next supported
  unfold RegistrationNativePlatformServerCompletion.adHash RegistrationNativePlatformServerCompletion.adHashWith at supported
  apply RegistrationServerAdHash.state_preserves _ localFields ?_ pending before result.2 previous next result.1 supported
  intro request current previous reply after next called
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨middle, queried, returned⟩ := called
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ middle.1 previous middle.2 queried
  have preserved : localFields middle.1.2 = localFields current := by
    simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
    obtain ⟨inner, _hashed, same⟩ := actual
    exact (congrArg (fun value => localFields value.2) same).symm
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  exact (congrArg localFields returned.1.2).trans preserved

open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
variable {E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]

/-- The complete literal source SDK build retains the actual auxiliary state and agreement request history across every failure and success. -/
theorem source (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reserve : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps serverFields (RegistrationNativePlatformSourceSeal.build (n := n) coins setup codec view failure allocation erased reserve sign helper writer handle application) := by
  apply build
  · exact nativeAdHash_keeps coins
  · intro before previous result next supported
    simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, map_apply, support_map] at supported
    obtain ⟨inner, _called, same⟩ := supported
    cases same
    rfl
  · intro before previous result next supported
    simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
    obtain ⟨inner, _called, same⟩ := supported
    cases same
    rfl
  · intro keyId
    apply world
    intro before previous result next supported
    have actual := RegistrationNativePlatformHashReceipt.native_support coins _ result previous next supported
    simp only [RegistrationWorldServerCompletion.capability, StateT.run, support_map] at actual
    obtain ⟨inner, _called, same⟩ := actual
    cases same
    rfl
  · intro control pending
    exact RegistrationNativePlatformSourceLocalFrame.finish coins setup codec view failure allocation erased sign helper writer control pending
end BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceSdkFrame.source
