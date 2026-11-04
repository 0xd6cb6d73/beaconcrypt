-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionSdk

/-! The actual corrected SDK threads the private-table/native signing-history alignment through its precise pin, occupancy, reservation, completion and commit control. Every raw optional ML reply/count and complete shared platform poststate is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology
open RegistrationNativePlatformMldsaPublicationChronology (Keeps pure_keeps bind_keeps)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformCompletionSdk (Completion)
variable {n : Nat} {Platform Value Encoded : Type} (source : RegistrationNativeMldsa.Source)

def localReceipts (before : RegistrationServerRootCompiler.Local n) := before.world.2
def serverReceipts (before : RegistrationServerFrontendCompiler.State n) := before.world.world.2

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

/-- The SDK World lens preserves actual source signing chronology with the complete private table and external state. -/
theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (M (handleSource source) Platform) Value)
    (allowed : Keeps source localReceipts work) :
    Keeps source serverReceipts (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous pool result aligned supported
  simp only [runState, RegistrationNativePlatformServerSdk.world, StateT.run, map_apply,
    RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact allowed before.world previous pool inner aligned called

/-- Successful and failed actual publication commit changes no native signing receipt or private table entry. -/
theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (Platform := Platform) source (serverReceipts (n := n)) (RegistrationNativePlatformServerSdk.commit published) := by
  intro before previous pool result aligned supported
  cases published with
  | fail error | div =>
    simp only [runState, RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      RegistrationNativeMldsaTableProgram.evaluate, simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact aligned
  | ok answer => cases answer <;>
    simp only [runState, RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      RegistrationNativeMldsaTableProgram.evaluate, simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported <;>
    cases supported <;> exact aligned

/-- Actual completion and commit preserve alignment through every source outcome. -/
theorem fromInitial (finish : Completion n (M (handleSource source) Platform) Encoded)
    (allowed : ∀ control initial, Keeps source localReceipts (finish control initial))
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps source serverReceipts (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_keeps source serverReceipts _ _ (world source _ (allowed control initial)) (commit source)

/-- Exact occupancy and stateful reservation branches retain both same-position chronological histories. -/
theorem afterOccupancy (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (reserved : Keeps source serverReceipts reserve) (finish : Completion n (M (handleSource source) Platform) Encoded)
    (allowed : ∀ control initial, Keeps source localReceipts (finish control initial))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps source serverReceipts (RegistrationNativePlatformCompletionSdk.afterOccupancy reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps source serverReceipts _
  | ok answer => cases answer with
    | Err prior => exact pure_keeps source serverReceipts _
    | Ok initial =>
      apply bind_keeps source serverReceipts _ _ reserved
      intro admitted
      cases admitted with
      | false => exact pure_keeps source serverReceipts _
      | true => exact fromInitial source finish allowed control initial

/-- Actual pin, lookup and preflight failures retain the original signing logs without dropping reached state. -/
theorem afterPin (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (reserved : Keeps source serverReceipts reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (presence : ∀ keyId, Keeps source serverReceipts (present keyId))
    (finish : Completion n (M (handleSource source) Platform) Encoded)
    (allowed : ∀ control initial, Keeps source localReceipts (finish control initial))
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps source serverReceipts (RegistrationNativePlatformCompletionSdk.afterPin reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact pure_keeps source serverReceipts _
  | ok optional => cases optional with
    | none => exact pure_keeps source serverReceipts _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_keeps source serverReceipts _
      | ok answer => cases answer with
        | Err prior => exact pure_keeps source serverReceipts _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => exact pure_keeps source serverReceipts _
          | ok keyId =>
            dsimp only
            split
            · exact bind_keeps source serverReceipts _ _ (presence keyId)
                (afterOccupancy source reserve reserved finish allowed control lookup)
            · exact pure_keeps source serverReceipts _

private theorem get_keeps : Keeps source (serverReceipts (n := n))
    (get : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) _) := by
  intro before previous pool result aligned supported
  simp only [runState, StateT.run_get, StateT.run_pure, RegistrationNativeMldsaTableProgram.evaluate,
    simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact aligned

/-- The complete literal SDK control read and pin execution preserve same-position ML request and native payload history. -/
theorem complete
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps source serverReceipts pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (reserved : Keeps source serverReceipts reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (presence : ∀ keyId, Keeps source serverReceipts (present keyId)) (finish : Completion n (M (handleSource source) Platform) Encoded)
    (allowed : ∀ control initial, Keeps source localReceipts (finish control initial))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps source serverReceipts (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_keeps source serverReceipts _ _ (get_keeps source)
  intro before
  exact bind_keeps source serverReceipts _ _ pinned
    (fun selected => afterPin source reserve reserved present presence finish allowed before.control token application selected)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_keeps (handle : Nat) : Keeps source (serverReceipts (n := n)) (take (Platform := Platform) source handle) := by
  intro before previous pool result aligned supported
  simp only [runState, take, StateT.run, pure_apply, RegistrationNativeMldsaTableProgram.evaluate,
    simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : before.sessions[handle]? with
  | none => simpa only [serverReceipts, RegistrationServerSdkSource.take, found] using aligned
  | some stored => cases stored <;> simpa only [serverReceipts, RegistrationServerSdkSource.take, found] using aligned

private theorem build_shape
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (finish : Completion n (M (handleSource source) Platform) Encoded) (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application = (do
      let token ← take source handle
      match token, application with
      | some token, some application => RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token application
      | _, _ => pure (.ok none)) := by
  funext before previous
  simp only [RegistrationNativePlatformCompletionSdk.build, take, bind_apply, pure_apply, pure_bind, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk token current => cases token <;> cases application <;> rfl

/-- All actual moved-token build branches preserve the chronological relation through failed reservation, publication and installation. -/
theorem build
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps source serverReceipts pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (reserved : Keeps source serverReceipts reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (M (handleSource source) Platform) Bool)
    (presence : ∀ keyId, Keeps source serverReceipts (present keyId)) (finish : Completion n (M (handleSource source) Platform) Encoded)
    (allowed : ∀ control initial, Keeps source localReceipts (finish control initial))
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps source serverReceipts (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application) := by
  rw [build_shape]
  apply bind_keeps source serverReceipts _ _ (take_keeps source handle)
  intro token
  cases token with
  | none => exact pure_keeps source serverReceipts _
  | some token => cases application with
    | none => exact pure_keeps source serverReceipts _
    | some application => exact complete source pin pinned reserve reserved present presence finish allowed token application
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.commit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.commit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkChronology.build
