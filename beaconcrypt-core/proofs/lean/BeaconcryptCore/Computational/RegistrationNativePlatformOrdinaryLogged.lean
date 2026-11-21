-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorldSeal
import BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters
/-! The actual frame journal records a reached writer even when public reservation rejects publication. Moving the terminal capacity gate preserves that journal, the advanced kernel, every shared CTX cache entry and all primitive counters. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged
open RegistrationNativePlatformOrdinarySendGate (liftState)
open RegistrationNativePlatformOrdinaryGate (gate)
open PqxdhRecordLiftLoggedAdapters (Frames swapResult)
variable {S Platform E A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def framesAfter (query : RawCtxMixedOwner.NativeSpec.Domain) (frames : Frames) : Frames :=
  match query with
  | .inr (.inr (.inr (.inr frame))) => frames ++ [frame]
  | _ => frames

def logged (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m)) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT (S × Frames) m) :=
  fun query before => (fun reply => (reply.1, (reply.2, framesAfter query before.2))) <$>
    (native query).run before.1

def gated (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT S (StateT Platform m))
  | .inr (.inr (.inr (.inr frame))) => do
      let output ← liftState (native (.inr (.inr (.inr (.inr frame)))))
      StateT.lift (gate reserve List.length output)
  | query => liftState (native query)

omit [LawfulMonad m] in
private theorem run_liftState (work : StateT S m A) (before : S) :
    (liftState (Platform := Platform) work).run before = StateT.lift (work.run before) := rfl

omit [LawfulMonad m] in
private theorem bind_apply {B : Type} (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
omit [LawfulMonad m] in
private theorem pure_apply (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
omit [LawfulMonad m] in
private theorem lift_apply (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (work >>= fun value => pure (value, before)) := rfl

private theorem map_apply {B : Type} (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1, result.2)) <$> work before := by
  change (f <$> work).run before = _
  rw [StateT.run_map]
  rfl

/-- A reached source writer is journaled on either reservation result, with the same private poststate and common platform state. -/
theorem logged_gated (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) :
    logged (gated native reserve) = gated (logged native) reserve := by
  unfold logged
  funext query
  rcases query with request | (input | (input | (bytes | frame)))
  all_goals ext before previous
  all_goals simp only [gated, framesAfter, StateT.run_map, run_liftState,
    StateT.run_lift, StateT.run_bind, map_bind, map_pure]
  all_goals dsimp only [StateT.run, liftState]
  all_goals simp only [bind_apply, pure_apply, lift_apply, bind_map_left, bind_pure_comp, Functor.map_map]
  dsimp only [liftState]
  simp only [lift_apply, bind_map_left, bind_pure_comp]
  dsimp only [StateT.run]
  simp only [bind_map_left, map_apply]

private theorem frameLog_query (query : RawCtxMixedOwner.NativeSpec.Domain) (frames : Frames) :
    (PqxdhDeploymentNative.frameLog query).run frames =
      (fun reply => (reply, framesAfter query frames)) <$>
        (RawCtxMixedOwner.NativeSpec.query query : OracleComp RawCtxMixedOwner.NativeSpec _) := by
  rcases query with request | (input | (input | (bytes | frame)))
  all_goals simp only [PqxdhDeploymentNative.frameLog, framesAfter, StateT.run_lift, bind_pure_comp]
  all_goals rfl

/-- The explicit logger is the literal source frame journal, with only pair reassociation. -/
theorem query_source (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (query : RawCtxMixedOwner.NativeSpec.Domain) (primitive : S) (frames : Frames) :
    (logged native query).run (primitive, frames) =
      swapResult <$> (simulateQ native ((PqxdhDeploymentNative.frameLog query).run frames)).run primitive := by
  rw [frameLog_query, simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- The complete adaptive source program retains its literal per-command writer journal and all private/common state effects. -/
theorem program_source (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (primitive : S) (frames : Frames) :
    (simulateQ (logged native) work).run (primitive, frames) =
      swapResult <$> (simulateQ native ((simulateQ PqxdhDeploymentNative.frameLog work).run frames)).run primitive := by
  induction work using OracleComp.inductionOn generalizing primitive frames with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, swapResult]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind]
      rw [query_source, bind_map_left, map_bind]
      apply bind_congr
      intro reply
      exact ih reply.1.1 reply.2 reply.1.2

/-- Every actual source seal leaf is forwarded privately, with the public reservation attached only to the final writer. -/
theorem seal_queries (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) :
    gated native reserve ∘ₛ RegistrationNativePlatformOrdinaryWorldSeal.inject =
      RegistrationNativePlatformOrdinarySealGate.implementation
        (native ∘ₛ RegistrationNativePlatformOrdinaryWorldSeal.inject) reserve := by
  funext query
  rcases query with input | (bytes | frame)
  all_goals simp only [QueryImpl.compose, RegistrationNativePlatformOrdinaryWorldSeal.inject,
    simulateQ_spec_query, gated, RegistrationNativePlatformOrdinarySealGate.implementation]
  all_goals rfl

/-- Terminal reservation may follow the complete actual private seal, including its frame journal. -/
theorem sealing (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) (input : RawCtxSourceSend.SealInput) :
    simulateQ (gated native reserve)
        (simulateQ RegistrationNativePlatformOrdinaryWorldSeal.inject (RawCtxSourceSeal.sealInput input)) = (do
      let output ← liftState (simulateQ native
        (simulateQ RegistrationNativePlatformOrdinaryWorldSeal.inject (RawCtxSourceSeal.sealInput input)))
      StateT.lift (gate reserve List.length output) : StateT S (StateT Platform m) _) := by
  rw [← QueryImpl.simulateQ_compose, seal_queries]
  simpa only [QueryImpl.simulateQ_compose] using
    RegistrationNativePlatformOrdinarySealGate.program
      (native ∘ₛ RegistrationNativePlatformOrdinaryWorldSeal.inject) reserve input

/-- The complete source send adapter reaches the same private leaves and terminal capacity gate. -/
theorem send_queries (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) :
    gated native reserve ∘ₛ RawCtxMixedOwner.sendAdapter =
      RegistrationNativePlatformOrdinarySendGate.implementation (native ∘ₛ RawCtxMixedOwner.sendAdapter) reserve := by
  funext query
  rcases query with request | input
  · simp only [QueryImpl.compose, RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter,
      RawCtxMixedOwner.sendLift, simulateQ_spec_query, gated,
      RegistrationNativePlatformOrdinarySendGate.implementation]
  · simp only [QueryImpl.compose, RawCtxMixedOwner.sendAdapter, RawCtxSourceSeal.nativeAdapter,
      RegistrationNativePlatformOrdinarySendGate.implementation]
    have inclusion : RawCtxMixedOwner.sendLift ∘ₛ RawCtxSourceSeal.sealLift =
        RegistrationNativePlatformOrdinaryWorldSeal.inject := by
      funext request
      rcases request with request | (bytes | frame)
      all_goals simp only [QueryImpl.compose, RawCtxSourceSeal.sealLift, simulateQ_spec_query,
        RawCtxMixedOwner.sendLift, RegistrationNativePlatformOrdinaryWorldSeal.inject]
    rw [← QueryImpl.simulateQ_compose RawCtxMixedOwner.sendLift RawCtxSourceSeal.sealLift, inclusion]
    convert sealing native reserve input using 1 <;> rfl

/-- The complete actual source owner advances before public reservation, retaining the complete private state and journal even when publication fails. -/
theorem sendOwner {Metadata : Type} (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E))
    (senderId : U64) (plaintext : Pqxdh.Bytes) (owner : RawCtxWholeOwner.OwnerState Metadata) :
    simulateQ (gated native reserve)
        (simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run owner)) = (do
      let result ← liftState (simulateQ native
        (simulateQ RawCtxMixedOwner.sendAdapter ((RawCtxSourceSend.sendOwner senderId plaintext).run owner)))
      let output ← StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1)
      pure (output, result.2) : StateT S (StateT Platform m) _) := by
  rw [← QueryImpl.simulateQ_compose, send_queries]
  simpa only [QueryImpl.simulateQ_compose] using
    RegistrationNativePlatformOrdinarySendGate.sendOwner
      (native ∘ₛ RawCtxMixedOwner.sendAdapter) reserve senderId plaintext owner

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.logged_gated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.logged_gated

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.seal_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.seal_queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.sealing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.send_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.send_queries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.sendOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryLogged.sendOwner
