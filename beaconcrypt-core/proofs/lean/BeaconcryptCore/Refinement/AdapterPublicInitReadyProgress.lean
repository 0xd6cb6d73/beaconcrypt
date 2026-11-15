-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicInitReady
/-! Every supported continued source Init iteration decreases the actual protocol rank even with stateful changing primitive replies. The well-founded execution retains the complete returned shared state and every failure/divergence outcome. The checked source finite request driver equals this execution with no caller fuel or fixed-reply premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
variable {S : Type}
abbrev M (S : Type) := RustT (StateT S ProbComp)

private theorem request_cut {Reply Value : Type} (request : RustM Reply) (next : Reply → M S Value)
    (value : Value) (before after : S)
    (supported : (.ok value, after) ∈ support (((do
      let reply ← (liftRust request : M S Reply)
      next reply).run).run before)) :
    ∃ reply, request = .ok reply ∧ (.ok value, after) ∈ support ((next reply).run.run before) := by
  cases request with
  | fail error | div =>
      simp only [RustT.run_bind, RustT.run_liftRust, StateT.run_pure,
        pure_bind, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | ok reply =>
      exact ⟨reply, rfl, by simpa only [RustT.run_bind, RustT.run_liftRust, StateT.run_bind,
        StateT.run_pure, pure_bind] using supported⟩

private theorem resume_cut {Reply Input Output : Type} (work : M S Reply) (resume : Reply → RustM Input)
    (next : Input) (before after : S)
    (supported : (.ok (.cont next), after) ∈ support (((do
      let reply ← work
      let effect ← liftRust (resume reply)
      pure (.cont effect : ControlFlow Input Output) : M S (ControlFlow Input Output)).run).run before)) :
    ∃ reply, resume reply = .ok next := by
  simp only [RustT.run_bind, StateT.run_bind] at supported
  obtain ⟨called, reached, continued⟩ := support_bind_exists supported
  rcases called with ⟨reply, state⟩
  cases reply with
  | fail error | div =>
      simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok reply =>
      simp only [RustT.run_liftRust, pure_bind] at continued
      cases actual : resume reply with
      | fail error | div =>
          simp only [actual, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
      | ok value =>
          simp only [actual, RustT.run_pure, StateT.run_pure, mem_support_pure_iff,
            Prod.mk.injEq, RustM.ok.injEq, ControlFlow.cont.injEq] at continued
          exact ⟨reply, actual.trans (congrArg RustM.ok continued.1.symm)⟩

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (M S)]
variable [AdapterPublicWrapperRequestMonad.CryptoOperations (M S)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (M S)]

omit platform localOps in
theorem step_progress (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect next : registration.BeaconInitEffect) (before after : S)
    (supported : (.ok (.cont next), after) ∈ support ((AdapterPublicInitReady.step (m := StateT S ProbComp) beacon effect).run.run before)) :
    AdapterPublicInitSourceLoop.rank next < AdapterPublicInitSourceLoop.rank effect := by
  cases effect with
  | Rejected _ | Ready _ =>
      simp only [AdapterPublicInitReady.step, RustT.run_pure, StateT.run_pure,
        mem_support_pure_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
  | Ed25519SigningRequested pending =>
      obtain ⟨request, _, continued⟩ := request_cut pending.request _ (.cont next : ControlFlow registration.BeaconInitEffect (core.option.Option registration.BeaconInitReady)) before after supported
      obtain ⟨reply, resumed⟩ := resume_cut (AdapterPublicInitReady.ed (m := StateT S ProbComp) beacon request) pending.resume next before after continued
      exact AdapterPublicInitSourceLoop.ed_progress pending reply next resumed
  | HashRequested pending =>
      obtain ⟨request, _, continued⟩ := request_cut pending.request _ (.cont next : ControlFlow registration.BeaconInitEffect (core.option.Option registration.BeaconInitReady)) before after supported
      obtain ⟨reply, resumed⟩ := resume_cut (children.executeHash request) pending.resume next before after continued
      exact AdapterPublicInitSourceLoop.hash_progress pending reply next resumed

noncomputable def execute (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect : registration.BeaconInitEffect) (before : S) :
    ProbComp (RustM (core.option.Option registration.BeaconInitReady) × S) := do
  let result ← MonadAttach.attach
    ((AdapterPublicInitReady.step (m := StateT S ProbComp) beacon effect).run.run before)
  match result with
  | ⟨(.ok (.cont next), after), _supported⟩ => execute beacon next after
  | ⟨(.ok (.done value), after), _⟩ => pure (.ok value, after)
  | ⟨(.fail error, after), _⟩ => pure (.fail error, after)
  | ⟨(.div, after), _⟩ => pure (.div, after)
termination_by AdapterPublicInitSourceLoop.rank effect
decreasing_by exact step_progress beacon effect next before after _supported

omit platform localOps in
theorem finite_execute (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (fuel : Nat) (effect : registration.BeaconInitEffect) (before : S)
    (enough : AdapterPublicInitSourceLoop.rank effect < fuel) :
    ((AdapterPublicWrapperLiftFunction.loopFuel fuel
      (AdapterPublicInitReady.step (m := StateT S ProbComp) beacon) effect).run).run before =
      execute beacon effect before := by
  induction fuel generalizing effect before with
  | zero => omega
  | succ fuel ih =>
      rw [AdapterPublicWrapperLiftFunction.loopFuel, execute.eq_def]
      simp only [RustT.run_bind, StateT.run_bind]
      rw [← WeaklyLawfulMonadAttach.attach_bind_val
        (x := (AdapterPublicInitReady.step (m := StateT S ProbComp) beacon effect).run.run before)]
      apply bind_congr
      intro result
      rcases result with ⟨⟨reply, after⟩, supported⟩
      cases reply with
      | fail error | div => rfl
      | ok decision => cases decision with
        | done value => rfl
        | cont next =>
            have smaller := step_progress beacon effect next before after supported
            exact ih next after (by omega)


omit platform localOps in
theorem source_execute (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (effect : registration.BeaconInitEffect) (before : S) :
    ((beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop
      (m := M S) effect beacon).run).run before = execute beacon effect before := by
  rw [AdapterPublicInitReady.loop_source]
  exact finite_execute beacon _ effect before (Nat.lt_succ_self _)

end BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress.step_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress.step_progress

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress.finite_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress.finite_execute

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress.source_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitReadyProgress.source_execute
