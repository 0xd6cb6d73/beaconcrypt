-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt
import BeaconcryptCore.Computational.RegistrationNativeStageTrace

/-! A message newly present in an actual source signing history has a first supported public bundle callback with a fresh history at entry. The private chronological callback journal supplies complete same-run before/after states; the all-attempt counter supplies its finite public ordinal. No first-bad-accept selector or source freshness premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace)
open RegistrationNativePlatformIdentityCtxSigningSource (Aligned typedHandler)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential
  keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "callback" => typedHandler setup.joint frontend
abbrev Whole (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  (((RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace) × RegistrationNativePlatformIdentityCtxSource.State)
local notation "WholeState" => Whole n KemSK Platform source

def messages (handle : Nat) (before : WholeState) : List Pqxdh.Bytes :=
  PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle before.2.1.transcript)
def coherent (before : WholeState) : Prop := Aligned (before.1.2, before.2)

private theorem step_coherent (query : TypedSpec.Domain) (before : WholeState)
    (result : TypedSpec.Range query × WholeState) (prior : coherent before)
    (supported : result ∈ support ((callback query).run before)) : coherent result.2 := by
  rw [typedHandler, QueryImpl.Stateful.link_impl_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact RegistrationNativePlatformIdentityCtxSigningSource.typed_interpreted setup.joint frontend
    (TypedSpec.query query) before.1 before.2 prior inner (by simpa only [simulateQ_spec_query] using called)

private theorem step_counter (query : TypedSpec.Domain) (before : WholeState)
    (result : TypedSpec.Range query × WholeState)
    (supported : result ∈ support ((callback query).run before)) :
    result.2.1.2.nextBundle = before.1.2.nextBundle +
      if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0 := by
  rw [typedHandler, QueryImpl.Stateful.link_impl_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  apply RegistrationNativePlatformIdentityCtxSigningTrace.query_counter frontend query before.1 inner.1
  apply support_simulateQ_run'_subset (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint) _ before.2
  rw [StateT.run'_eq, support_map]
  exact ⟨inner, called, rfl⟩

private theorem nonsigning_log (query : TypedSpec.Domain) (notBundle : ∀ index, query ≠ .inr (.bundle index))
    (before : WholeState) (result : TypedSpec.Range query × WholeState)
    (supported : result ∈ support ((callback query).run before)) : result.2.1.2.log = before.1.2.log := by
  rw [typedHandler, QueryImpl.Stateful.link_impl_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  have quiet := RegistrationNativePlatformIdentityCtxSignScope.handler_safe setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query notBundle before.1.1
  have literal : (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend query).run before.1 =
      (fun returned => (returned.1, (returned.2, (RegistrationNativePlatformIdentityCtxSigningTrace.mark query before.1.2).2))) <$>
        (frontend query).run before.1.1 := by
    unfold RegistrationNativePlatformIdentityCtxSigningTrace.wrap
    change (fun returned => (returned.1.1, (returned.1.2, returned.2))) <$>
      (simulateQ (RegistrationNativePlatformIdentityCtxSigningLog.logging
        (RegistrationNativePlatformIdentityCtxSigningTrace.mark query before.1.2).1)
        ((frontend query).run before.1.1)).run
          (RegistrationNativePlatformIdentityCtxSigningTrace.mark query before.1.2).2 = _
    rw [RegistrationNativePlatformIdentityCtxSigningLog.no_sign _ _ quiet]
    simp only [Functor.map_map]
  rw [literal, simulateQ_map, StateT.run_map, support_map] at called
  obtain ⟨returned, _reached, rfl⟩ := called
  unfold RegistrationNativePlatformIdentityCtxSigningTrace.mark
  split <;> rfl

private theorem nonsigning_history (query : TypedSpec.Domain) (notBundle : ∀ index, query ≠ .inr (.bundle index))
    (before : WholeState) (result : TypedSpec.Range query × WholeState) (prior : coherent before)
    (supported : result ∈ support ((callback query).run before)) (handle : Nat) :
    messages handle result.2 = messages handle before := by
  have after := step_coherent setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer query before result prior supported
  have logs := nonsigning_log setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer query notBundle before result supported
  rw [messages, messages, RegistrationNativePlatformIdentityCtxSigningSource.selected_history,
    RegistrationNativePlatformIdentityCtxSigningSource.selected_history, ← after, ← prior]
  simp only [RegistrationNativePlatformIdentityCtxSigningSource.traceCalls, logs]

private theorem path_counter {before after : WholeState} {calls : List (Call TypedSpec WholeState)}
    (actual : Path callback before calls after) : before.1.2.nextBundle ≤ after.1.2.nextBundle := by
  induction actual with
  | nil => exact Nat.le_refl _
  | cons call called rest last following ih =>
    have step := step_counter setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer call.query call.before (call.reply, call.after) called
    exact (by rw [step]; omega : call.before.1.2.nextBundle ≤ call.after.1.2.nextBundle).trans ih

/-- A first chronological crossing of source signing history must be an actual bundle callback. Its public ordinal is bounded by the same run's all-attempt bundle counter. -/
theorem first {before after : WholeState} {calls : List (Call TypedSpec WholeState)}
    (actual : Path callback before calls after) (prior : coherent before) (handle : Nat) (message : Pqxdh.Bytes)
    (fresh : message ∉ messages handle before) (signed : message ∈ messages handle after)
    (budget : Nat) (bounded : after.1.2.nextBundle ≤ budget) :
    ∃ leading call trailing index,
      calls = leading ++ call :: trailing ∧ Path callback before leading call.before ∧
      Executed callback call ∧ Path callback call.after trailing after ∧
      call.query = .inr (.bundle index) ∧ coherent call.before ∧
      message ∉ messages handle call.before ∧ message ∈ messages handle call.after ∧
      call.before.1.2.nextBundle < budget := by
  induction actual with
  | nil => exact False.elim (fresh signed)
  | cons call called rest last following ih =>
    have afterCoherent := step_coherent setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer call.query call.before (call.reply, call.after) prior called
    by_cases current : message ∈ messages handle call.after
    · have bundleQuery : ∃ index, call.query = .inr (.bundle index) := by
        by_contra none
        have notBundle : ∀ index, call.query ≠ .inr (.bundle index) := by
          intro index equal
          exact none ⟨index, equal⟩
        have same := nonsigning_history setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer call.query notBundle call.before (call.reply, call.after) prior called handle
        exact fresh (same ▸ current)
      obtain ⟨index, queryEq⟩ := bundleQuery
      have counter := step_counter setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer call.query call.before (call.reply, call.after) called
      have later := path_counter setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer following
      have finite : call.before.1.2.nextBundle < budget := by
        simp only [queryEq, RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle, ite_true] at counter
        omega
      exact ⟨[], call, rest, index, rfl, .nil _, called, following, queryEq, prior, fresh, current, finite⟩
    · obtain ⟨leading, chosen, trailing, index, split, prefixPath, chosenCalled, suffixPath, queryEq, chosenCoherent, chosenFresh, chosenSigned, finite⟩ :=
        ih afterCoherent current signed bounded
      exact ⟨call :: leading, chosen, trailing, index, by rw [split]; rfl,
        .cons call called _ _ prefixPath, chosenCalled, suffixPath, queryEq, chosenCoherent, chosenFresh, chosenSigned, finite⟩

/-- The original typed all-attempt allowance bounds the same actual source callback counter, including every failed native and writer path. -/
theorem budget (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle cap)
    (before : WholeState) (result : A × WholeState)
    (supported : result ∈ support ((simulateQ callback work).run before)) :
    result.2.1.2.nextBundle ≤ before.1.2.nextBundle + cap := by
  induction work using OracleComp.inductionOn generalizing cap before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    have counted := step_counter setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer query before middle called
    have later := ih middle.1 _ (bounded.2 middle.1) middle.2 result continued
    rw [counted] at later
    by_cases selected : RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query
    · have positive := bounded.1.resolve_left (fun impossible => impossible selected)
      simp only [selected, ite_true] at later
      omega
    · simp only [selected, ite_false, Nat.add_zero] at later
      exact later

/-- A complete actual empty-identity source run supplies its own fresh-entry bundle cut and finite public ordinal. The chronological path is derived by exact ghost-journal erasure, rather than supplied as a protocol-event premise. -/
theorem initialized (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle cap)
    (before : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (physical : RegistrationNativePlatformCtxBackend.State) (result : A × WholeState)
    (supported : result ∈ support ((simulateQ callback work).run
      ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical))))
    (handle : Nat) (message : Pqxdh.Bytes) (signed : message ∈ messages handle result.2) :
    ∃ calls leading call trailing index,
      Path callback ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) calls result.2 ∧
      calls = leading ++ call :: trailing ∧
      Path callback ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) leading call.before ∧
      Executed callback call ∧ Path callback call.after trailing result.2 ∧
      call.query = .inr (.bundle index) ∧ coherent call.before ∧
      message ∉ messages handle call.before ∧ message ∈ messages handle call.after ∧
      call.before.1.2.nextBundle < cap := by
  have journalPossible : result ∈ support (Prod.map id Prod.fst <$>
      (simulateQ (RegistrationNativeStageTrace.handler callback) work).run
        (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)), [])) := by
    rw [RegistrationNativeStageTrace.erase]
    exact supported
  rw [support_map] at journalPossible
  obtain ⟨journaled, reached, same⟩ := journalPossible
  have actual := RegistrationNativeStageTrace.path callback work
    ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) journaled reached
  have finalState : journaled.2.1 = result.2 := congrArg Prod.snd same
  rw [finalState] at actual
  have counted := budget setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer work cap bounded ((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) result supported
  have finite : result.2.1.2.nextBundle ≤ cap := by simpa only [Nat.zero_add] using counted
  have initialCoherent : coherent (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) : WholeState) := by rfl
  have fresh : message ∉ messages handle (((before, {}), (PqxdhDynamicIdentityPool.initialState, physical)) : WholeState) := by
    change message ∉ ([] : List Pqxdh.Bytes)
    exact List.not_mem_nil
  obtain ⟨leading, call, trailing, index, split, prefixPath, called, suffixPath, queryEq, prior, firstFresh, firstSigned, ordinal⟩ :=
    first setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer actual initialCoherent handle message fresh signed cap finite
  exact ⟨journaled.2.2, leading, call, trailing, index, actual, split, prefixPath, called, suffixPath, queryEq, prior, firstFresh, firstSigned, ordinal⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut.first
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut.budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut.budget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstBundleCut.initialized
