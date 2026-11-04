-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSyncMain
/-! Every target chosen by the literal public compiler is an actual one-time role message. Arbitrary adaptive source replies, optional failures and all public callback entry updates preserve this structural invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

def Tagged (before : Mode) : Prop :=
  ∀ message, before.target = some message → RegistrationNativeIdentitySigningRole.oneTime message = true

private theorem simulated_support {I J : Type} {spec : OracleSpec I} {target : OracleSpec J}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec A) (value : A)
    (reached : value ∈ support (simulateQ impl work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure returned =>
      rw [simulateQ_pure] at reached
      obtain rfl := eq_of_mem_support_pure _ reached
      simp only [support_pure, Set.mem_singleton_iff]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
    obtain ⟨reply, _queried, continued⟩ := reached
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply continued⟩

private theorem lift_state {B : Type} (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support ((StateT.lift work : StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) B).run mode)) :
    result.2 = mode := by
  change result ∈ support (do let reply ← work; pure (reply, mode)) at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl

private theorem constant_state {I : Type} {spec : OracleSpec I} {B : Type} (work : OracleComp spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support (do let reply ← work; pure (reply, mode))) : result.2 = mode := by
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl


private theorem prepare (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) (prior : Tagged before)
    (result : Unit × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run before)) :
    Tagged result.2 := by
  by_cases eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message
  · simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible, and_self, ite_true] at reached
    split at reached
    · rw [mem_support_bind_iff] at reached
      obtain ⟨chosen, _selected, rest⟩ := reached
      cases chosen
      · simp only [Bool.false_eq_true, ite_false, mem_support_pure_iff] at rest
        cases rest
        exact prior
      · simp only [ite_true] at rest
        rw [mem_support_bind_iff] at rest
        obtain ⟨_answer, _inspected, returned⟩ := rest
        obtain rfl := eq_of_mem_support_pure _ returned
        intro target same
        have equal : message = target := Option.some.inj same
        rw [← equal]
        exact eligible.2
    · simp only [Bool.false_eq_true, ite_false, pure_bind, mem_support_pure_iff] at reached
      cases reached
      exact prior
  · simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, eligible, ite_false, mem_support_pure_iff] at reached
    cases reached
    exact prior

private theorem signing_tagged (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode)
    (prior : Tagged before) (result : Option Ed25519Signature × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run before)) :
    Tagged result.2 := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨prepared, queried, rest⟩ := reached
  have original := simulated_support _ _ _ queried
  have tagged := prepare selected handle message before prior prepared original
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at rest
  split at rest
  all_goals rw [lift_state _ _ _ rest]
  all_goals exact tagged
/-- Actual operational source leaves preserve the selected-message role through all later hashes and signing calls. -/
theorem query (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (mode : Mode)
    (prior : Tagged mode)
    (result : RegistrationNativePlatformIdentityCtxCompiler.Spec.Range request × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)) :
    Tagged result.2 := by
  rcases request with ((coin | request) | report) | bytes
  · have original := simulated_support _ _ _ reached
    rw [constant_state _ _ _ original]
    exact prior
  · cases request with
    | create | reveal handle =>
      have original := simulated_support _ _ _ reached
      rw [constant_state _ _ _ original]
      exact prior
    | service handle request => cases request with
      | staticDh peer =>
        have original := simulated_support _ _ _ reached
        rw [constant_state _ _ _ original]
        exact prior
      | sign message => exact signing_tagged selected handle message mode prior result reached
  · have original := simulated_support _ _ _ reached
    rw [constant_state _ _ _ original]
    exact prior
  · change result ∈ support (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => simulateQ RegistrationNativeIdentityCensorOperational.embed
          ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode)
      | none => do
          let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query
            (.inr (.template selected mode.target (RegistrationNativeIdentityCensorOperational.parts bytes).1
              (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp RegistrationNativeIdentityCensorOperational.Spec _)
          pure (reply, mode)) at reached
    split at reached
    · have original := simulated_support _ _ _ reached
      change result ∈ support (do
        let reply ← (RegistrationNativeIdentityCensorCompiler.Spec.query
          (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)) : OracleComp RegistrationNativeIdentityCensorCompiler.Spec _)
        pure (reply, {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
          | none => mode.knownInputs
          | some input => mode.knownInputs ++ [input]})) at original
      have same := constant_state _ _ result original
      rw [same]
      exact prior
    · rw [constant_state _ _ _ reached]
      exact prior


/-- Arbitrary adaptive source work retains that any selected target is a one-time-role message, including all optional replies. -/
theorem program (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A)
    (mode : Mode) (prior : Tagged mode) (result : A × Mode)
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)) :
    Tagged result.2 := by
  induction work using OracleComp.inductionOn generalizing mode result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1 middle.2 (query selected placeholder request mode prior middle called) result continued


/-- Either private source interpretation retains the selected-target role of the literal operational computation. -/
theorem lower_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A) (mode : Mode)
    (before : RegistrationNativeIdentityCensorSource.State) (prior : Tagged mode)
    (result : (A × Mode) × RegistrationNativeIdentityCensorSource.State)
    (reached : result ∈ support ((simulateQ (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    Tagged result.1.2 := by
  have operational : result.1 ∈ support
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode) := by
    apply OracleComp.support_simulateQ_run'_subset
      (if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
        else RegistrationNativeIdentityCensorSource.implementation joint selected) _ before
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  exact program selected placeholder work mode prior result.1 operational

open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
open RegistrationNativeIdentityCensorTargetSync (lower)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {KemSK Platform : Type} {mlSource : RegistrationNativeMldsa.Source}

/-- The full literal Main interpreter preserves role-correct targets without inspecting any private seed or source row. -/
theorem main (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : Tagged before.1.2)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((interpret joint selected placeholder masked work).run before)) :
    Tagged result.2.1.2 := by
  simp only [interpret, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨returned, called, completed⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ completed
  exact lower_program joint selected placeholder masked (work.run before.1.1) before.1.2 before.2 prior returned called

/-- All public callback entry markers preserve the selected-target role while resetting current routing. -/
theorem enter (position : Nat) (query : TypedSpec.Domain) (before : Mode) (prior : Tagged before) :
    Tagged (RegistrationNativeIdentityCensorCompiler.enter position query before) := by
  cases query with
  | inl query => exact prior
  | inr command => cases command <;> exact prior

/-- The actual complete source callback derives the selected-target role across the literal all-attempt entry marker. -/
theorem callback (joint : PqxdhJointIdentity.Primitives) (selected position : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (query : TypedSpec.Domain)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : Tagged before.1.2)
    (result : TypedSpec.Range query × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((RegistrationNativeIdentityCensorPublicSource.callback
      (lower joint selected placeholder masked)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend) query).run before)) :
    Tagged result.2.1.2 := by
  rw [lower, RegistrationNativeIdentityCensorPublicSource.current] at supported
  exact main joint selected placeholder masked (frontend query)
    ((before.1.1, RegistrationNativeIdentityCensorCompiler.enter position query before.1.2), before.2)
    (enter position query before.1.2 prior) result supported

/-- Every adaptive complete callback history retains role-correct targets through successes and failures. -/
theorem adaptive (joint : PqxdhJointIdentity.Primitives) (selected position : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (work : OracleComp TypedSpec A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (prior : Tagged before.1.2)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPublicSource.callback
      (lower joint selected placeholder masked)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend)) work).run before)) :
    Tagged result.2.1.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨returned, called, continued⟩ := supported
    exact ih returned.1 returned.2
      (callback joint selected position placeholder masked frontend request before prior returned called) result continued

/-- Starting without a target derives every later selected message's one-time role from the literal compiler alone. -/
theorem initialized (joint : PqxdhJointIdentity.Primitives) (selected position : Nat)
    (placeholder : Ed25519Signature) (masked : Bool)
    (frontend : QueryImpl TypedSpec (RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource))
    (work : OracleComp TypedSpec A)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (empty : before.1.2.target = none)
    (result : A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource))
    (supported : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorPublicSource.callback
      (lower joint selected placeholder masked)
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend)) work).run before)) :
    Tagged result.2.1.2 := by
  apply adaptive joint selected position placeholder masked frontend work before _ result supported
  intro message same
  rw [empty] at same
  cases same

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.lower_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.main

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.enter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.enter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.adaptive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.adaptive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetRole.initialized
