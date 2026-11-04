-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorEdOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace

/-! Lower source queries preserve the public all-attempt bundle counter. Only the literal typed callback entry increments it, before owner lookup or any possible writer failure. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

private theorem prepare (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode)
    (result : Unit × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run mode)) :
    result.2.bundles = mode.bundles := by
  simp only [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run] at reached
  split at reached
  · split at reached
    · rw [mem_support_bind_iff] at reached
      obtain ⟨chosen, _selected, rest⟩ := reached
      split at rest
      · rw [mem_support_bind_iff] at rest
        obtain ⟨_scanned, _queried, returned⟩ := rest
        obtain rfl := eq_of_mem_support_pure _ returned
        rfl
      · obtain rfl := eq_of_mem_support_pure _ rest
        rfl
    · simp only [pure_bind, Bool.false_eq_true, ite_false] at reached
      obtain rfl := eq_of_mem_support_pure _ reached
      rfl
  · obtain rfl := eq_of_mem_support_pure _ reached
    rfl

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

private theorem signing (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode)
    (result : Option Ed25519Signature × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)) :
    result.2.bundles = mode.bundles := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨prepared, queried, rest⟩ := reached
  have prior := prepare selected handle message mode prepared (simulated_support _ _ _ queried)
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at rest
  split at rest
  · rw [lift_state _ _ _ rest]
    exact prior
  · rw [lift_state _ _ _ rest]
    exact prior

private theorem constant_state {I : Type} {spec : OracleSpec I} {B : Type} (work : OracleComp spec B)
    (mode : Mode) (result : B × Mode)
    (reached : result ∈ support (do let reply ← work; pure (reply, mode))) : result.2 = mode := by
  rw [mem_support_bind_iff] at reached
  obtain ⟨reply, _queried, returned⟩ := reached
  obtain rfl := eq_of_mem_support_pure _ returned
  rfl

/-- No lower primitive, omission, scan or hash query increments the public callback counter. -/
theorem query (selected : Nat) (placeholder : Ed25519Signature)
    (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (mode : Mode)
    (result : RegistrationNativePlatformIdentityCtxCompiler.Spec.Range request × Mode)
    (reached : result ∈ support ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)) :
    result.2.bundles = mode.bundles := by
  rcases request with ((coin | request) | report) | bytes
  · have original := simulated_support _ _ _ reached
    exact congrArg Mode.bundles (constant_state _ _ _ original)
  · cases request with
    | create | reveal handle =>
      have original := simulated_support _ _ _ reached
      exact congrArg Mode.bundles (constant_state _ _ _ original)
    | service handle request => cases request with
      | staticDh peer =>
        have original := simulated_support _ _ _ reached
        exact congrArg Mode.bundles (constant_state _ _ _ original)
      | sign message => exact signing selected handle message mode result reached
  · have original := simulated_support _ _ _ reached
    exact congrArg Mode.bundles (constant_state _ _ _ original)
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
      have projected := congrArg Mode.bundles same
      exact projected
    · exact congrArg Mode.bundles (constant_state _ _ _ reached)

/-- Every adaptive lower source tree preserves the public typed-bundle position. -/
theorem program (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A) (mode : Mode)
    (result : A × Mode)
    (reached : result ∈ support ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)) :
    result.2.bundles = mode.bundles := by
  induction work using OracleComp.inductionOn generalizing mode result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure] at reached
    obtain rfl := eq_of_mem_support_pure _ reached
    rfl
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact (ih middle.1 middle.2 result continued).trans (query selected placeholder request mode middle called)

/-- Interpreting actual private queries cannot change the counter law. The private source may retain every failed attempt and full hash journal. -/
theorem source {Private : Type} (selected : Nat) (placeholder : Ed25519Signature)
    (impl : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT Private ProbComp))
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A) (mode : Mode) (privateState : Private)
    (result : (A × Mode) × Private)
    (reached : result ∈ support ((simulateQ impl
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run privateState)) :
    result.1.2.bundles = mode.bundles := by
  apply program selected placeholder work mode result.1
  apply support_simulateQ_run'_subset impl _ privateState
  rw [StateT.run'_eq, support_map]
  exact ⟨result, reached, rfl⟩

/-- The actual public callback increments once before every typed bundle, including invalid owners and failed writers, and never at any lower query. -/
theorem callback {S Private : Type} (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (impl : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT Private ProbComp))
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : S × Mode) (privateState : Private)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range request × (S × Mode)) × Private)
    (reached : result ∈ support ((simulateQ impl
      ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend request).run before)).run privateState)) :
    result.1.2.2.bundles = before.2.bundles +
      if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle request then 1 else 0 := by
  have literal : (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend request).run before =
      (fun returned => (returned.1.1, (returned.1.2, returned.2))) <$>
        (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
          ((frontend request).run before.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.2) := by
    change (do
      let returned ← (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
        ((frontend request).run before.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.2)
      pure (returned.1.1, (returned.1.2, returned.2))) = _
    rw [bind_pure_comp]
  rw [literal, simulateQ_map, StateT.run_map, support_map] at reached
  obtain ⟨inner, actual, rfl⟩ := reached
  have unchanged := source selected placeholder impl ((frontend request).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter position request before.2) privateState inner actual
  rw [unchanged]
  rcases request with request | request
  · rfl
  · cases request <;> rfl

/-- A private interpretation of the marked callback retains an actual original reply/state path in the literal supplied frontend. -/
theorem callback_support {S Private : Type} (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (impl : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT Private ProbComp))
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : S × Mode) (privateState : Private)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range request × (S × Mode)) × Private)
    (reached : result ∈ support ((simulateQ impl
      ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend request).run before)).run privateState)) :
    (result.1.1, result.1.2.1) ∈ support ((frontend request).run before.1) := by
  have literal : (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend request).run before =
      (fun returned => (returned.1.1, (returned.1.2, returned.2))) <$>
        (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
          ((frontend request).run before.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.2) := by
    change (do
      let returned ← (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
        ((frontend request).run before.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.2)
      pure (returned.1.1, (returned.1.2, returned.2))) = _
    rw [bind_pure_comp]
  rw [literal, simulateQ_map, StateT.run_map, support_map] at reached
  obtain ⟨inner, actual, rfl⟩ := reached
  have lower : inner.1 ∈ support ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
      ((frontend request).run before.1)).run (RegistrationNativeIdentityCensorCompiler.enter position request before.2)) := by
    apply support_simulateQ_run'_subset impl _ privateState
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, actual, rfl⟩
  apply support_simulateQ_run'_subset (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
    ((frontend request).run before.1) (RegistrationNativeIdentityCensorCompiler.enter position request before.2)
  rw [StateT.run'_eq, support_map]
  exact ⟨inner.1, lower, rfl⟩

/-- The executable selector's counter equals the actual signing receipt journal's all-attempt counter after each same-run callback. -/
theorem synchronized {S Private : Type} (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (impl : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT Private ProbComp))
    (request : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : (S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × Mode) (privateState : Private)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range request ×
      ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × Mode)) × Private)
    (same : before.2.bundles = before.1.2.nextBundle)
    (reached : result ∈ support ((simulateQ impl
      ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder
        (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) request).run before)).run privateState)) :
    result.1.2.2.bundles = result.1.2.1.2.nextBundle := by
  have executable := callback selected position placeholder (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)
    impl request before privateState result reached
  have chronological := RegistrationNativePlatformIdentityCtxSigningTrace.query_counter frontend request before.1
    (result.1.1, result.1.2.1)
    (callback_support selected position placeholder (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)
      impl request before privateState result reached)
  rw [executable, chronological, same]

/-- Synchronization survives the complete adaptive typed run, so every recorded first-signing ordinal is the executable selector's public bundle ordinal. -/
theorem run_synchronized {S Private : Type} (selected position : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (impl : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT Private ProbComp))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : ((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × Mode) × Private)
    (result : A × (((S × RegistrationNativePlatformIdentityCtxSigningLog.Trace) × Mode) × Private))
    (same : before.1.2.bundles = before.1.1.2.nextBundle)
    (reached : result ∈ support ((simulateQ (QueryImpl.Stateful.link
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder
        (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend)) impl) work).run before)) :
    result.2.1.2.bundles = result.2.1.1.2.nextBundle := by
  apply simulateQ_run_preservesInv _ (fun state => state.1.2.bundles = state.1.1.2.nextBundle) _ work before same result reached
  intro request state prior returned supported
  rw [QueryImpl.Stateful.link_impl_apply_run, support_map] at supported
  obtain ⟨inner, actual, rfl⟩ := supported
  exact synchronized selected position placeholder frontend impl request state.1 state.2 inner prior actual

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.callback_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.callback_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.synchronized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.synchronized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.run_synchronized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleCounter.run_synchronized
