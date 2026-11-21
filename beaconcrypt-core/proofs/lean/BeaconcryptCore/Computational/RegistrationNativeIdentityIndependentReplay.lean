-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistory

/-! The monitored independent-coin source retains exactly the full family history reconstructed from its literal original dynamic transcript. Independent coins append neither a source observation nor a history event. Both lazy creation and reserved eager creation retain all optional replies and rejected paths. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay
open RegistrationNativeIdentityIndependentSource (Spec lazyImpl eagerImpl)
open RegistrationNativeIdentityIndependentRouting (historyUpdate sourceWithHistory)
open PqxdhDynamicIdentityPool (SourceState Observation DynamicSpec)
open PqxdhJointIdentityFreshness (GlobalState)
variable {A : Type}

private def observation : (query : Spec.Domain) → Spec.Range query → List Observation
  | .inl query, reply => [⟨query, reply⟩]
  | .inr _, _ => []

private def Tape (source : QueryImpl Spec (StateT SourceState ProbComp)) : Prop :=
  ∀ query before result, result ∈ support ((source query).run before) →
    result.2.transcript = before.transcript ++ observation query result.1

private theorem lazy_tape (joint : PqxdhJointIdentity.Primitives) : Tape (lazyImpl joint) := by
  intro query before result reached
  cases query with
  | inl query => exact PqxdhDynamicIdentityPool.lazyImpl_transcript joint query before result reached
  | inr coin =>
    rw [RegistrationNativeIdentityIndependentSource.independent, support_map] at reached
    obtain ⟨reply, _sampled, rfl⟩ := reached
    exact (List.append_nil _).symm

private theorem eager_tape (joint : PqxdhJointIdentity.Primitives) (pool : List PqxdhJointIdentity.IdentitySeed) :
    Tape (eagerImpl joint pool) := by
  intro query before result reached
  cases query with
  | inr coin =>
    rw [RegistrationNativeIdentityIndependentSource.eager_independent] at reached
    exact lazy_tape joint (.inr coin) before result reached
  | inl query =>
    change result ∈ support ((PqxdhDynamicIdentityPool.eagerImpl joint pool query).run before) at reached
    by_cases creates : PqxdhDynamicIdentityPool.IsCreate query
    · have shape : query = .inr .create := by
        cases query with
        | inl coin => cases creates
        | inr query => cases query <;> first | rfl | cases creates
      subst query
      simp only [PqxdhDynamicIdentityPool.eagerImpl, PqxdhDynamicIdentityPool.poolImpl, StateT.run, pure_bind] at reached
      cases supplied : pool[before.seeds.length]? with
      | none =>
        simp only [supplied, mem_support_pure_iff] at reached
        cases reached
        rfl
      | some seed =>
        simp only [supplied, mem_support_pure_iff] at reached
        cases reached
        rfl
    · rw [← PqxdhDynamicIdentityPool.noncreate_step_eq joint pool query creates before] at reached
      exact PqxdhDynamicIdentityPool.lazyImpl_transcript joint query before result reached

private theorem replay_step (count : Nat) (transcript : List Observation) (query : Spec.Domain) (reply : Spec.Range query) :
    RegistrationNativeIdentityHistory.replay count (transcript ++ observation query reply) =
      historyUpdate count query reply (RegistrationNativeIdentityHistory.replay count transcript) := by
  cases query with
  | inl query =>
    simp only [RegistrationNativeIdentityHistory.replay, observation, List.foldl_append, List.foldl_cons, List.foldl_nil, historyUpdate]
  | inr coin => simp only [observation, List.append_nil, historyUpdate]

private def Consistent (count : Nat) (before : GlobalState count × SourceState) : Prop :=
  before.1 = RegistrationNativeIdentityHistory.replay count before.2.transcript

private theorem step (count : Nat) (source : QueryImpl Spec (StateT SourceState ProbComp)) (tape : Tape source)
    (query : Spec.Domain) (before : GlobalState count × SourceState) (prior : Consistent count before)
    (result : Spec.Range query × (GlobalState count × SourceState))
    (reached : result ∈ support ((sourceWithHistory count source query).run before)) : Consistent count result.2 := by
  rw [RegistrationNativeIdentityIndependentRouting.sourceWithHistory_run, mem_support_bind_iff] at reached
  obtain ⟨inner, called, returned⟩ := reached
  simp only [mem_support_pure_iff] at returned
  cases returned
  change historyUpdate count query inner.1 before.1 = RegistrationNativeIdentityHistory.replay count inner.2.transcript
  change before.1 = RegistrationNativeIdentityHistory.replay count before.2.transcript at prior
  rw [prior, tape query before.2 inner called, replay_step]

private theorem program (count : Nat) (source : QueryImpl Spec (StateT SourceState ProbComp)) (tape : Tape source)
    (client : OracleComp Spec A) (before : GlobalState count × SourceState) (prior : Consistent count before)
    (result : A × (GlobalState count × SourceState))
    (reached : result ∈ support ((simulateQ (sourceWithHistory count source) client).run before)) : Consistent count result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (sourceWithHistory count source) (Consistent count)
    (step count source tape) client before prior result reached

/-- Actual initialized on-demand creation gives exactly the original source-transcript family replay, jointly with every full client and private state result. -/
theorem lazy_initialized (joint : PqxdhJointIdentity.Primitives) (count : Nat) (client : OracleComp Spec A)
    (result : A × (GlobalState count × SourceState))
    (reached : result ∈ support ((simulateQ (sourceWithHistory count (lazyImpl joint)) client).run
      (PqxdhJointIdentityFreshness.initialState count, PqxdhDynamicIdentityPool.initialState))) :
    result.2.1 = RegistrationNativeIdentityHistory.replay count result.2.2.transcript :=
  program count (lazyImpl joint) (lazy_tape joint) client (PqxdhJointIdentityFreshness.initialState count, PqxdhDynamicIdentityPool.initialState) rfl result reached

/-- Actual initialized eager reservation has that same complete source-transcript replay, including exhausted or rejected requests and independent ambient coins. -/
theorem eager_initialized (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (pool : List PqxdhJointIdentity.IdentitySeed) (client : OracleComp Spec A)
    (result : A × (GlobalState count × SourceState))
    (reached : result ∈ support ((simulateQ (sourceWithHistory count (eagerImpl joint pool)) client).run
      (PqxdhJointIdentityFreshness.initialState count, PqxdhDynamicIdentityPool.initialState))) :
    result.2.1 = RegistrationNativeIdentityHistory.replay count result.2.2.transcript :=
  program count (eagerImpl joint pool) (eager_tape joint pool) client (PqxdhJointIdentityFreshness.initialState count, PqxdhDynamicIdentityPool.initialState) rfl result reached

/-- The literal linked reserved-family router retains that same complete source-history replay, without a caller projection or history invariant. -/
theorem routed_initialized (joint : PqxdhJointIdentity.Primitives) {count : Nat}
    (seeds : Fin count → PqxdhJointIdentity.IdentitySeed) (client : OracleComp Spec A)
    (result : A × (PqxdhDynamicIdentityRouting.PublicState × GlobalState count))
    (reached : result ∈ support ((simulateQ
      (QueryImpl.Stateful.link (RegistrationNativeIdentityIndependentRouting.routeImpl (PqxdhJointIdentityFamily.familyPublic joint seeds))
        (PqxdhJointIdentityFreshness.sourceImpl joint seeds)) client).run
      (PqxdhDynamicIdentityRouting.initialPublicState, PqxdhJointIdentityFreshness.initialState count))) :
    result.2.2 = RegistrationNativeIdentityHistory.replay count result.2.1.transcript := by
  have viewed := Set.mem_image_of_mem (Prod.map id (PqxdhDynamicIdentityRouting.projection seeds)) reached
  rw [← support_map, RegistrationNativeIdentityIndependentRouting.route_complete joint seeds client
    (PqxdhDynamicIdentityRouting.initialPublicState, PqxdhJointIdentityFreshness.initialState count) (Nat.zero_le count)] at viewed
  exact eager_initialized joint count (List.ofFn seeds) client (result.1, PqxdhDynamicIdentityRouting.projection seeds result.2) viewed

end BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay.lazy_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay.lazy_initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay.eager_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay.eager_initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay.routed_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentReplay.routed_initialized
