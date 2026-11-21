-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource
import BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting

/-! Independent ambient coins bypass the identity router and both audits. Exact dynamic routing therefore reconstructs the original created seed prefix and literal source transcript, with every family history and complete client result retained. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity)
open PqxdhJointIdentityFamily (familyPublic familyImpl)
open PqxdhJointIdentityFreshness (GlobalSpec GlobalState sourceImpl)
open PqxdhDynamicIdentityPool (DynamicSpec SourceState)
open PqxdhDynamicIdentityRouting (PublicState sourceState projection)
open RegistrationNativeIdentityIndependentSource (Spec)
variable {A : Type}

def routeImpl {count : Nat} (keys : Fin count → PublicIdentity) :
    QueryImpl Spec (StateT PublicState (OracleComp (GlobalSpec count)))
  | .inl query => PqxdhDynamicIdentityRouting.routeImpl keys query
  | .inr coin => StateT.lift ((GlobalSpec count).query (.inl (.inl coin)))

def historyUpdate (count : Nat) : (query : Spec.Domain) → Spec.Range query → GlobalState count → GlobalState count
  | .inl query, reply, before => PqxdhDynamicIdentityRouting.historyUpdate count query reply before
  | .inr _, _, before => before

def historyImpl (count : Nat) : QueryImpl Spec (StateT (GlobalState count) (OracleComp Spec)) := fun query before => do
  let reply ← Spec.query query
  pure (reply, historyUpdate count query reply before)

def sourceWithHistory (count : Nat) (source : QueryImpl Spec (StateT SourceState ProbComp)) :
    QueryImpl Spec (StateT (GlobalState count × SourceState) ProbComp) :=
  QueryImpl.Stateful.link (historyImpl count) source

/-- The extended monitor retains exactly the real source reply and poststate; independent coins make no history entry. -/
theorem sourceWithHistory_run (count : Nat) (source : QueryImpl Spec (StateT SourceState ProbComp))
    (query : Spec.Domain) (history : GlobalState count) (before : SourceState) :
    (sourceWithHistory count source query).run (history, before) =
      (source query).run before >>= fun reply => pure (reply.1, (historyUpdate count query reply.1 history, reply.2)) := by
  rw [sourceWithHistory, QueryImpl.Stateful.link_impl_apply_run]
  simp only [historyImpl, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  change (fun result : (Spec.Range query × GlobalState count) × SourceState => (result.1.1, (result.1.2, result.2))) <$>
    ((source query).run before >>= fun reply => pure ((reply.1, historyUpdate count query reply.1 history), reply.2)) = _
  simp only [map_bind, map_pure]
  rfl

private theorem dynamic_history (primitives : Primitives) {count : Nat} (seeds : Fin count → IdentitySeed)
    (query : DynamicSpec.Domain) (history : GlobalState count) (before : SourceState) :
    (sourceWithHistory count (RegistrationNativeIdentityIndependentSource.eagerImpl primitives (List.ofFn seeds)) (.inl query)).run (history, before) =
      (PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.eagerImpl primitives (List.ofFn seeds)) query).run (history, before) := by
  rw [sourceWithHistory_run, PqxdhDynamicIdentityRouting.sourceWithHistory_run]
  rfl

/-- Every extended query has the exact original source pool and complete family history projection; ambient coins bypass all three audits. -/
theorem projection_step (primitives : Primitives) {count : Nat} (seeds : Fin count → IdentitySeed)
    (query : Spec.Domain) (before : PublicState × GlobalState count) (valid : before.1.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds) query).run before =
      (sourceWithHistory count (RegistrationNativeIdentityIndependentSource.eagerImpl primitives (List.ofFn seeds)) query).run (projection seeds before) := by
  cases query with
  | inl query =>
    change Prod.map id (projection seeds) <$>
      (QueryImpl.Stateful.link (PqxdhDynamicIdentityRouting.routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds) query).run before = _
    rw [dynamic_history]
    exact PqxdhDynamicIdentityRouting.projection_step primitives seeds query before valid
  | inr coin =>
    rcases before with ⟨router, history⟩
    rw [QueryImpl.Stateful.link_impl_apply_run, sourceWithHistory_run]
    simp only [routeImpl, StateT.run, RegistrationNativeIdentityIndependentSource.eagerImpl,
      historyUpdate, bind_pure_comp, Functor.map_map]
    rfl

/-- Public family capacity is preserved without adding any independent coin to the router transcript. -/
theorem routeImpl_preserves_count {count : Nat} (keys : Fin count → PublicIdentity)
    (query : Spec.Domain) (before : PublicState) (valid : before.created ≤ count)
    (result : Spec.Range query × PublicState) (reached : result ∈ support ((routeImpl keys query).run before)) :
    result.2.created ≤ count := by
  cases query with
  | inl query => exact PqxdhDynamicIdentityRouting.routeImpl_preserves_count keys query before valid result reached
  | inr coin =>
    simp only [routeImpl, StateT.run_lift, bind_pure_comp, support_map] at reached
    obtain ⟨reply, _called, rfl⟩ := reached
    exact valid

/-- Closing the real family primitive retains the same router capacity on every actual reply. -/
theorem linked_preserves_count (primitives : Primitives) {count : Nat} (seeds : Fin count → IdentitySeed) :
    QueryImpl.PreservesInv
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds))
      (fun before => before.1.created ≤ count) := by
  rintro query ⟨router, history⟩ valid result reached
  rw [QueryImpl.Stateful.link_impl_apply_run, support_map] at reached
  obtain ⟨inner, called, rfl⟩ := reached
  have publicPossible : inner.1 ∈ support
      ((simulateQ (sourceImpl primitives seeds) ((routeImpl (familyPublic primitives seeds) query).run router)).run' history) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, called, rfl⟩
  exact routeImpl_preserves_count (familyPublic primitives seeds) query router valid inner.1
    (OracleComp.support_simulateQ_run'_subset (sourceImpl primitives seeds) _ history publicPossible)

/-- Arbitrary adaptive extended programs retain the exact private created prefix, original audited transcript, every prior family history and whole client result. -/
theorem route_complete (primitives : Primitives) {count : Nat} (seeds : Fin count → IdentitySeed)
    (client : OracleComp Spec A) (before : PublicState × GlobalState count) (valid : before.1.created ≤ count) :
    Prod.map id (projection seeds) <$>
      (simulateQ (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds)) client).run before =
      (simulateQ (sourceWithHistory count (RegistrationNativeIdentityIndependentSource.eagerImpl primitives (List.ofFn seeds))) client).run
        (projection seeds before) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds))
    (sourceWithHistory count (RegistrationNativeIdentityIndependentSource.eagerImpl primitives (List.ofFn seeds)))
    (fun before => before.1.created ≤ count) (projection seeds)
    (linked_preserves_count primitives seeds) (projection_step primitives seeds) client before valid

/-- The same fully continued routed program derives its final family capacity, retaining arbitrary client/private state in its result. -/
theorem program_count (primitives : Primitives) {count : Nat} (seeds : Fin count → IdentitySeed)
    (client : OracleComp Spec A) (before : PublicState × GlobalState count) (valid : before.1.created ≤ count)
    (result : A × (PublicState × GlobalState count))
    (reached : result ∈ support ((simulateQ
      (QueryImpl.Stateful.link (routeImpl (familyPublic primitives seeds)) (sourceImpl primitives seeds)) client).run before)) :
    result.2.1.created ≤ count :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ _ (linked_preserves_count primitives seeds) client before valid result reached

/-- The exact history observer forwards each original extended request once, preserving every syntactic source class budget. -/
theorem historyRun_query_bound (count : Nat) (client : OracleComp Spec A) (predicate : Spec.Domain → Prop)
    [DecidablePred predicate] (cap : Nat) (bounded : client.IsQueryBoundP predicate cap) (history : GlobalState count) :
    ((simulateQ (historyImpl count) client).run history).IsQueryBoundP predicate cap := by
  apply OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded _ history
  intro query before
  change OracleComp.IsQueryBoundP
    ((fun reply : Spec.Range query => (reply, historyUpdate count query reply before)) <$>
      (Spec.query query : OracleComp Spec _)) predicate _
  rw [OracleComp.isQueryBoundP_map_iff, OracleComp.isQueryBoundP_query_iff]
  split_ifs <;> simp_all

end BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.sourceWithHistory_run' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.sourceWithHistory_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.projection_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.projection_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.routeImpl_preserves_count' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.routeImpl_preserves_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.linked_preserves_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.linked_preserves_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.route_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.route_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.program_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.program_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.historyRun_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting.historyRun_query_bound
