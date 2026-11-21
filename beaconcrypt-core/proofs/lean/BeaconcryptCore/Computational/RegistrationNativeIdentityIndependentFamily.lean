-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentRouting
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily
open PqxdhDynamicIdentityPool (DynamicSpec SourceState)
open RegistrationNativeIdentityIndependentSource (Spec IsCreate lazyImpl eagerImpl independent)
open RegistrationNativeIdentityIndependentRouting (sourceWithHistory historyImpl routeImpl)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointIdentityFamily (sampleFamily familyPublic)
open PqxdhJointIdentityFreshness (GlobalState initialState sourceImpl)
open PqxdhDynamicIdentityRouting (PublicState initialPublicState projection)
variable {A : Type}
private theorem create_dynamic (query : DynamicSpec.Domain) : IsCreate (.inl query) ↔ PqxdhDynamicIdentityPool.IsCreate query := by
  cases query with
  | inl coin => rfl
  | inr query => cases query <;> rfl

private theorem noncreate_step_eq (joint : PqxdhJointIdentity.Primitives) (pool : List PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (notCreate : ¬ IsCreate query) (before : SourceState) :
    (lazyImpl joint query).run before = (eagerImpl joint pool query).run before := by
  cases query with
  | inr coin => rfl
  | inl query =>
    exact PqxdhDynamicIdentityPool.noncreate_step_eq joint pool query ((create_dynamic query).not.mp notCreate) before

private theorem noncreate_seeds (joint : PqxdhJointIdentity.Primitives)
    (query : Spec.Domain) (notCreate : ¬ IsCreate query) (before : SourceState)
    (result : Spec.Range query × SourceState)
    (supported : result ∈ support ((lazyImpl joint query).run before)) : result.2.seeds = before.seeds := by
  cases query with
  | inl query => exact PqxdhDynamicIdentityPool.noncreate_seeds_preserved joint query ((create_dynamic query).not.mp notCreate) before result supported
  | inr coin =>
    rw [independent, support_map] at supported
    obtain ⟨answer, _sampled, rfl⟩ := supported
    rfl

/-- Reserving the future generated-key family first preserves the complete dynamic execution while independent ambient coins remain outside its source audit. -/
theorem lazy_eager_complete (joint : PqxdhJointIdentity.Primitives)
    (client : OracleComp Spec A) (count : Nat) (bounded : client.IsQueryBoundP IsCreate count) (before : SourceState) :
    EvalDistEq ((simulateQ (lazyImpl joint) client).run before)
      (PqxdhDynamicIdentityPool.sampleSeeds count >>= fun future =>
        (simulateQ (eagerImpl joint (before.seeds ++ future)) client).run before) := by
  induction client using OracleComp.inductionOn generalizing count before with
  | pure value =>
    simpa only [simulateQ_pure, StateT.run_pure] using
      (PqxdhDynamicIdentityPool.sampleSeeds_unused count (pure (value, before))).symm
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    change EvalDistEq ((lazyImpl joint query).run before >>= fun result =>
      (simulateQ (lazyImpl joint) (next result.1)).run result.2)
      (PqxdhDynamicIdentityPool.sampleSeeds count >>= fun future =>
        (eagerImpl joint (before.seeds ++ future) query).run before >>= fun result =>
          (simulateQ (eagerImpl joint (before.seeds ++ future)) (next result.1)).run result.2)
    by_cases creates : IsCreate query
    · have queryEq : query = .inl (.inr .create) := by
        cases query with
        | inr coin => exact False.elim creates
        | inl query => cases query with
          | inl coin => exact False.elim creates
          | inr request => cases request <;> simp_all [IsCreate]
      subst query
      have positive : 0 < count := bounded.1.resolve_left (not_not.mpr creates)
      cases count with
      | zero => omega
      | succ count =>
        simp only [lazyImpl,eagerImpl]
        rw [PqxdhDynamicIdentityPool.lazyImpl_create,PqxdhDynamicIdentityPool.sampleSeeds_succ]
        simp only [bind_assoc,bind_map_left,pure_bind]
        refine EvalDistEq.bind_right PqxdhJointIdentity.sampleSeed fun seed => ?_
        simp only [PqxdhDynamicIdentityPool.eagerImpl_create joint before seed, pure_bind]
        simpa only [PqxdhDynamicIdentityPool.createdReply,PqxdhDynamicIdentityPool.record,List.append_assoc,List.singleton_append] using
          ih (PqxdhDynamicIdentityPool.createdReply joint before seed).1 count
            (by simpa [IsCreate] using bounded.2 (PqxdhDynamicIdentityPool.createdReply joint before seed).1)
            (PqxdhDynamicIdentityPool.createdReply joint before seed).2
    · have stepEq (future : List PqxdhJointIdentity.IdentitySeed) :=
        noncreate_step_eq joint (before.seeds ++ future) query creates before
      simp_rw [← stepEq]
      refine EvalDistEq.trans ?_ (PqxdhSecretInputKdf.evalSPMF_sample_comm (PqxdhDynamicIdentityPool.sampleSeeds count)
        ((lazyImpl joint query).run before) _).symm
      refine OracleComp.EvalDistEq.bind_congr_of_support _ fun result supported => ?_
      have sameSeeds := noncreate_seeds joint query creates before result supported
      simpa only [sameSeeds] using
        ih result.1 count (by simpa [creates] using bounded.2 result.1) result.2


/-- Exact family-history instrumentation erases without changing the full source result or pool transcript. -/
theorem history_erasure (count : Nat) (source : QueryImpl Spec (StateT SourceState ProbComp))
    (client : OracleComp Spec A) (before : GlobalState count × SourceState) :
    Prod.map id Prod.snd <$> (simulateQ (sourceWithHistory count source) client).run before =
      (simulateQ source client).run before.2 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  rw [RegistrationNativeIdentityIndependentRouting.sourceWithHistory_run]
  simp only [Prod.map_def,id_eq,bind_pure_comp,Functor.map_map]
  exact id_map _

/-- The full monitored dynamic source remains joint with its future reserved family when ambient randomness bypasses the pool audit. -/
theorem lazy_eager_history_complete (joint : PqxdhJointIdentity.Primitives)
    (count : Nat) (client : OracleComp Spec A) (bounded : client.IsQueryBoundP IsCreate count)
    (history : GlobalState count) (before : SourceState) :
    EvalDistEq ((simulateQ (sourceWithHistory count (lazyImpl joint)) client).run (history,before))
      (PqxdhDynamicIdentityPool.sampleSeeds count >>= fun future =>
        (simulateQ (sourceWithHistory count (eagerImpl joint (before.seeds ++ future))) client).run (history,before)) := by
  have law := lazy_eager_complete joint ((simulateQ (historyImpl count) client).run history) count
    (RegistrationNativeIdentityIndependentRouting.historyRun_query_bound count client IsCreate count bounded history) before
  have mapped := law.map
    (fun value : (A × GlobalState count) × SourceState => (value.1.1,(value.1.2,value.2)))
  simp_rw [sourceWithHistory,QueryImpl.Stateful.simulateQ_link_run]
  change EvalDistEq ((fun value : (A × GlobalState count) × SourceState => (value.1.1,(value.1.2,value.2))) <$>
    (simulateQ (lazyImpl joint) ((simulateQ (historyImpl count) client).run history)).run before)
    (PqxdhDynamicIdentityPool.sampleSeeds count >>= fun future =>
      (fun value : (A × GlobalState count) × SourceState => (value.1.1,(value.1.2,value.2))) <$>
        (simulateQ (eagerImpl joint (before.seeds ++ future)) ((simulateQ (historyImpl count) client).run history)).run before)
  simpa only [map_bind] using mapped

noncomputable def dynamicRun (joint : PqxdhJointIdentity.Primitives) (count : Nat) (client : OracleComp Spec A) :
    ProbComp (A × (GlobalState count × SourceState)) :=
  (simulateQ (sourceWithHistory count (lazyImpl joint)) client).run
    (initialState count,PqxdhDynamicIdentityPool.initialState)

noncomputable def reservedRun (joint : PqxdhJointIdentity.Primitives) (count : Nat) (client : OracleComp Spec A) :
    ProbComp (A × (GlobalState count × SourceState)) := do
  let seeds ← sampleFamily count
  let result ← (simulateQ (QueryImpl.Stateful.link (routeImpl (familyPublic joint seeds)) (sourceImpl joint seeds)) client).run
    (initialPublicState,initialState count)
  pure (result.1,projection seeds result.2)

/-- The actual complete on-demand source and finite public router have the same evaluated execution; every original pool observation and private result is retained. -/
theorem dynamic_reserved_complete (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (client : OracleComp Spec A) (bounded : client.IsQueryBoundP IsCreate count) :
    EvalDistEq (dynamicRun joint count client) (reservedRun joint count client) := by
  rw [dynamicRun]
  refine (lazy_eager_history_complete joint count client bounded _ _).trans ?_
  simp only [PqxdhDynamicIdentityPool.initialState,List.nil_append,
    PqxdhDynamicIdentityPool.sampleSeeds,bind_map_left,reservedRun,bind_pure_comp]
  refine EvalDistEq.bind_right _ fun seeds => ?_
  have exactRun := RegistrationNativeIdentityIndependentRouting.route_complete joint seeds client
    (initialPublicState,initialState count) (Nat.zero_le count)
  change EvalDistEq ((simulateQ (sourceWithHistory count (eagerImpl joint (List.ofFn seeds))) client).run
    (projection seeds (initialPublicState,initialState count))) _
  rw [← exactRun]
  exact EvalDistEq.rfl
end BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.lazy_eager_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.lazy_eager_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.history_erasure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.history_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.lazy_eager_history_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.lazy_eager_history_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.dynamic_reserved_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentFamily.dynamic_reserved_complete
