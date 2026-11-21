-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol
/-! The selected identity is recovered from actual public create replies after the identity-free prefix. This executable observer holds public keys only; it neither reads the seed table nor supplies a future private key to the client. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry
open PqxdhJointIdentity (Primitives PublicIdentity IdentitySeed)
open PqxdhDynamicIdentityPool (SourceState DynamicSpec)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
variable {A : Type}
abbrev Registry := Nat → Option PublicIdentity

def empty : Registry := fun _ => none

def note : (query : PublicSpec.Domain) → PublicSpec.Range query → Registry → Registry
  | .inl (.inl (.inr .create)), some (index,identity), before => Function.update before index (some identity)
  | _, _, before => before

def record : QueryImpl PublicSpec (StateT Registry (OracleComp PublicSpec)) := fun query before => do
  let answer ← PublicSpec.query query
  pure (answer,note query answer before)

def keys (joint : Primitives) (before : SourceState) : Registry := fun index =>
  before.seeds[index]?.map joint.publicKeys

private theorem append_keys (joint : Primitives) (before : SourceState) (seed : IdentitySeed) :
    Function.update (keys joint before) before.seeds.length (some (joint.publicKeys seed)) =
      keys joint {before with seeds := before.seeds ++ [seed]} := by
  funext index
  by_cases old : index < before.seeds.length
  · rw [Function.update_of_ne (by omega)]
    simp only [keys,List.getElem?_append_left old]
  · by_cases current : index = before.seeds.length
    · subst index
      rw [Function.update_self]
      simp only [keys,List.getElem?_concat_length,Option.map_some]
    · rw [Function.update_of_ne current]
      have outside : before.seeds.length ≤ index := by omega
      have beyond : (before.seeds ++ [seed]).length ≤ index := by simp only [List.length_append,List.length_singleton]; omega
      simp only [keys,List.getElem?_eq_none outside,List.getElem?_eq_none beyond,Option.map_none]

private theorem pool_query (joint : Primitives) (supply : SourceState → ProbComp (Option IdentitySeed))
    (query : DynamicSpec.Domain) (before : SourceState) (result : DynamicSpec.Range query × SourceState)
    (supported : result ∈ support ((PqxdhDynamicIdentityPool.poolImpl joint supply query).run before)) :
    note (.inl (.inl query)) result.1 (keys joint before) = keys joint result.2 := by
  cases query with
  | inl coin =>
    simp only [PqxdhDynamicIdentityPool.poolImpl,StateT.run,mem_support_bind_iff] at supported
    obtain ⟨answer,_sampled,returned⟩ := supported
    obtain rfl := eq_of_mem_support_pure _ returned
    rfl
  | inr query => cases query with
    | create =>
      simp only [PqxdhDynamicIdentityPool.poolImpl,StateT.run,mem_support_bind_iff] at supported
      obtain ⟨generated,_sampled,returned⟩ := supported
      cases generated with
      | none =>
        obtain rfl := eq_of_mem_support_pure _ returned
        rfl
      | some seed =>
        obtain rfl := eq_of_mem_support_pure _ returned
        exact append_keys joint before seed
    | service handle request | reveal handle =>
      simp only [PqxdhDynamicIdentityPool.poolImpl,StateT.run,mem_support_pure_iff] at supported
      cases supported
      rfl

/-- The literal optional source replies determine the complete public registry, including future/uncreated handles and rejected services. -/
theorem source_query (joint : Primitives) (query : PublicSpec.Domain) (before : SourceState)
    (result : PublicSpec.Range query × SourceState)
    (supported : result ∈ support ((RegistrationNativeIdentityTemplateProtocol.source joint query).run before)) :
    note query result.1 (keys joint before) = keys joint result.2 := by
  rcases query with (dynamic | report) | coin
  · exact pool_query joint (fun _ => some <$> PqxdhJointIdentity.sampleSeed) dynamic before result supported
  · simp only [RegistrationNativeIdentityTemplateProtocol.source,RegistrationNativeIdentityMainSource.implementation,
      StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  · change result ∈ support ((fun answer => (answer,before)) <$> (unifSpec.query coin : ProbComp _)) at supported
    rw [support_map] at supported
    obtain ⟨answer,_sampled,rfl⟩ := supported
    rfl

/-- Forgetting the public registry retains the full original free query tree and every reply. -/
theorem erasure (work : OracleComp PublicSpec A) (before : Registry) :
    Prod.fst <$> (simulateQ record work).run before = work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_spec_query]
    change Prod.fst <$> (do
      let answer ← (PublicSpec.query query : OracleComp PublicSpec _)
      (simulateQ record (next answer)).run (note query answer before)) = _
    rw [map_bind]
    exact bind_congr (fun answer => ih answer (note query answer before))

private theorem map_apply {State X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT State m X) (before : State) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem linked_query (joint : Primitives) (query : PublicSpec.Domain)
    (before : Registry × SourceState) :
    (QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint) query).run before =
      (fun result => (result.1,(note query result.1 before.1,result.2))) <$>
        (RegistrationNativeIdentityTemplateProtocol.source joint query).run before.2 := by
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [record,StateT.run,bind_pure_comp,simulateQ_map,simulateQ_spec_query,map_apply,
    Functor.map_map,QueryImpl.Stateful.Frame.prod]
  rfl

private theorem aligned_query (joint : Primitives) (query : PublicSpec.Domain)
    (before : Registry × SourceState) (aligned : before.1 = keys joint before.2)
    (result : PublicSpec.Range query × (Registry × SourceState))
    (supported : result ∈ support ((QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint) query).run before)) :
    result.2.1 = keys joint result.2.2 := by
  rw [linked_query,support_map] at supported
  obtain ⟨called,reached,rfl⟩ := supported
  rw [aligned]
  exact source_query joint query before.2 called reached

/-- At every reached prefix the executable registry is exactly the public projection of generated source rows. This holds without a selected-row or signing-success premise. -/
theorem source_program (joint : Primitives) (work : OracleComp PublicSpec A)
    (before : Registry × SourceState) (aligned : before.1 = keys joint before.2)
    (result : A × (Registry × SourceState))
    (supported : result ∈ support ((simulateQ (QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint)) work).run before)) :
    result.2.1 = keys joint result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact aligned
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact ih middle.1 middle.2 (aligned_query joint query before aligned middle called) result continued

/-- The public observer adds no primitive request of any class. -/
theorem query_bound (work : OracleComp PublicSpec A) (before : Registry) (predicate : PublicSpec.Domain → Prop) (cap : Nat) [DecidablePred predicate] :
    ((simulateQ record work).run before).IsQueryBoundP predicate cap ↔ work.IsQueryBoundP predicate cap := by
  have same := Iff.of_eq (congrArg (fun code => code.IsQueryBoundP predicate cap) (erasure work before))
  simpa only [isQueryBoundP_map_iff] using same

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.source_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.erasure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.source_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.query_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry.query_bound
