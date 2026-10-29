-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKeyCompiler

/-! Relabelling the private PRK table by the complete dependent key schedule yields the indexed108 table used by the ordinary primitive hybrids. Neither injectivity of the key schedule nor injectivity of any public descriptor is assumed. The actual complete source input remains the table key. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyRelabel
open PqxdhRegistrationJointKemSecondEntry (Spec IState indexedImpl indexed_coin indexed_hit indexed_miss)
open PqxdhRegistrationJointKemEntryFactor (mapCache relabelR mapCache_cacheQuery mapCache_empty)
open PqxdhSecretInputKdf (HmacBlock HmacSha512 HmacOracle)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhServerAuthKeySchedule (Output keySchedule)

theorem indexed_relabel {D R S Result : Type} [DecidableEq D]
    (f : R → S) (draw : Nat → ProbComp R) (client : OracleComp (Spec D S) Result)
    (before : IState D R) :
    Prod.map id (fun table : IState D R => (mapCache f table.1, table.2)) <$>
      (simulateQ (indexedImpl draw) (simulateQ (relabelR f) client)).run before =
      (simulateQ (indexedImpl (fun index => f <$> draw index)) client).run (mapCache f before.1, before.2) := by
  rw [← QueryImpl.simulateQ_compose]
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query state
  cases query with
  | inl coin =>
    change Prod.map id (fun table : IState D R => (mapCache f table.1, table.2)) <$>
      (simulateQ (indexedImpl draw) ((Spec D R).query (.inl coin) : OracleComp (Spec D R) _)).run state = _
    simp only [simulateQ_spec_query, indexed_coin, Functor.map_map, Prod.map, id_eq]
  | inr bytes =>
    change Prod.map id (fun table : IState D R => (mapCache f table.1, table.2)) <$>
      (simulateQ (indexedImpl draw) (f <$> ((Spec D R).query (.inr bytes) : OracleComp (Spec D R) R))).run state = _
    rw [simulateQ_map, simulateQ_spec_query, StateT.run_map]
    cases cached : state.1 bytes with
    | none =>
      have missing : mapCache f state.1 bytes = none := by simp only [mapCache, QueryCache.ofFn_apply, cached, Option.map_none]
      rw [indexed_miss draw bytes state cached,
        indexed_miss (fun index => f <$> draw index) bytes (mapCache f state.1, state.2) missing]
      simp only [map_bind, bind_map_left, map_pure, Prod.map, id_eq, mapCache_cacheQuery]
    | some answer =>
      have hit : mapCache f state.1 bytes = some (f answer) := by
        simp only [mapCache, QueryCache.ofFn_apply, cached, Option.map_some]
      rw [indexed_hit draw bytes state answer cached,
        indexed_hit (fun index => f <$> draw index) bytes (mapCache f state.1, state.2) (f answer) hit]
      simp only [map_pure, Prod.map, id_eq]

/-- Forgetting the indexing counter of the underlying uniform PRK table retains exactly the private source key interpreter. -/
theorem prk_query (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (query : RegistrationNativeKeyCompiler.KeySpec.Domain) (before : IState Pqxdh.Bytes HmacBlock) :
    Prod.map id Prod.fst <$>
      (((indexedImpl (fun _ => ($ᵗ HmacBlock : ProbComp HmacBlock))) ∘ₛ relabelR (keySchedule source hmac)) query).run before =
      (RegistrationNativeKeyCompiler.sourceInterpreter source hmac query).run before.1 := by
  cases query with
  | inl coin =>
    change Prod.map id Prod.fst <$>
      (simulateQ (indexedImpl (fun _ => ($ᵗ HmacBlock : ProbComp HmacBlock)))
        ((Spec Pqxdh.Bytes HmacBlock).query (.inl coin) : OracleComp (Spec Pqxdh.Bytes HmacBlock) _)).run before = _
    simp only [simulateQ_spec_query,
      indexed_coin, RegistrationNativeKeyCompiler.sourceInterpreter, StateT.run_lift, Functor.map_map,
      Prod.map, id_eq, bind_pure_comp]
    rfl
  | inr bytes =>
    change Prod.map id Prod.fst <$>
      (simulateQ (indexedImpl (fun _ => ($ᵗ HmacBlock : ProbComp HmacBlock)))
        (keySchedule source hmac <$> ((Spec Pqxdh.Bytes HmacBlock).query (.inr bytes) :
          OracleComp (Spec Pqxdh.Bytes HmacBlock) HmacBlock))).run before = _
    simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map,
      RegistrationNativeKeyCompiler.sourceInterpreter]
    cases cached : before.1 bytes with
    | none =>
      rw [indexed_miss _ bytes before cached, LazyOracleDiscard.query_of_none cached]
      simp only [map_bind, map_pure, Prod.map, id_eq]
    | some prk =>
      rw [indexed_hit _ bytes before prk cached, LazyOracleDiscard.query_of_some cached]
      simp only [map_pure, Prod.map, id_eq]

theorem prk_program {Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (work : OracleComp RegistrationNativeKeyCompiler.KeySpec Result) (before : IState Pqxdh.Bytes HmacBlock) :
    Prod.map id Prod.fst <$>
      (simulateQ (indexedImpl (fun _ => ($ᵗ HmacBlock : ProbComp HmacBlock)))
        (simulateQ (relabelR (keySchedule source hmac)) work)).run before =
      (simulateQ (RegistrationNativeKeyCompiler.sourceInterpreter source hmac) work).run before.1 := by
  rw [← QueryImpl.simulateQ_compose]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (prk_query source hmac) work before

/-- The actual lazy protected PRKs, expanded at material demand, have exactly the real indexed-key hybrid's ordinary final bit. -/
theorem source_hybrid (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (work : OracleComp RegistrationNativeKeyCompiler.KeySpec Bool) :
    (simulateQ (RegistrationNativeKeyCompiler.sourceInterpreter source hmac) work).run' ∅ =
      RegistrationNativeKeyHybrid.hybrid source hmac work 0 := by
  have direct := prk_program source hmac work (∅, 0)
  have mapped := indexed_relabel (keySchedule source hmac) (fun _ => ($ᵗ HmacBlock : ProbComp HmacBlock)) work (∅, 0)
  have left := congrArg (fun experiment => Prod.fst <$> experiment) direct
  have right := congrArg (fun experiment => Prod.fst <$> experiment) mapped
  simp only [Functor.map_map, Prod.map, id_eq] at left right
  change Prod.fst <$> (simulateQ (RegistrationNativeKeyCompiler.sourceInterpreter source hmac) work).run ∅ = _
  rw [← left]
  have zeroSampler : RegistrationNativeKeyHybrid.sampler source hmac 0 =
      fun _ => keySchedule source hmac <$> ($ᵗ HmacBlock) := by
    funext index
    simp only [RegistrationNativeKeyHybrid.sampler, Nat.not_lt_zero, ite_false]
  simpa only [RegistrationNativeKeyHybrid.hybrid, zeroSampler,
    RegistrationNativeKeyHybrid.empty, StateT.run'_eq, mapCache_empty] using right

end BeaconcryptCore.Computational.RegistrationNativeKeyRelabel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.indexed_relabel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.indexed_relabel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.prk_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.prk_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.prk_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.prk_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.source_hybrid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyRelabel.source_hybrid
