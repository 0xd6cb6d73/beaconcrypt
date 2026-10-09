-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashNative
import BeaconcryptCore.Computational.PqxdhRecordFactsDigestCache
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle

/-! Actual shared-hash calls in the combined private/ordinary digest experiment. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashShared
open CtxRomAuth AdaptiveCtxSharedHash
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec HashInput)
open PqxdhRecordFactsDigestCache (cacheOf withShared)
variable {n : Nat}

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X)
    (state : S) : (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state :=
  StateT.run_map f work state

/-- Forward the literal hash input and finite coins, retaining the source's shared-cache copy. -/
noncomputable def compile : QueryImpl HashSpec (StateT (CtxPrivate n) (OracleComp (Spec n)))
  | .inl coin => fun state => (fun reply => (reply, state)) <$> (Spec n).query (.inr coin)
  | .inr ((), bytes) => fun state => do
      let digest ← (Spec n).query (.inl (.inr bytes))
      pure (digest, withShared state (state.base.primitive.2.cacheQuery ((), bytes) digest))

/-- The source endpoint touches only its actual shared ROM, retaining every other private field. -/
noncomputable def source : QueryImpl HashSpec (StateT (CtxPrivate n) ProbComp) :=
  fun query state => (fun result => (result.1, withShared state result.2)) <$>
    (hashImpl query).run state.base.primitive.2

/-- One compiled shared query preserves both the full source state and its coherent combined cache. -/
theorem query_exact (query : HashSpec.Domain) (state : CtxPrivate n) :
    (simulateQ PqxdhRecordFactsCollisionOracle.plain ((compile query).run state)).run (cacheOf state) =
      (fun result => (result, cacheOf result.2)) <$> (source query).run state := by
  cases query with
  | inl coin =>
      have coin_run : (hashImpl (.inl coin)).run state.base.primitive.2 =
          (fun reply => (reply, state.base.primitive.2)) <$> (unifSpec.query coin : ProbComp _) := by
        change ((unifSpec.query coin : ProbComp _) >>= fun reply => pure (reply, state.base.primitive.2)) = _
        exact bind_pure_comp _ _
      simp only [compile, source, StateT.run, simulateQ_map, simulateQ_spec_query,
        map_apply, PqxdhRecordFactsCollisionOracle.plain, Functor.map_map]
      simp only [StateT.run] at coin_run
      rw [coin_run]
      simp only [Functor.map_map, withShared, Prod.eta]
      rfl
  | inr query =>
      rcases query with ⟨⟨⟩, bytes⟩
      simp only [compile, source, StateT.run, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, map_apply, Functor.map_map]
      change (fun result => ((result.1, withShared state
          (state.base.primitive.2.cacheQuery ((), bytes) result.1)), result.2)) <$>
        (uniformSampleImpl.withCaching (.inr bytes)).run (cacheOf state) =
          (fun result => ((result.1, withShared state result.2), cacheOf (withShared state result.2))) <$>
            (uniformSampleImpl.withCaching ((), bytes)).run state.base.primitive.2
      cases hit : state.base.primitive.2 ((), bytes)
      case none =>
        have combined : cacheOf state (.inr bytes) = none := hit
        rw [QueryImpl.withCaching_run_none _ combined, QueryImpl.withCaching_run_none _ hit]
        simp only [Functor.map_map, PqxdhRecordFactsDigestCache.cacheOf_shared_query]
        rfl
      case some digest =>
        have combined : cacheOf state (.inr bytes) = some digest := hit
        rw [QueryImpl.withCaching_run_some _ combined, QueryImpl.withCaching_run_some _ hit]
        simp only [map_pure]
        have unchanged : state.base.primitive.2.cacheQuery ((), bytes) digest = state.base.primitive.2 := by
          funext query
          by_cases same : query = ((), bytes)
          · subst query; simp [hit]
          · simp [QueryCache.cacheQuery, same]
        rw [unchanged]
        rfl

/-- The combined memoizing interpreter preserves the complete adaptive shared-hash continuation and coherent source cache. -/
theorem program_exact {X : Type} (client : OracleComp HashSpec X) (state : CtxPrivate n) :
    (simulateQ PqxdhRecordFactsCollisionOracle.plain ((simulateQ compile client).run state)).run (cacheOf state) =
      (fun result => (result, cacheOf result.2)) <$> (simulateQ source client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_exact]
      simp only [bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

/-- The source framing is exactly the original shared oracle with every unrelated private field retained. -/
theorem source_program {X : Type} (client : OracleComp HashSpec X) (state : CtxPrivate n) :
    (simulateQ source client).run state =
      (fun result => (result.1, withShared state result.2)) <$>
        (simulateQ hashImpl client).run state.base.primitive.2 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [StateT.run, source, bind_map_left, map_bind]
      apply bind_congr
      intro result
      exact ih result.1 (withShared state result.2)

open PqxdhServerAuthExperiment (Setup Codec)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Reinstall the actual native bill and writer log around the already retained shared-cache poststate. -/
def finishNative {X : Type}
    (result : (X × (PqxdhRecordLiftWorld.Counts × PqxdhRecordLiftLoggedAdapters.Frames)) × CtxPrivate n) :
    X × CtxPrivate n :=
  (result.1.1, { result.2 with base := { result.2.base with
    primitive := (result.1.2.1, result.2.base.primitive.2)
    pending := result.1.2.2 } })

/-- Compile every actual native record callback, preserving its counters, writer log and shared queries. -/
noncomputable def nativeProgram (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {X : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : CtxPrivate n) :
    OracleComp (Spec n) (X × CtxPrivate n) :=
  finishNative <$> (simulateQ compile
    (PqxdhRecordFactsHashNative.loggedProgram setup codec client
      (state.base.primitive.1, state.base.pending))).run state

/-- The combined compiler returns the literal native program result, full private state and coherent cache, including unsuccessful publication. -/
theorem nativeProgram_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {X : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : CtxPrivate n) :
    (simulateQ PqxdhRecordFactsCollisionOracle.plain (nativeProgram setup codec client state)).run (cacheOf state) =
      (fun result => (result, cacheOf result.2)) <$>
        (PqxdhRecordLiftIdeal.onBase (PqxdhRecordLiftProtocol.withRecord
          (PqxdhRecordLiftProtocol.primitiveWork
            (simulateQ (PqxdhRecordLiftLoggedAdapters.loggedNative
              (PqxdhRecordFactsCounter.primitives setup codec)) client)))).run state := by
  rw [nativeProgram, simulateQ_map, StateT.run_map, program_exact, source_program]
  simp only [Functor.map_map]
  have same := congrArg (fun work => (fun result : X ×
      (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames) =>
    let post := { state with base := { state.base with primitive := result.2.1, pending := result.2.2 } }
    ((result.1, post), cacheOf post)) <$> work)
    (PqxdhRecordFactsHashNative.loggedProgram_exact setup codec client
      (state.base.primitive, state.base.pending))
  simp only [PqxdhRecordLiftIdeal.onBase, PqxdhRecordLiftProtocol.withRecord,
    PqxdhRecordLiftProtocol.primitiveWork, PqxdhRecordLiftProtocol.recordState,
    PqxdhRecordLiftProtocol.putRecord, StateT.run, bind_pure_comp, Functor.map_map,
    finishNative, withShared] at same ⊢
  convert same using 1
  congr 1

/-- The shared compiler forwards at most one actual hash or finite-coin request per input query. Memoized digest sampling is a separate interpreter cost. -/
theorem compile_queries (query : HashSpec.Domain) (state : CtxPrivate n) :
    ((compile query).run state).IsTotalQueryBound 1 := by
  cases query with
  | inl coin => simp [compile, StateT.run, IsTotalQueryBound]
  | inr query => rcases query with ⟨⟨⟩, bytes⟩; simp [compile, StateT.run, IsTotalQueryBound]

end BeaconcryptCore.Computational.PqxdhRecordFactsHashShared

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.query_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.query_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.program_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.program_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.source_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.nativeProgram_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.nativeProgram_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.compile_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashShared.compile_queries
