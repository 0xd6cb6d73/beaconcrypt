import BeaconcryptCore.Computational.PqxdhInitialRootContext
import BeaconcryptCore.Computational.PqxdhInitialFusedOwner

/-!
The initializer observer has a private response-only root service. A request names either a root-family coordinate or a locally known root. The selected coordinate returns the supplied64-byte response without revealing the selected root; every other request uses its actual real initializer and the original uniform-root cache. Repeated selected coordinates reuse the supplied response. Source interpretation reconstructs the selected cache entry privately. This operational source law is not a claim that different coordinates cannot have equal root bytes; such aliases remain explicit events for the comparison hybrid.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootLabelService
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhCorrelatedExtractFamily PqxdhInitialResponseService

inductive Request where
  | known : RootOutput → Request
  | family : Message → Request
abbrev Response := pqxdh.concrete.InitialRatchetKdfResponse
abbrev InitialOracle : OracleSpec Request := fun _ => Response
abbrev Spec {ι : Type} (base : OracleSpec ι) := base + InitialOracle
variable {ι Result : Type} {base : OracleSpec ι}

noncomputable def realInitial (fixed : FixedHkdfSha512NoSaltSource) (root : RootOutput) : Response :=
  RawCtxSourceHkdf.initialResponse fixed.crypto (pending false root).request

def completeCache (selected : Message) (root : RootOutput) (cache : RootOracle.QueryCache) : RootOracle.QueryCache :=
  cache.cacheQuery selected root

noncomputable def native (fixed : FixedHkdfSha512NoSaltSource) :
    QueryImpl InitialOracle (StateT RootOracle.QueryCache ProbComp)
  | .known root => pure (realInitial fixed root)
  | .family message => fun cache => do
      let result ← (uniformImpl (.inr message)).run cache
      pure (realInitial fixed result.1, result.2)

noncomputable def labelled (fixed : FixedHkdfSha512NoSaltSource) (selected : Message) (response : Response) :
    QueryImpl InitialOracle (StateT RootOracle.QueryCache ProbComp)
  | .known root => pure (realInitial fixed root)
  | .family message => if message = selected then pure response else native fixed (.family message)

/-- Repeated selected coordinates return the same supplied response and leave the entire nonselected cache unchanged; no selected root is an argument of this executable service. -/
theorem selected_reply (fixed : FixedHkdfSha512NoSaltSource) (selected : Message) (response : Response)
    (cache : RootOracle.QueryCache) :
    (labelled fixed selected response (.family selected)).run cache = pure (response, cache) := by
  simp [labelled]

/-- Reconstructing the selected private entry commutes with recording a different actual coordinate. -/
theorem cache_record (selected message : Message) (root value : RootOutput)
    (cache : RootOracle.QueryCache) (different : message ≠ selected) :
    completeCache selected root (cache.cacheQuery message value) =
      (completeCache selected root cache).cacheQuery message value := by
  refine QueryCache.ext (fun other => ?_)
  by_cases hselected : other = selected
  · subst other
    simp [completeCache, QueryCache.cacheQuery_of_ne, Ne.symm different]
  · by_cases hmessage : other = message
    · subst other
      simp [completeCache, QueryCache.cacheQuery_of_ne, different]
    · simp [completeCache, QueryCache.cacheQuery_of_ne, hselected, hmessage]

set_option backward.isDefEq.respectTransparency false in
/-- At every original response-only request, private reconstruction of the selected root cache recovers the exact native service and complete cache result. -/
theorem native_step (fixed : FixedHkdfSha512NoSaltSource) (selected : Message) (root : RootOutput)
    (query : InitialOracle.Domain) (cache : RootOracle.QueryCache) :
    Prod.map id (completeCache selected root) <$>
      (labelled fixed selected (realInitial fixed root) query).run cache =
        (native fixed query).run (completeCache selected root cache) := by
  cases query with
  | known value => rfl
  | family message =>
      by_cases same : message = selected
      · subst message
        have hit : completeCache selected root cache selected = some root := by simp [completeCache]
        have sampled : (uniformImpl (.inr selected)).run (completeCache selected root cache) =
            pure (root, completeCache selected root cache) := by
          simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
            QueryImpl.withCaching_run_some _ hit]
        rw [selected_reply]
        change Prod.map id (completeCache selected root) <$> pure (realInitial fixed root, cache) =
          (do let result ← (uniformImpl (.inr selected)).run (completeCache selected root cache)
              pure (realInitial fixed result.1, result.2))
        rw [sampled]
        rfl
      · have lookup : completeCache selected root cache message = cache message := by
          simp [completeCache, QueryCache.cacheQuery_of_ne, same]
        simp only [labelled, same, ite_false]
        change Prod.map id (completeCache selected root) <$>
          (do let result ← (uniformImpl (.inr message)).run cache
              pure (realInitial fixed result.1, result.2)) =
          (do let result ← (uniformImpl (.inr message)).run (completeCache selected root cache)
              pure (realInitial fixed result.1, result.2))
        cases hit : cache message with
        | some value =>
            have fullHit : completeCache selected root cache message = some value := lookup.trans hit
            simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
              QueryImpl.withCaching_run_some _ hit, QueryImpl.withCaching_run_some _ fullHit,
              pure_bind, map_pure]
            rfl
        | none =>
            have fullMiss : completeCache selected root cache message = none := lookup.trans hit
            simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
              QueryImpl.withCaching_run_none _ hit, QueryImpl.withCaching_run_none _ fullMiss,
              uniformSampleImpl, bind_map_left, map_bind, map_pure]
            apply bind_congr
            intro value
            simp only [Prod.map, id_eq, cache_record selected message root value cache same]

noncomputable def nativeFull (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl base ProbComp) :
    QueryImpl (Spec base) (StateT RootOracle.QueryCache ProbComp) :=
  baseImpl.liftTarget (StateT RootOracle.QueryCache ProbComp) + native fixed

noncomputable def labelledFull (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl base ProbComp)
    (selected : Message) (response : Response) : QueryImpl (Spec base) (StateT RootOracle.QueryCache ProbComp) :=
  baseImpl.liftTarget (StateT RootOracle.QueryCache ProbComp) + labelled fixed selected response

/-- Every ordinary callback stays the same real computation, and only the selected private cache entry is reconstructed for the full response-only interface. -/
theorem full_step (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl base ProbComp)
    (selected : Message) (root : RootOutput) (query : (Spec base).Domain) (cache : RootOracle.QueryCache) :
    Prod.map id (completeCache selected root) <$>
      (labelledFull fixed baseImpl selected (realInitial fixed root) query).run cache =
        (nativeFull fixed baseImpl query).run (completeCache selected root cache) := by
  cases query with
  | inl query =>
      simp only [labelledFull, nativeFull, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply]
      rw [StateT.run_liftM, StateT.run_liftM]
      simp only [bind_pure_comp, Functor.map_map]
      rfl
  | inr query => exact native_step fixed selected root query cache

/-- Every complete adaptive continuation recovers the native source under private cache reconstruction, including all replies, local work and final nonselected cache entries. -/
theorem complete_source (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl base ProbComp)
    (selected : Message) (root : RootOutput) (client : OracleComp (Spec base) Result)
    (cache : RootOracle.QueryCache) :
    Prod.map id (completeCache selected root) <$>
      (simulateQ (labelledFull fixed baseImpl selected (realInitial fixed root)) client).run cache =
        (simulateQ (nativeFull fixed baseImpl) client).run (completeCache selected root cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (full_step fixed baseImpl selected root) client cache

/-- The actual first-miss root cache is reconstructed from an empty observer cache, while the observer receives only the initializer response. -/
theorem empty_source (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl base ProbComp)
    (selected : Message) (root : RootOutput) (client : OracleComp (Spec base) Result) :
    (simulateQ (labelledFull fixed baseImpl selected (realInitial fixed root)) client).run' ∅ =
      (simulateQ (nativeFull fixed baseImpl) client).run' ((∅ : RootOracle.QueryCache).cacheQuery selected root) := by
  have same := congrArg (Functor.map Prod.fst) (complete_source fixed baseImpl selected root client ∅)
  simpa only [StateT.run'_eq, Functor.map_map, Prod.map_fst, id_eq, completeCache] using same

set_option backward.isDefEq.respectTransparency false in
/-- Each labelled private initializer costs at most32 uniform-byte queries: known roots, selected coordinates and cache hits are pure; only a nonselected fresh root draws bytes. Real HKDF and cache work remain local computation. -/
theorem labelled_uniform_bound (fixed : FixedHkdfSha512NoSaltSource) (selected : Message)
    (response : Response) (query : InitialOracle.Domain) (cache : RootOracle.QueryCache) :
    ((labelled fixed selected response query).run cache).IsTotalQueryBound 32 := by
  cases query with
  | known root => trivial
  | family message =>
      by_cases same : message = selected
      · subst message
        rw [selected_reply]
        trivial
      · simp only [labelled, same, ite_false]
        change (do let result ← (uniformImpl (.inr message)).run cache
                   pure (realInitial fixed result.1, result.2)).IsTotalQueryBound 32
        cases found : cache message with
        | some value =>
            simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
              QueryImpl.withCaching_run_some _ found, pure_bind]
            trivial
        | none =>
            simp only [uniformImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle,
              QueryImpl.withCaching_run_none _ found, uniformSampleImpl, bind_pure_comp,
              IsTotalQueryBound, isQueryBound_map_iff]
            exact CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

end BeaconcryptCore.Computational.PqxdhInitialRootLabelService

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.selected_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.selected_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.cache_record' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.cache_record

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.native_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.full_step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.complete_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.empty_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.empty_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootLabelService.labelled_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootLabelService.labelled_uniform_bound
