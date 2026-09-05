import BeaconcryptCore.Computational.PqxdhJointKdfGame
import VCVio.OracleComp.QueryTracking.Birthday
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# PQXDH joint-HKDF projection collisions

This module separates the canonical identity of each source-visible projection from its byte
value. Repeating one identity, including the required initial/step aliases at one exact ratchet
address, is intentional cache equality. A collision is bad only when two distinct visible
identities have the same value.

The random model exposes a 76-byte answer as independent 32-byte first, 32-byte second, and
12-byte final coordinates. It records the exact source calls `root`, `initial`, `step`, and a
single public projection without inventing protocol labels or fixed protocol call counts.
The real-world inequality retains the legacy fixed-public-HKDF/random-table advantage, which is efficiently large in general (`PqxdhPublicKdfCounterexample`). Thus the birthday bound is a random-table result; this module does not discharge computational output noncollision of production HKDF. A useful production transfer still needs a source/distribution-specific reduction that preserves local public evaluation.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhProjectionCollisions

open PqxdhJointKdf PqxdhJointKdfGame

/-! ## Exact stream coordinates -/

/-- One exact 32-byte projection value. -/
abbrev Projection32Value := List.Vector UInt8 32

/-- One exact 12-byte nonce projection value. -/
abbrev Projection12Value := List.Vector UInt8 12

/-- The two independently random 32-byte positions in a complete joint stream. -/
inductive Projection32Slot where
  | first
  | second
deriving DecidableEq

/-- Canonical identity of one 32-byte observation: exact stream address plus exact position. -/
structure Coord32 where
  address : JointKdfAddress
  slot : Projection32Slot
deriving DecidableEq

/-- Canonical identity of one nonce observation; `final12` is its only position. -/
abbrev Coord12 := JointKdfAddress

/-- First-position identity at an exact address. -/
def firstCoord (address : JointKdfAddress) : Coord32 :=
  ⟨address, .first⟩

/-- Second-position identity at an exact address. -/
def secondCoord (address : JointKdfAddress) : Coord32 :=
  ⟨address, .second⟩

/-- Read the exact 32-byte coordinate selected by one canonical identity. -/
def Coord32.project (coord : Coord32) (stream : JointKdfStream) : Projection32Value :=
  match coord.slot with
  | .first => JointKdfProjection.first32.project stream
  | .second => JointKdfProjection.second32.project stream

/-- Read the exact 12-byte coordinate selected by one canonical nonce identity. -/
def Coord12.project (_coord : Coord12) (stream : JointKdfStream) : Projection12Value :=
  JointKdfProjection.final12.project stream

@[simp] theorem firstCoord_project (address : JointKdfAddress) (stream : JointKdfStream) :
    (firstCoord address).project stream = JointKdfProjection.first32.project stream := by
  rfl

@[simp] theorem secondCoord_project (address : JointKdfAddress) (stream : JointKdfStream) :
    (secondCoord address).project stream = JointKdfProjection.second32.project stream := by
  rfl

/-- The two positions at one address are distinct canonical identities. -/
theorem firstCoord_ne_secondCoord (address : JointKdfAddress) :
    firstCoord address ≠ secondCoord address := by
  intro equality
  have := congrArg Coord32.slot equality
  cases this

/-- A 76-byte stream is exactly a pair of 32-byte coordinates and one 12-byte coordinate. -/
def jointKdfStreamProjectionEquiv :
    JointKdfStream ≃ (Projection32Value × Projection32Value × Projection12Value) where
  toFun stream :=
    (List.Vector.take 32 stream,
      List.Vector.take 32 (List.Vector.drop 32 stream),
      List.Vector.drop 64 stream)
  invFun parts := parts.1 ++ parts.2.1 ++ parts.2.2
  left_inv stream := by
    apply List.Vector.toList_injective
    change List.take 32 stream.toList ++
        List.take 32 (List.drop 32 stream.toList) ++ List.drop 64 stream.toList =
      stream.toList
    have hprefix :
        List.take 64 stream.toList =
          List.take 32 stream.toList ++ List.take 32 (List.drop 32 stream.toList) := by
      simpa only [Nat.reduceAdd] using
        (List.take_add (l := stream.toList) (i := 32) (j := 32))
    rw [← hprefix]
    exact List.take_append_drop 64 stream.toList
  right_inv parts := by
    rcases parts with ⟨first, second, nonce⟩
    apply Prod.ext
    · apply List.Vector.toList_injective
      change List.take 32 (first.toList ++ second.toList ++ nonce.toList) = first.toList
      simp
    · apply Prod.ext
      · apply List.Vector.toList_injective
        change List.take 32 (List.drop 32
          (first.toList ++ second.toList ++ nonce.toList)) = second.toList
        simp
      · apply List.Vector.toList_injective
        change List.drop 64 (first.toList ++ second.toList ++ nonce.toList) = nonce.toList
        rw [show 64 = 32 + 32 by norm_num, ← List.drop_drop]
        simp

/-- The split equivalence exposes exactly the existing first projection. -/
@[simp] theorem jointKdfStreamProjectionEquiv_first (stream : JointKdfStream) :
    (jointKdfStreamProjectionEquiv stream).1 =
      JointKdfProjection.first32.project stream := by
  rfl

/-- The split equivalence exposes exactly the existing second projection. -/
@[simp] theorem jointKdfStreamProjectionEquiv_second (stream : JointKdfStream) :
    (jointKdfStreamProjectionEquiv stream).2.1 =
      JointKdfProjection.second32.project stream := by
  rfl

/-- The split equivalence exposes exactly the existing nonce projection. -/
@[simp] theorem jointKdfStreamProjectionEquiv_nonce (stream : JointKdfStream) :
    (jointKdfStreamProjectionEquiv stream).2.2 =
      JointKdfProjection.final12.project stream := by
  rfl

@[simp] theorem jointKdfStreamProjectionEquiv_symm_first
    (parts : Projection32Value × Projection32Value × Projection12Value) :
    (show Projection32Value from JointKdfProjection.first32.project
        (jointKdfStreamProjectionEquiv.symm parts)) = parts.1 := by
  have h := congrArg Prod.fst
    (jointKdfStreamProjectionEquiv.apply_symm_apply parts)
  exact (jointKdfStreamProjectionEquiv_first _).symm.trans h

@[simp] theorem jointKdfStreamProjectionEquiv_symm_second
    (parts : Projection32Value × Projection32Value × Projection12Value) :
    (show Projection32Value from JointKdfProjection.second32.project
        (jointKdfStreamProjectionEquiv.symm parts)) = parts.2.1 := by
  have h := congrArg (fun value => value.2.1)
    (jointKdfStreamProjectionEquiv.apply_symm_apply parts)
  exact (jointKdfStreamProjectionEquiv_second _).symm.trans h

@[simp] theorem jointKdfStreamProjectionEquiv_symm_nonce
    (parts : Projection32Value × Projection32Value × Projection12Value) :
    (show Projection12Value from JointKdfProjection.final12.project
        (jointKdfStreamProjectionEquiv.symm parts)) = parts.2.2 := by
  have h := congrArg (fun value => value.2.2)
    (jointKdfStreamProjectionEquiv.apply_symm_apply parts)
  exact (jointKdfStreamProjectionEquiv_nonce _).symm.trans h

/-- A uniform complete stream is exactly a uniform triple of its independent coordinates. -/
theorem evalDist_split_uniformJointKdfStream :
    evalDist (jointKdfStreamProjectionEquiv <$> ($ᵗ JointKdfStream)) =
      evalDist ($ᵗ (Projection32Value × Projection32Value × Projection12Value)) := by
  exact evalDist_ext fun parts =>
    probOutput_map_bijective_uniform_cross
      (α := JointKdfStream)
      (β := Projection32Value × Projection32Value × Projection12Value)
      jointKdfStreamProjectionEquiv
      jointKdfStreamProjectionEquiv.bijective parts

/-- The library product sampler is exactly sequential independent sampling, stated generically
so concrete fixed-vector sampler instances remain opaque to the elaborator. -/
theorem uniformSample_prod_prod_eq {A B C : Type}
    [SampleableType A] [SampleableType B] [SampleableType C] :
    (do
      let a ← $ᵗ A
      let b ← $ᵗ B
      let c ← $ᵗ C
      pure (a, b, c)) = $ᵗ (A × B × C) := by
  change (do
      let a ← $ᵗ A
      let b ← $ᵗ B
      let c ← $ᵗ C
      pure (a, b, c)) =
    (Prod.mk <$> ($ᵗ A) <*> (Prod.mk <$> ($ᵗ B) <*> ($ᵗ C)))
  simp [monad_norm]

/-- A deterministic function of three sequential independent samples factors through their
sampled product without changing the computation. -/
theorem map_uniformSample_prod_prod_eq {A B C gamma : Type}
    [SampleableType A] [SampleableType B] [SampleableType C]
    (f : A × B × C → gamma) :
    (do
      let a ← $ᵗ A
      let b ← $ᵗ B
      let c ← $ᵗ C
      pure (f (a, b, c))) = f <$> (do
        let a ← $ᵗ A
        let b ← $ᵗ B
        let c ← $ᵗ C
        pure (a, b, c)) := by
  simp [monad_norm]

/-! ## Infinite-domain deferred-prefetch law -/

/-- Cache updates at two distinct inputs of one possibly dependent-range oracle commute exactly. -/
theorem dependentQueryCache_cacheQuery_comm
    {iota : Type} {spec : OracleSpec.{0, 0} iota} [DecidableEq iota]
    (cache : spec.QueryCache) (left right : spec.Domain)
    (leftValue : spec.Range left) (rightValue : spec.Range right)
    (hne : left ≠ right) :
    (cache.cacheQuery left leftValue).cacheQuery right rightValue =
      (cache.cacheQuery right rightValue).cacheQuery left leftValue := by
  unfold QueryCache.cacheQuery
  exact Function.update_comm hne _ _ _

open Classical in
/-- A fresh lazy-oracle coordinate may equivalently be sampled and cached before an arbitrary
future computation. The statement is output-law only: the final cache is discarded. -/
theorem evalDist_randomOracle_eq_uniform_prefill
    {iota alpha : Type} {spec : OracleSpec.{0, 0} iota} [DecidableEq iota]
    [(query : spec.Domain) → SampleableType (spec.Range query)]
    (target : spec.Domain) (computation : OracleComp spec alpha)
    (cache : spec.QueryCache) (hcache : cache target = none) :
    evalDist ((simulateQ randomOracle computation).run' cache) =
      evalDist (($ᵗ spec.Range target) >>= fun value =>
        (simulateQ randomOracle computation).run'
          (cache.cacheQuery target value)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure output =>
      apply evalDist_ext
      intro candidate
      simp
  | query_bind query rest ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run'_eq, StateT.run_bind, map_bind]
      cases hquery : cache query with
      | some response =>
          have hne : query ≠ target := by
            intro heq
            subst query
            rw [hcache] at hquery
            contradiction
          have hstep : (id <$> randomOracle query).run cache =
              pure (response, cache) := by
            rw [StateT.run_map,
              QueryImpl.withCaching_run_some uniformSampleImpl hquery]
            rfl
          have hstepPrefill (value : spec.Range target) :
              (id <$> randomOracle query).run (cache.cacheQuery target value) =
                pure (response, cache.cacheQuery target value) := by
            have hcached : (cache.cacheQuery target value) query = some response := by
              rw [QueryCache.cacheQuery_of_ne cache value hne]
              exact hquery
            rw [StateT.run_map,
              QueryImpl.withCaching_run_some uniformSampleImpl hcached]
            rfl
          rw [hstep]
          simp only [pure_bind]
          simp_rw [hstepPrefill]
          simp only [pure_bind]
          exact ih response cache hcache
      | none =>
          by_cases heq : query = target
          · subst query
            have hstep : (id <$> randomOracle target).run cache =
                (fun value : spec.Range target =>
                  (value, cache.cacheQuery target value)) <$>
                    ($ᵗ spec.Range target) := by
              rw [StateT.run_map,
                QueryImpl.withCaching_run_none uniformSampleImpl hcache]
              simp [uniformSampleImpl, Functor.map_map]
            have hstepPrefill (value : spec.Range target) :
                (id <$> randomOracle target).run
                    (cache.cacheQuery target value) =
                  pure (value, cache.cacheQuery target value) := by
              rw [StateT.run_map,
                QueryImpl.withCaching_run_some uniformSampleImpl
                  (QueryCache.cacheQuery_self cache target value)]
              rfl
            rw [hstep]
            simp_rw [hstepPrefill]
            simp
          · have hstep : (id <$> randomOracle query).run cache =
                (fun value : spec.Range query =>
                  (value, cache.cacheQuery query value)) <$>
                    ($ᵗ spec.Range query) := by
              rw [StateT.run_map,
                QueryImpl.withCaching_run_none uniformSampleImpl hquery]
              simp [uniformSampleImpl, Functor.map_map]
            have hstepPrefill (targetValue : spec.Range target) :
                (id <$> randomOracle query).run
                    (cache.cacheQuery target targetValue) =
                  (fun value : spec.Range query =>
                    (value, (cache.cacheQuery target targetValue).cacheQuery
                      query value)) <$> ($ᵗ spec.Range query) := by
              have hnone : (cache.cacheQuery target targetValue) query = none := by
                rw [QueryCache.cacheQuery_of_ne cache targetValue heq]
                exact hquery
              rw [StateT.run_map,
                QueryImpl.withCaching_run_none uniformSampleImpl hnone]
              simp [uniformSampleImpl, Functor.map_map]
            rw [hstep]
            simp_rw [hstepPrefill]
            rw [bind_map_left]
            simp_rw [bind_map_left]
            change evalDist (do
                let response ← $ᵗ spec.Range query
                (simulateQ randomOracle (rest response)).run'
                  (cache.cacheQuery query response)) =
              evalDist (do
                let targetValue ← $ᵗ spec.Range target
                let response ← $ᵗ spec.Range query
                (simulateQ randomOracle (rest response)).run'
                  ((cache.cacheQuery target targetValue).cacheQuery query response))
            calc
              evalDist (do
                  let response ← $ᵗ spec.Range query
                  (simulateQ randomOracle (rest response)).run'
                    (cache.cacheQuery query response)) =
                evalDist (do
                  let response ← $ᵗ spec.Range query
                  let targetValue ← $ᵗ spec.Range target
                  (simulateQ randomOracle (rest response)).run'
                    ((cache.cacheQuery query response).cacheQuery
                      target targetValue)) := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro response
                apply ih response
                rw [QueryCache.cacheQuery_of_ne cache response (Ne.symm heq)]
                exact hcache
              _ = evalDist (do
                  let targetValue ← $ᵗ spec.Range target
                  let response ← $ᵗ spec.Range query
                  (simulateQ randomOracle (rest response)).run'
                    ((cache.cacheQuery query response).cacheQuery
                      target targetValue)) :=
                OracleComp.DeferredSampling.evalDist_bind_comm
                  ($ᵗ spec.Range query) ($ᵗ spec.Range target)
                    fun response targetValue =>
                    (simulateQ randomOracle (rest response)).run'
                      ((cache.cacheQuery query response).cacheQuery
                        target targetValue)
              _ = evalDist (do
                  let targetValue ← $ᵗ spec.Range target
                  let response ← $ᵗ spec.Range query
                  (simulateQ randomOracle (rest response)).run'
                    ((cache.cacheQuery target targetValue).cacheQuery
                      query response)) := by
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro targetValue
                apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                intro response
                rw [dependentQueryCache_cacheQuery_comm cache query target
                  response targetValue heq]

open Classical in
/-- Querying and ignoring one lazy-oracle coordinate is distributionally inert,
even when the computation later reveals that same coordinate adaptively. -/
theorem evalDist_randomOracle_prefetch_irrelevant
    {iota alpha : Type} {spec : OracleSpec.{0, 0} iota} [DecidableEq iota]
    [(query : spec.Domain) → SampleableType (spec.Range query)]
    (target : spec.Domain) (computation : OracleComp spec alpha)
    (cache : spec.QueryCache) :
    evalDist ((randomOracle (spec := spec) target >>= fun _ =>
          simulateQ randomOracle computation).run' cache) =
      evalDist ((simulateQ randomOracle computation).run' cache) := by
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  cases hcache : cache target with
  | some value =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache]
      simp
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache]
      rw [bind_map_left]
      change evalDist (do
          let value ← $ᵗ spec.Range target
          (simulateQ randomOracle computation).run'
            (cache.cacheQuery target value)) =
        evalDist ((simulateQ randomOracle computation).run' cache)
      exact (evalDist_randomOracle_eq_uniform_prefill
        target computation cache hcache).symm

/-! ## Canonical observations and bad events -/

/-- One visible 32-byte observation, retaining identity separately from value. -/
structure Observation32 where
  coord : Coord32
  value : Projection32Value

/-- One visible nonce observation, retaining identity separately from value. -/
structure Observation12 where
  coord : Coord12
  value : Projection12Value

/-- Accidental 32-byte collision among two distinct canonical visible identities. -/
def Bad32 (observations : List Observation32) : Prop :=
  ∃ left ∈ observations, ∃ right ∈ observations,
    left.coord ≠ right.coord ∧ left.value = right.value

/-- Accidental nonce collision among two distinct canonical visible identities. -/
def Bad12 (observations : List Observation12) : Prop :=
  ∃ left ∈ observations, ∃ right ∈ observations,
    left.coord ≠ right.coord ∧ left.value = right.value

/-- Repeating exactly one 32-byte coordinate is intentional equality and cannot witness bad. -/
theorem not_bad32_single_coord (coord : Coord32) (values : List Projection32Value)
    (observations : List Observation32)
    (hcoords : observations = values.map fun value => ⟨coord, value⟩) :
    ¬ Bad32 observations := by
  subst observations
  rintro ⟨left, hleft, right, hright, hne, _⟩
  simp only [List.mem_map] at hleft hright
  obtain ⟨_, _, rfl⟩ := hleft
  obtain ⟨_, _, rfl⟩ := hright
  exact hne rfl

/-- Repeating exactly one nonce coordinate is intentional equality and cannot witness bad. -/
theorem not_bad12_single_coord (coord : Coord12) (values : List Projection12Value)
    (observations : List Observation12)
    (hcoords : observations = values.map fun value => ⟨coord, value⟩) :
    ¬ Bad12 observations := by
  subst observations
  rintro ⟨left, hleft, right, hright, hne, _⟩
  simp only [List.mem_map] at hleft hright
  obtain ⟨_, _, rfl⟩ := hleft
  obtain ⟨_, _, rfl⟩ := hright
  exact hne rfl

/-! ## Source-shaped call surface -/

/-- Exact source calls whose output projections are relevant to constructor injectivity. -/
inductive SourceKdfQuery where
  | root (input : Pqxdh.Bytes)
  | initial (input : Pqxdh.Bytes)
  | step (input : Pqxdh.Bytes)
  | project (query : JointKdfViewQuery)
deriving DecidableEq

/-- Exact result type of each source-shaped call. -/
def SourceKdfSpec : OracleSpec SourceKdfQuery
  | .root _ => Projection32Value
  | .initial _ => Projection32Value × Projection32Value
  | .step _ => Projection32Value × Projection32Value × Projection12Value
  | .project query => JointKdfViewSpec.Range query

/-- The canonical stream address used by one source call. -/
def SourceKdfQuery.address : SourceKdfQuery → JointKdfAddress
  | .root input => FixedHkdfDomain.pqxdh.address input
  | .initial input => FixedHkdfDomain.ratchet.address input
  | .step input => FixedHkdfDomain.ratchet.address input
  | .project query => query.address

/-- Return the exact source result by projecting one complete stream. -/
def SourceKdfQuery.output (query : SourceKdfQuery) (stream : JointKdfStream) :
    SourceKdfSpec.Range query :=
  match query with
  | .root _ => JointKdfProjection.first32.project stream
  | .initial _ =>
      (JointKdfProjection.first32.project stream,
        JointKdfProjection.second32.project stream)
  | .step _ =>
      (JointKdfProjection.first32.project stream,
        JointKdfProjection.second32.project stream,
        JointKdfProjection.final12.project stream)
  | .project query => query.project stream

/-- Visible 32-byte observations made by one source call. -/
def SourceKdfQuery.observations32 (query : SourceKdfQuery) (stream : JointKdfStream) :
    List Observation32 :=
  match query with
  | .root _ =>
      [⟨firstCoord query.address, JointKdfProjection.first32.project stream⟩]
  | .initial _ | .step _ =>
      [⟨firstCoord query.address, JointKdfProjection.first32.project stream⟩,
        ⟨secondCoord query.address, JointKdfProjection.second32.project stream⟩]
  | .project view =>
      match view.projection with
      | .first32 =>
          [⟨firstCoord query.address, JointKdfProjection.first32.project stream⟩]
      | .second32 =>
          [⟨secondCoord query.address, JointKdfProjection.second32.project stream⟩]
      | .final12 => []

/-- Visible nonce observations made by one source call. -/
def SourceKdfQuery.observations12 (query : SourceKdfQuery) (stream : JointKdfStream) :
    List Observation12 :=
  match query with
  | .step _ =>
      [⟨query.address, JointKdfProjection.final12.project stream⟩]
  | .project view =>
      match view.projection with
      | .final12 => [⟨query.address, JointKdfProjection.final12.project stream⟩]
      | .first32 | .second32 => []
  | .root _ | .initial _ => []

/-- The exact source-visible projection trace, excluding every latent coordinate of a cached
complete stream. -/
structure SourceProjectionLog where
  observations32 : List Observation32
  observations12 : List Observation12

/-- Empty source-visible trace. -/
def emptySourceProjectionLog : SourceProjectionLog :=
  ⟨[], []⟩

/-- Record exactly the coordinates returned by one source call, in the same reverse-chronological
order as the coordinate-level logging cache. -/
def SourceProjectionLog.record (log : SourceProjectionLog)
    (query : SourceKdfQuery) (stream : JointKdfStream) : SourceProjectionLog where
  observations32 := (query.observations32 stream).reverse ++ log.observations32
  observations12 := (query.observations12 stream).reverse ++ log.observations12

/-- Record the same visible trace directly from the typed result of a source call. -/
def SourceProjectionLog.recordOutput (log : SourceProjectionLog)
    (query : SourceKdfQuery) (output : SourceKdfSpec.Range query) : SourceProjectionLog :=
  match query with
  | .root input =>
      ⟨⟨firstCoord (FixedHkdfDomain.pqxdh.address input), output⟩ :: log.observations32,
        log.observations12⟩
  | .initial input =>
      ⟨⟨secondCoord (FixedHkdfDomain.ratchet.address input), output.2⟩ ::
          ⟨firstCoord (FixedHkdfDomain.ratchet.address input), output.1⟩ ::
            log.observations32,
        log.observations12⟩
  | .step input =>
      ⟨⟨secondCoord (FixedHkdfDomain.ratchet.address input), output.2.1⟩ ::
          ⟨firstCoord (FixedHkdfDomain.ratchet.address input), output.1⟩ ::
            log.observations32,
        ⟨FixedHkdfDomain.ratchet.address input, output.2.2⟩ :: log.observations12⟩
  | .project ⟨input, domain, .first32⟩ =>
      ⟨⟨firstCoord (domain.address input), output⟩ :: log.observations32,
        log.observations12⟩
  | .project ⟨input, domain, .second32⟩ =>
      ⟨⟨secondCoord (domain.address input), output⟩ :: log.observations32,
        log.observations12⟩
  | .project ⟨input, domain, .final12⟩ =>
      ⟨log.observations32,
        ⟨domain.address input, output⟩ :: log.observations12⟩

/-- Recording from a complete stream or from the source-typed result is exactly the same. -/
@[simp] theorem SourceProjectionLog.recordOutput_output
    (log : SourceProjectionLog) (query : SourceKdfQuery) (stream : JointKdfStream) :
    log.recordOutput query (query.output stream) = log.record query stream := by
  rcases query with input | input | input | ⟨input, domain, projection⟩
  · rfl
  · rfl
  · rfl
  · cases projection <;> rfl

/-- Collision event over exactly the values returned through the source-shaped interface. -/
def SourceProjectionLog.HasCollision (log : SourceProjectionLog) : Prop :=
  Bad32 log.observations32 ∨ Bad12 log.observations12

/-- Initial-left and step-key calls at equal input have the same canonical first identity. -/
theorem initial_firstCoord_eq_step_firstCoord (input : Pqxdh.Bytes) :
    firstCoord (SourceKdfQuery.initial input).address =
      firstCoord (SourceKdfQuery.step input).address := by
  rfl

/-- Initial-right and step-next calls at equal input have the same canonical second identity. -/
theorem initial_secondCoord_eq_step_secondCoord (input : Pqxdh.Bytes) :
    secondCoord (SourceKdfQuery.initial input).address =
      secondCoord (SourceKdfQuery.step input).address := by
  rfl

/-- The root and ratchet first projections remain distinct identities at all inputs. -/
theorem root_firstCoord_ne_ratchet_firstCoord (rootInput ratchetInput : Pqxdh.Bytes) :
    firstCoord (SourceKdfQuery.root rootInput).address ≠
      firstCoord (SourceKdfQuery.step ratchetInput).address := by
  intro equality
  have addressEquality := congrArg Coord32.address equality
  exact rootAddress_ne_ratchetAddress rootInput ratchetInput addressEquality

/-! ## One-stream forwarding and exact source-call accounting -/

/-- Public source-call interface: adversary randomness plus the four source-shaped KDF calls. -/
abbrev SourceKdfAdversarySpec := unifSpec + SourceKdfSpec

/-- Forward each complete source call through exactly one complete-stream query. -/
def sourceKdfForwardImpl :
    QueryImpl SourceKdfAdversarySpec
      (OracleComp FixedHkdfSha512JointStreamSpec) :=
  fun query =>
    match query with
    | .inl randomQuery =>
        liftM (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery))
    | .inr sourceQuery => do
        let stream ←
          liftM (FixedHkdfSha512JointStreamSpec.query (.inr sourceQuery.address))
        pure (sourceQuery.output stream)

@[simp] theorem sourceKdfForwardImpl_uniform (query : unifSpec.Domain) :
    sourceKdfForwardImpl (.inl query) =
      liftM (FixedHkdfSha512JointStreamSpec.query (.inl query)) := by
  rfl

@[simp] theorem sourceKdfForwardImpl_source (query : SourceKdfQuery) :
    sourceKdfForwardImpl (.inr query) = (do
      let stream ←
        liftM (FixedHkdfSha512JointStreamSpec.query (.inr query.address))
      pure (query.output stream)) := by
  rfl

/-- The six disjoint logical source-call classes used for exact projection accounting. -/
inductive SourceKdfCallClass where
  | root
  | initial
  | step
  | publicFirst
  | publicSecond
  | publicNonce
deriving DecidableEq

/-- Classify one exact source call by source wrapper and public projection. -/
def SourceKdfQuery.callClass : SourceKdfQuery → SourceKdfCallClass
  | .root _ => .root
  | .initial _ => .initial
  | .step _ => .step
  | .project view =>
      match view.projection with
      | .first32 => .publicFirst
      | .second32 => .publicSecond
      | .final12 => .publicNonce

/-- Select adversary-controlled uniform queries. -/
def IsSourceKdfUniformQuery : SourceKdfAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsSourceKdfUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Select one of the six exact source-call classes. -/
def IsSourceKdfClassQuery (kind : SourceKdfCallClass) :
    SourceKdfAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr query => query.callClass = kind

instance (kind : SourceKdfCallClass) : DecidablePred (IsSourceKdfClassQuery kind)
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable (query.callClass = kind))

/-- Select every source KDF call and no adversary-uniform call. -/
def IsSourceKdfCallQuery : SourceKdfAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsSourceKdfCallQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- The exact logical number of first-coordinate observations. -/
def sourceQF (r i s pF : ℕ) : ℕ :=
  r + i + s + pF

/-- The exact logical number of second-coordinate observations. -/
def sourceQS (i s pS : ℕ) : ℕ :=
  i + s + pS

/-- The exact logical number of nonce-coordinate observations. -/
def sourceQN (s pN : ℕ) : ℕ :=
  s + pN

/-- The conservative complete-stream query count: one query per source call. -/
def sourceQStream (r i s pF pS pN : ℕ) : ℕ :=
  r + i + s + pF + pS + pN

/-- The exact number of visible 32-byte observations. -/
def sourceQ32 (r i s pF pS : ℕ) : ℕ :=
  sourceQF r i s pF + sourceQS i s pS

@[simp] theorem sourceQ32_eq (r i s pF pS : ℕ) :
    sourceQ32 r i s pF pS = r + i + s + pF + (i + s + pS) := by
  rfl

/-- A bounded source computation with independent caps for every actual call class. -/
structure SourceKdfAdversary (qU r i s pF pS pN : ℕ) where
  main : OracleComp SourceKdfAdversarySpec Bool
  uniformQueryBound : main.IsQueryBoundP IsSourceKdfUniformQuery qU
  rootQueryBound : main.IsQueryBoundP (IsSourceKdfClassQuery .root) r
  initialQueryBound : main.IsQueryBoundP (IsSourceKdfClassQuery .initial) i
  stepQueryBound : main.IsQueryBoundP (IsSourceKdfClassQuery .step) s
  publicFirstQueryBound : main.IsQueryBoundP (IsSourceKdfClassQuery .publicFirst) pF
  publicSecondQueryBound : main.IsQueryBoundP (IsSourceKdfClassQuery .publicSecond) pS
  publicNonceQueryBound : main.IsQueryBoundP (IsSourceKdfClassQuery .publicNonce) pN

/-- Query bounds for two predicates add to a bound for their disjunction. -/
theorem isQueryBoundP_or {ι : Type} {spec : OracleSpec.{0, 0} ι} {alpha : Type}
    {computation : OracleComp spec alpha} {left right : spec.Domain → Prop}
    [DecidablePred left] [DecidablePred right] {qLeft qRight : ℕ}
    (hleft : computation.IsQueryBoundP left qLeft)
    (hright : computation.IsQueryBoundP right qRight) :
    computation.IsQueryBoundP (fun query => left query ∨ right query)
      (qLeft + qRight) := by
  induction computation using OracleComp.inductionOn generalizing qLeft qRight with
  | pure output => trivial
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hleft hright ⊢
      constructor
      · by_cases hl : left query
        · exact Or.inr (by
            have := hleft.1
            simp only [hl, not_true, false_or] at this
            omega)
        · by_cases hr : right query
          · exact Or.inr (by
              have := hright.1
              simp only [hr, not_true, false_or] at this
              omega)
          · exact Or.inl (by simp [hl, hr])
      · intro response
        have hposLeft : left query → 0 < qLeft := by
          intro hl
          exact hleft.1.resolve_left (by simpa using hl)
        have hposRight : right query → 0 < qRight := by
          intro hr
          exact hright.1.resolve_left (by simpa using hr)
        have hrec := ih response (hleft.2 response) (hright.2 response)
        exact hrec.mono (by
          by_cases hl : left query
          · by_cases hr : right query
            · simp only [hl, hr, true_or, if_true] at hrec ⊢
              have := hposLeft hl
              have := hposRight hr
              omega
            · simp only [hl, true_or, if_true, hr, if_false] at hrec ⊢
              have := hposLeft hl
              omega
          · by_cases hr : right query
            · simp only [hl, false_or, hr, if_true, if_false] at hrec ⊢
              have := hposRight hr
              omega
            · simp only [hl, hr, false_or, if_false] at hrec ⊢
              exact le_rfl)

/-- Every source call belongs to exactly one of the six source classes. -/
theorem isSourceKdfCallQuery_iff_classes (query : SourceKdfAdversarySpec.Domain) :
    IsSourceKdfCallQuery query ↔
      IsSourceKdfClassQuery .root query ∨
      IsSourceKdfClassQuery .initial query ∨
      IsSourceKdfClassQuery .step query ∨
      IsSourceKdfClassQuery .publicFirst query ∨
      IsSourceKdfClassQuery .publicSecond query ∨
      IsSourceKdfClassQuery .publicNonce query := by
  rcases query with randomQuery | sourceQuery
  · simp [IsSourceKdfCallQuery, IsSourceKdfClassQuery]
  · rcases sourceQuery with input | input | input | view
    · simp [IsSourceKdfCallQuery, IsSourceKdfClassQuery, SourceKdfQuery.callClass]
    · simp [IsSourceKdfCallQuery, IsSourceKdfClassQuery, SourceKdfQuery.callClass]
    · simp [IsSourceKdfCallQuery, IsSourceKdfClassQuery, SourceKdfQuery.callClass]
    · rcases view with ⟨input, domain, projection⟩
      cases projection <;>
        simp [IsSourceKdfCallQuery, IsSourceKdfClassQuery,
          SourceKdfQuery.callClass]

/-- The six source-class bounds derive the exact complete-stream call bound. -/
theorem SourceKdfAdversary.sourceCallQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    adversary.main.IsQueryBoundP IsSourceKdfCallQuery
      (sourceQStream r i s pF pS pN) := by
  have hclasses := isQueryBoundP_or adversary.rootQueryBound
    (isQueryBoundP_or adversary.initialQueryBound
      (isQueryBoundP_or adversary.stepQueryBound
        (isQueryBoundP_or adversary.publicFirstQueryBound
          (isQueryBoundP_or adversary.publicSecondQueryBound
            adversary.publicNonceQueryBound))))
  have hconverted : adversary.main.IsQueryBoundP IsSourceKdfCallQuery
      (r + (i + (s + (pF + (pS + pN))))) :=
    (OracleComp.isQueryBoundP_congr_pred
      (oa := adversary.main)
      (p := fun query =>
        IsSourceKdfClassQuery .root query ∨
        IsSourceKdfClassQuery .initial query ∨
        IsSourceKdfClassQuery .step query ∨
        IsSourceKdfClassQuery .publicFirst query ∨
        IsSourceKdfClassQuery .publicSecond query ∨
        IsSourceKdfClassQuery .publicNonce query)
      (p' := IsSourceKdfCallQuery)
      (fun query => (isSourceKdfCallQuery_iff_classes query).symm)).mp hclasses
  exact hconverted.mono (by unfold sourceQStream; omega)

/-! ## Visible trace through the complete-stream challenge -/

/-- Forward source calls to the complete-stream challenge while retaining only source-visible
projection observations as auxiliary state. -/
def sourceKdfStreamObservationForwardImpl :
    QueryImpl SourceKdfAdversarySpec
      (StateT SourceProjectionLog
        (OracleComp FixedHkdfSha512JointStreamSpec))
  | .inl randomQuery => StateT.mk fun log =>
      (fun value => (value, log)) <$>
        liftM (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery))
  | .inr sourceQuery => StateT.mk fun log => do
      let stream ←
        liftM (FixedHkdfSha512JointStreamSpec.query (.inr sourceQuery.address))
      pure (sourceQuery.output stream, log.record sourceQuery stream)

/-- Forwarded complete-stream computation returning the adversary output together with the exact
source-visible projection trace. -/
def sourceKdfStreamObservedMain {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    OracleComp FixedHkdfSha512JointStreamSpec
      (Bool × SourceProjectionLog) :=
  (simulateQ sourceKdfStreamObservationForwardImpl adversary.main).run
    emptySourceProjectionLog

/-- Lazy complete-stream random experiment whose output retains every and only visible projection
observation. -/
noncomputable def sourceProjectionObservedFullRandomRun
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    ProbComp (Bool × SourceProjectionLog) :=
  (simulateQ fixedHkdfSha512JointStreamRandomImpl
    (sourceKdfStreamObservedMain adversary)).run' ∅

/-! ## Deferred coordinate view -/

/-- Random oracle for exact 32-byte coordinate identities. -/
abbrev Projection32RO := Coord32 →ₒ Projection32Value

/-- Random oracle for exact nonce-coordinate identities. -/
abbrev Projection12RO := Coord12 →ₒ Projection12Value

noncomputable instance projection32ROIsUniformSpec : IsUniformSpec Projection32RO :=
  OracleSpec.IsUniformSpec.ofFintypeInhabited _

noncomputable instance projection12ROIsUniformSpec : IsUniformSpec Projection12RO :=
  OracleSpec.IsUniformSpec.ofFintypeInhabited _

/-- The two mixed-width coordinate oracles, kept as constant-range suboracles. -/
abbrev ProjectionCoordSpec := Projection32RO + Projection12RO

/-- Primitive normalized-random interface: uncached adversary randomness plus cached coordinates. -/
abbrev ProjectionCoordChallengeSpec := unifSpec + ProjectionCoordSpec

/-- Query one first coordinate in the normalized random interface. -/
def queryFirstCoord (address : JointKdfAddress) :
    OracleComp ProjectionCoordChallengeSpec Projection32Value :=
  liftM (ProjectionCoordChallengeSpec.query (.inr (.inl (firstCoord address))))

/-- Query one second coordinate in the normalized random interface. -/
def querySecondCoord (address : JointKdfAddress) :
    OracleComp ProjectionCoordChallengeSpec Projection32Value :=
  liftM (ProjectionCoordChallengeSpec.query (.inr (.inl (secondCoord address))))

/-- Query one nonce coordinate in the normalized random interface. -/
def queryNonceCoord (address : JointKdfAddress) :
    OracleComp ProjectionCoordChallengeSpec Projection12Value :=
  liftM (ProjectionCoordChallengeSpec.query (.inr (.inr address)))

/-- Query the two source-visible initial coordinates in source order. -/
def queryInitialCoords (address : JointKdfAddress) :
    OracleComp ProjectionCoordChallengeSpec (Projection32Value × Projection32Value) := do
  let first ← queryFirstCoord address
  let second ← querySecondCoord address
  pure (first, second)

/-- Query the three source-visible step coordinates in source order. -/
def queryStepCoords (address : JointKdfAddress) :
    OracleComp ProjectionCoordChallengeSpec
      (Projection32Value × Projection32Value × Projection12Value) := do
  let first ← queryFirstCoord address
  let second ← querySecondCoord address
  let nonce ← queryNonceCoord address
  pure (first, second, nonce)

/-- Deferred-coordinate implementation of the exact source-shaped surface.

Only coordinates returned by the source call are queried. A root call exposes `F`; an initial call
exposes `F,S`; a step exposes `F,S,N`; and a public projection exposes its selected coordinate.
-/
def sourceKdfCoordinateForwardImpl :
    QueryImpl SourceKdfAdversarySpec (OracleComp ProjectionCoordChallengeSpec) :=
  fun query =>
    match query with
    | .inl randomQuery =>
        liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery))
    | .inr (.root input) =>
        queryFirstCoord (FixedHkdfDomain.pqxdh.address input)
    | .inr (.initial input) =>
        queryInitialCoords (FixedHkdfDomain.ratchet.address input)
    | .inr (.step input) =>
        queryStepCoords (FixedHkdfDomain.ratchet.address input)
    | .inr (.project ⟨input, domain, .first32⟩) =>
        queryFirstCoord (domain.address input)
    | .inr (.project ⟨input, domain, .second32⟩) =>
        querySecondCoord (domain.address input)
    | .inr (.project ⟨input, domain, .final12⟩) =>
        queryNonceCoord (domain.address input)

/-- Select uncached adversary randomness on the normalized challenge interface. -/
def IsProjectionCoordUniformQuery : ProjectionCoordChallengeSpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsProjectionCoordUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Select first-position coordinate queries. -/
def IsProjectionFirstQuery : ProjectionCoordChallengeSpec.Domain → Prop
  | .inr (.inl coord) => coord.slot = .first
  | _ => False

instance : DecidablePred IsProjectionFirstQuery
  | .inr (.inl coord) => inferInstanceAs (Decidable (coord.slot = .first))
  | .inl _ | .inr (.inr _) => isFalse id

/-- Select second-position coordinate queries. -/
def IsProjectionSecondQuery : ProjectionCoordChallengeSpec.Domain → Prop
  | .inr (.inl coord) => coord.slot = .second
  | _ => False

instance : DecidablePred IsProjectionSecondQuery
  | .inr (.inl coord) => inferInstanceAs (Decidable (coord.slot = .second))
  | .inl _ | .inr (.inr _) => isFalse id

/-- Select nonce-coordinate queries. -/
def IsProjectionNonceQuery : ProjectionCoordChallengeSpec.Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred IsProjectionNonceQuery
  | .inr (.inr _) => isTrue trivial
  | .inl _ | .inr (.inl _) => isFalse id

@[simp] theorem queryFirstCoord_first_bound (address : JointKdfAddress) :
    (queryFirstCoord address).IsQueryBoundP IsProjectionFirstQuery 1 := by
  unfold queryFirstCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionFirstQuery) (.inr (.inl (firstCoord address))) 1).2 (by
      simp [IsProjectionFirstQuery, firstCoord])

@[simp] theorem queryFirstCoord_second_bound (address : JointKdfAddress) :
    (queryFirstCoord address).IsQueryBoundP IsProjectionSecondQuery 0 := by
  unfold queryFirstCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionSecondQuery) (.inr (.inl (firstCoord address))) 0).2 (by
      simp [IsProjectionSecondQuery, firstCoord])

@[simp] theorem queryFirstCoord_nonce_bound (address : JointKdfAddress) :
    (queryFirstCoord address).IsQueryBoundP IsProjectionNonceQuery 0 := by
  unfold queryFirstCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionNonceQuery) (.inr (.inl (firstCoord address))) 0).2 (by
      simp [IsProjectionNonceQuery])

@[simp] theorem querySecondCoord_first_bound (address : JointKdfAddress) :
    (querySecondCoord address).IsQueryBoundP IsProjectionFirstQuery 0 := by
  unfold querySecondCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionFirstQuery) (.inr (.inl (secondCoord address))) 0).2 (by
      simp [IsProjectionFirstQuery, secondCoord])

@[simp] theorem querySecondCoord_second_bound (address : JointKdfAddress) :
    (querySecondCoord address).IsQueryBoundP IsProjectionSecondQuery 1 := by
  unfold querySecondCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionSecondQuery) (.inr (.inl (secondCoord address))) 1).2 (by
      simp [IsProjectionSecondQuery, secondCoord])

@[simp] theorem querySecondCoord_nonce_bound (address : JointKdfAddress) :
    (querySecondCoord address).IsQueryBoundP IsProjectionNonceQuery 0 := by
  unfold querySecondCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionNonceQuery) (.inr (.inl (secondCoord address))) 0).2 (by
      simp [IsProjectionNonceQuery])

@[simp] theorem queryNonceCoord_first_bound (address : JointKdfAddress) :
    (queryNonceCoord address).IsQueryBoundP IsProjectionFirstQuery 0 := by
  unfold queryNonceCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionFirstQuery) (.inr (.inr address)) 0).2 (by
      simp [IsProjectionFirstQuery])

@[simp] theorem queryNonceCoord_second_bound (address : JointKdfAddress) :
    (queryNonceCoord address).IsQueryBoundP IsProjectionSecondQuery 0 := by
  unfold queryNonceCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionSecondQuery) (.inr (.inr address)) 0).2 (by
      simp [IsProjectionSecondQuery])

@[simp] theorem queryNonceCoord_nonce_bound (address : JointKdfAddress) :
    (queryNonceCoord address).IsQueryBoundP IsProjectionNonceQuery 1 := by
  unfold queryNonceCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionNonceQuery) (.inr (.inr address)) 1).2 (by
      simp [IsProjectionNonceQuery])

@[simp] theorem queryFirstCoord_uniform_bound (address : JointKdfAddress) :
    (queryFirstCoord address).IsQueryBoundP IsProjectionCoordUniformQuery 0 := by
  unfold queryFirstCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionCoordUniformQuery) (.inr (.inl (firstCoord address))) 0).2 (by
      simp [IsProjectionCoordUniformQuery])

@[simp] theorem querySecondCoord_uniform_bound (address : JointKdfAddress) :
    (querySecondCoord address).IsQueryBoundP IsProjectionCoordUniformQuery 0 := by
  unfold querySecondCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionCoordUniformQuery) (.inr (.inl (secondCoord address))) 0).2 (by
      simp [IsProjectionCoordUniformQuery])

@[simp] theorem queryNonceCoord_uniform_bound (address : JointKdfAddress) :
    (queryNonceCoord address).IsQueryBoundP IsProjectionCoordUniformQuery 0 := by
  unfold queryNonceCoord
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsProjectionCoordUniformQuery) (.inr (.inr address)) 0).2 (by
      simp [IsProjectionCoordUniformQuery])

@[simp] theorem queryInitialCoords_first_bound (address : JointKdfAddress) :
    (queryInitialCoords address).IsQueryBoundP IsProjectionFirstQuery 1 := by
  unfold queryInitialCoords
  simpa using OracleComp.isQueryBoundP_bind (queryFirstCoord_first_bound address)
    (fun first _ => (OracleComp.isQueryBoundP_map_iff
      (querySecondCoord address) (Prod.mk first) 0).mpr
        (querySecondCoord_first_bound address))

@[simp] theorem queryInitialCoords_second_bound (address : JointKdfAddress) :
    (queryInitialCoords address).IsQueryBoundP IsProjectionSecondQuery 1 := by
  unfold queryInitialCoords
  have h := OracleComp.isQueryBoundP_bind (queryFirstCoord_second_bound address)
    (fun first _ => (OracleComp.isQueryBoundP_map_iff
      (querySecondCoord address) (Prod.mk first) 1).mpr
        (querySecondCoord_second_bound address))
  simpa using h

@[simp] theorem queryInitialCoords_nonce_bound (address : JointKdfAddress) :
    (queryInitialCoords address).IsQueryBoundP IsProjectionNonceQuery 0 := by
  unfold queryInitialCoords
  simpa using OracleComp.isQueryBoundP_bind (queryFirstCoord_nonce_bound address)
    (fun first _ => (OracleComp.isQueryBoundP_map_iff
      (querySecondCoord address) (Prod.mk first) 0).mpr
        (querySecondCoord_nonce_bound address))

@[simp] theorem queryInitialCoords_uniform_bound (address : JointKdfAddress) :
    (queryInitialCoords address).IsQueryBoundP IsProjectionCoordUniformQuery 0 := by
  unfold queryInitialCoords
  simpa using OracleComp.isQueryBoundP_bind (queryFirstCoord_uniform_bound address)
    (fun first _ => (OracleComp.isQueryBoundP_map_iff
      (querySecondCoord address) (Prod.mk first) 0).mpr
        (querySecondCoord_uniform_bound address))

@[simp] theorem queryStepCoords_first_bound (address : JointKdfAddress) :
    (queryStepCoords address).IsQueryBoundP IsProjectionFirstQuery 1 := by
  unfold queryStepCoords
  have h := OracleComp.isQueryBoundP_bind (queryFirstCoord_first_bound address)
    (fun first _ => OracleComp.isQueryBoundP_bind (querySecondCoord_first_bound address)
      (fun second _ => (OracleComp.isQueryBoundP_map_iff
        (queryNonceCoord address) (fun nonce => (first, second, nonce)) 0).mpr
          (queryNonceCoord_first_bound address)))
  simpa using h

@[simp] theorem queryStepCoords_second_bound (address : JointKdfAddress) :
    (queryStepCoords address).IsQueryBoundP IsProjectionSecondQuery 1 := by
  unfold queryStepCoords
  have h := OracleComp.isQueryBoundP_bind (queryFirstCoord_second_bound address)
    (fun first _ => OracleComp.isQueryBoundP_bind (querySecondCoord_second_bound address)
      (fun second _ => (OracleComp.isQueryBoundP_map_iff
        (queryNonceCoord address) (fun nonce => (first, second, nonce)) 0).mpr
          (queryNonceCoord_second_bound address)))
  simpa using h

@[simp] theorem queryStepCoords_nonce_bound (address : JointKdfAddress) :
    (queryStepCoords address).IsQueryBoundP IsProjectionNonceQuery 1 := by
  unfold queryStepCoords
  have h := OracleComp.isQueryBoundP_bind (queryFirstCoord_nonce_bound address)
    (fun first _ => OracleComp.isQueryBoundP_bind (querySecondCoord_nonce_bound address)
      (fun second _ => (OracleComp.isQueryBoundP_map_iff
        (queryNonceCoord address) (fun nonce => (first, second, nonce)) 1).mpr
          (queryNonceCoord_nonce_bound address)))
  simpa using h

@[simp] theorem queryStepCoords_uniform_bound (address : JointKdfAddress) :
    (queryStepCoords address).IsQueryBoundP IsProjectionCoordUniformQuery 0 := by
  unfold queryStepCoords
  have h := OracleComp.isQueryBoundP_bind (queryFirstCoord_uniform_bound address)
    (fun first _ => OracleComp.isQueryBoundP_bind (querySecondCoord_uniform_bound address)
      (fun second _ => (OracleComp.isQueryBoundP_map_iff
        (queryNonceCoord address) (fun nonce => (first, second, nonce)) 0).mpr
          (queryNonceCoord_uniform_bound address)))
  simpa using h

/-- Source calls that expose the first 32-byte coordinate. -/
def IsSourceFirstObservation : SourceKdfAdversarySpec.Domain → Prop
  | .inr query =>
      query.callClass = .root ∨ query.callClass = .initial ∨
        query.callClass = .step ∨ query.callClass = .publicFirst
  | .inl _ => False

instance : DecidablePred IsSourceFirstObservation
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable
      (query.callClass = .root ∨ query.callClass = .initial ∨
        query.callClass = .step ∨ query.callClass = .publicFirst))

/-- Source calls that expose the second 32-byte coordinate. -/
def IsSourceSecondObservation : SourceKdfAdversarySpec.Domain → Prop
  | .inr query =>
      query.callClass = .initial ∨ query.callClass = .step ∨
        query.callClass = .publicSecond
  | .inl _ => False

instance : DecidablePred IsSourceSecondObservation
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable
      (query.callClass = .initial ∨ query.callClass = .step ∨
        query.callClass = .publicSecond))

/-- Source calls that expose the final 12-byte nonce coordinate. -/
def IsSourceNonceObservation : SourceKdfAdversarySpec.Domain → Prop
  | .inr query => query.callClass = .step ∨ query.callClass = .publicNonce
  | .inl _ => False

instance : DecidablePred IsSourceNonceObservation
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable
      (query.callClass = .step ∨ query.callClass = .publicNonce))

/-- The source-class caps derive the exact first-coordinate request cap. -/
theorem SourceKdfAdversary.firstObservationQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    adversary.main.IsQueryBoundP IsSourceFirstObservation (sourceQF r i s pF) := by
  have h := isQueryBoundP_or adversary.rootQueryBound
    (isQueryBoundP_or adversary.initialQueryBound
      (isQueryBoundP_or adversary.stepQueryBound adversary.publicFirstQueryBound))
  exact ((OracleComp.isQueryBoundP_congr_pred
    (oa := adversary.main)
    (p := fun query =>
      IsSourceKdfClassQuery .root query ∨
      IsSourceKdfClassQuery .initial query ∨
      IsSourceKdfClassQuery .step query ∨
      IsSourceKdfClassQuery .publicFirst query)
    (p' := IsSourceFirstObservation)
    (fun query => by
      rcases query with randomQuery | sourceQuery
      · simp [IsSourceKdfClassQuery, IsSourceFirstObservation]
      · simp [IsSourceKdfClassQuery, IsSourceFirstObservation]))).mp h |>.mono (by
        unfold sourceQF
        omega)

/-- The source-class caps derive the exact second-coordinate request cap. -/
theorem SourceKdfAdversary.secondObservationQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    adversary.main.IsQueryBoundP IsSourceSecondObservation (sourceQS i s pS) := by
  have h := isQueryBoundP_or adversary.initialQueryBound
    (isQueryBoundP_or adversary.stepQueryBound adversary.publicSecondQueryBound)
  exact ((OracleComp.isQueryBoundP_congr_pred
    (oa := adversary.main)
    (p := fun query =>
      IsSourceKdfClassQuery .initial query ∨
      IsSourceKdfClassQuery .step query ∨
      IsSourceKdfClassQuery .publicSecond query)
    (p' := IsSourceSecondObservation)
    (fun query => by
      rcases query with randomQuery | sourceQuery
      · simp [IsSourceKdfClassQuery, IsSourceSecondObservation]
      · simp [IsSourceKdfClassQuery, IsSourceSecondObservation]))).mp h |>.mono (by
        unfold sourceQS
        omega)

/-- The source-class caps derive the exact nonce-coordinate request cap. -/
theorem SourceKdfAdversary.nonceObservationQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    adversary.main.IsQueryBoundP IsSourceNonceObservation (sourceQN s pN) := by
  have h := isQueryBoundP_or adversary.stepQueryBound adversary.publicNonceQueryBound
  exact ((OracleComp.isQueryBoundP_congr_pred
    (oa := adversary.main)
    (p := fun query =>
      IsSourceKdfClassQuery .step query ∨
      IsSourceKdfClassQuery .publicNonce query)
    (p' := IsSourceNonceObservation)
    (fun query => by
      rcases query with randomQuery | sourceQuery
      · simp [IsSourceKdfClassQuery, IsSourceNonceObservation]
      · simp [IsSourceKdfClassQuery, IsSourceNonceObservation]))).mp h |>.mono (by
        unfold sourceQN
        omega)

/-- One coordinate-forwarding step emits one first query exactly for a first-exposing call. -/
theorem sourceKdfCoordinateForwardImpl_first_step
    (query : SourceKdfAdversarySpec.Domain) :
    (sourceKdfCoordinateForwardImpl query).IsQueryBoundP IsProjectionFirstQuery
      (if IsSourceFirstObservation query then 1 else 0) := by
  rcases query with randomQuery | sourceQuery
  · change (liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery)) :
        OracleComp ProjectionCoordChallengeSpec _).IsQueryBoundP
      IsProjectionFirstQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsProjectionFirstQuery]
  · rcases sourceQuery with input | input | input | view
    · change (queryFirstCoord (FixedHkdfDomain.pqxdh.address input)).IsQueryBoundP
        IsProjectionFirstQuery 1
      exact queryFirstCoord_first_bound _
    · change (queryInitialCoords (FixedHkdfDomain.ratchet.address input)).IsQueryBoundP
        IsProjectionFirstQuery 1
      exact queryInitialCoords_first_bound _
    · change (queryStepCoords (FixedHkdfDomain.ratchet.address input)).IsQueryBoundP
        IsProjectionFirstQuery 1
      exact queryStepCoords_first_bound _
    · rcases view with ⟨viewInput, domain, projection⟩
      cases projection
      · exact queryFirstCoord_first_bound _
      · exact querySecondCoord_first_bound _
      · exact queryNonceCoord_first_bound _

/-- One coordinate-forwarding step emits one second query exactly for a second-exposing call. -/
theorem sourceKdfCoordinateForwardImpl_second_step
    (query : SourceKdfAdversarySpec.Domain) :
    (sourceKdfCoordinateForwardImpl query).IsQueryBoundP IsProjectionSecondQuery
      (if IsSourceSecondObservation query then 1 else 0) := by
  rcases query with randomQuery | sourceQuery
  · change (liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery)) :
        OracleComp ProjectionCoordChallengeSpec _).IsQueryBoundP
      IsProjectionSecondQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsProjectionSecondQuery]
  · rcases sourceQuery with input | input | input | view
    · change (queryFirstCoord (FixedHkdfDomain.pqxdh.address input)).IsQueryBoundP
        IsProjectionSecondQuery 0
      exact queryFirstCoord_second_bound _
    · change (queryInitialCoords (FixedHkdfDomain.ratchet.address input)).IsQueryBoundP
        IsProjectionSecondQuery 1
      exact queryInitialCoords_second_bound _
    · change (queryStepCoords (FixedHkdfDomain.ratchet.address input)).IsQueryBoundP
        IsProjectionSecondQuery 1
      exact queryStepCoords_second_bound _
    · rcases view with ⟨viewInput, domain, projection⟩
      cases projection
      · exact queryFirstCoord_second_bound _
      · exact querySecondCoord_second_bound _
      · exact queryNonceCoord_second_bound _

/-- One coordinate-forwarding step emits one nonce query exactly for a nonce-exposing call. -/
theorem sourceKdfCoordinateForwardImpl_nonce_step
    (query : SourceKdfAdversarySpec.Domain) :
    (sourceKdfCoordinateForwardImpl query).IsQueryBoundP IsProjectionNonceQuery
      (if IsSourceNonceObservation query then 1 else 0) := by
  rcases query with randomQuery | sourceQuery
  · change (liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery)) :
        OracleComp ProjectionCoordChallengeSpec _).IsQueryBoundP
      IsProjectionNonceQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsProjectionNonceQuery]
  · rcases sourceQuery with input | input | input | view
    · change (queryFirstCoord (FixedHkdfDomain.pqxdh.address input)).IsQueryBoundP
        IsProjectionNonceQuery 0
      exact queryFirstCoord_nonce_bound _
    · change (queryInitialCoords (FixedHkdfDomain.ratchet.address input)).IsQueryBoundP
        IsProjectionNonceQuery 0
      exact queryInitialCoords_nonce_bound _
    · change (queryStepCoords (FixedHkdfDomain.ratchet.address input)).IsQueryBoundP
        IsProjectionNonceQuery 1
      exact queryStepCoords_nonce_bound _
    · rcases view with ⟨viewInput, domain, projection⟩
      cases projection
      · exact queryFirstCoord_nonce_bound _
      · exact querySecondCoord_nonce_bound _
      · exact queryNonceCoord_nonce_bound _

/-- Deferred forwarding preserves the exact first-coordinate cap. -/
theorem SourceKdfAdversary.coordinateFirstQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main).IsQueryBoundP
      IsProjectionFirstQuery (sourceQF r i s pF) := by
  refine adversary.firstObservationQueryBound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_first_step query
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_first_step query

/-- Deferred forwarding preserves the exact second-coordinate cap. -/
theorem SourceKdfAdversary.coordinateSecondQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main).IsQueryBoundP
      IsProjectionSecondQuery (sourceQS i s pS) := by
  refine adversary.secondObservationQueryBound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_second_step query
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_second_step query

/-- Deferred forwarding preserves the exact nonce-coordinate cap. -/
theorem SourceKdfAdversary.coordinateNonceQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main).IsQueryBoundP
      IsProjectionNonceQuery (sourceQN s pN) := by
  refine adversary.nonceObservationQueryBound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_nonce_step query
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_nonce_step query

/-- One deferred-forwarding step preserves adversary randomness exactly. -/
theorem sourceKdfCoordinateForwardImpl_uniform_step
    (query : SourceKdfAdversarySpec.Domain) :
    (sourceKdfCoordinateForwardImpl query).IsQueryBoundP IsProjectionCoordUniformQuery
      (if IsSourceKdfUniformQuery query then 1 else 0) := by
  rcases query with randomQuery | sourceQuery
  · change (liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery)) :
        OracleComp ProjectionCoordChallengeSpec _).IsQueryBoundP
      IsProjectionCoordUniformQuery 1
    exact (OracleComp.isQueryBoundP_query_iff
      (p := IsProjectionCoordUniformQuery) (.inl randomQuery) 1).2 (by
        simp [IsProjectionCoordUniformQuery])
  · rcases sourceQuery with input | input | input | view
    · exact queryFirstCoord_uniform_bound _
    · exact queryInitialCoords_uniform_bound _
    · exact queryStepCoords_uniform_bound _
    · rcases view with ⟨viewInput, domain, projection⟩
      cases projection
      · exact queryFirstCoord_uniform_bound _
      · exact querySecondCoord_uniform_bound _
      · exact queryNonceCoord_uniform_bound _

/-- Deferred forwarding preserves the adversary's `qU` bound without charging cache randomness. -/
theorem SourceKdfAdversary.coordinateUniformQueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main).IsQueryBoundP
      IsProjectionCoordUniformQuery qU := by
  refine adversary.uniformQueryBound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_uniform_step query
  · intro query hquery
    simpa [hquery] using sourceKdfCoordinateForwardImpl_uniform_step query

/-- Select either 32-byte position in the normalized challenge. -/
def IsProjection32Query : ProjectionCoordChallengeSpec.Domain → Prop
  | .inr (.inl _) => True
  | _ => False

instance : DecidablePred IsProjection32Query
  | .inr (.inl _) => isTrue trivial
  | .inl _ | .inr (.inr _) => isFalse id

/-- The first and second caps combine to the exact logical `q32` cap. -/
theorem SourceKdfAdversary.coordinate32QueryBound {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main).IsQueryBoundP
      IsProjection32Query (sourceQ32 r i s pF pS) := by
  have h := isQueryBoundP_or adversary.coordinateFirstQueryBound
    adversary.coordinateSecondQueryBound
  exact (OracleComp.isQueryBoundP_congr_pred
    (oa := simulateQ sourceKdfCoordinateForwardImpl adversary.main)
    (p := fun query => IsProjectionFirstQuery query ∨ IsProjectionSecondQuery query)
    (p' := IsProjection32Query)
    (fun query => by
      rcases query with randomQuery | coordinate
      · simp [IsProjectionFirstQuery, IsProjectionSecondQuery, IsProjection32Query]
      · rcases coordinate with coord | nonce
        · rcases coord with ⟨address, slot⟩
          cases slot <;>
            simp [IsProjectionFirstQuery, IsProjectionSecondQuery, IsProjection32Query]
        · simp [IsProjectionFirstQuery, IsProjectionSecondQuery, IsProjection32Query])).mp h

/-! ## Exact normalized lazy caches -/

/-- Separate lazy caches retain the exact mixed-width coordinate types. -/
abbrev ProjectionCoordCache := Projection32RO.QueryCache × Projection12RO.QueryCache

/-- Cache one 32-byte coordinate while leaving the nonce cache untouched. -/
noncomputable def projection32LazyRandomImpl :
    QueryImpl Projection32RO (StateT ProjectionCoordCache ProbComp) :=
  fun coord => StateT.mk fun state =>
    (fun result : Projection32Value × Projection32RO.QueryCache =>
      (result.1, (result.2, state.2))) <$>
        (Projection32RO.randomOracle coord).run state.1

/-- Cache one nonce coordinate while leaving the 32-byte cache untouched. -/
noncomputable def projection12LazyRandomImpl :
    QueryImpl Projection12RO (StateT ProjectionCoordCache ProbComp) :=
  fun coord => StateT.mk fun state =>
    (fun result : Projection12Value × Projection12RO.QueryCache =>
      (result.1, (state.1, result.2))) <$>
        (Projection12RO.randomOracle coord).run state.2

/-- Normalized lazy random handler; adversary randomness is never installed in either cache. -/
noncomputable def projectionCoordLazyRandomImpl :
    QueryImpl ProjectionCoordChallengeSpec (StateT ProjectionCoordCache ProbComp) :=
  (uniformSampleImpl (spec := unifSpec)).liftTarget
      (StateT ProjectionCoordCache ProbComp) +
    (projection32LazyRandomImpl + projection12LazyRandomImpl)

@[simp] theorem projectionCoordLazyRandomImpl_uniform_run
    (query : unifSpec.Domain) (state : ProjectionCoordCache) :
    (projectionCoordLazyRandomImpl (.inl query)).run state =
      (fun value => (value, state)) <$> uniformSampleImpl query := by
  rfl

@[simp] theorem projectionCoordLazyRandomImpl_first_run
    (coord : Coord32) (state : ProjectionCoordCache) :
    (projectionCoordLazyRandomImpl (.inr (.inl coord))).run state =
      (fun result : Projection32Value × Projection32RO.QueryCache =>
        (result.1, (result.2, state.2))) <$>
          (Projection32RO.randomOracle coord).run state.1 := by
  rfl

@[simp] theorem projectionCoordLazyRandomImpl_nonce_run
    (coord : Coord12) (state : ProjectionCoordCache) :
    (projectionCoordLazyRandomImpl (.inr (.inr coord))).run state =
      (fun result : Projection12Value × Projection12RO.QueryCache =>
        (result.1, (state.1, result.2))) <$>
          (Projection12RO.randomOracle coord).run state.2 := by
  rfl

/-- A cached 32-byte identity returns its stored value and changes neither cache. -/
theorem projectionCoordLazyRandomImpl_first_run_hit
    (coord : Coord32) (state : ProjectionCoordCache) (value : Projection32Value)
    (hcache : state.1 coord = some value) :
    (projectionCoordLazyRandomImpl (.inr (.inl coord))).run state =
      pure (value, state) := by
  rw [projectionCoordLazyRandomImpl_first_run]
  unfold OracleSpec.randomOracle
  rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache]
  rfl

/-- A fresh 32-byte identity samples and installs exactly one uniform 32-byte value. -/
theorem projectionCoordLazyRandomImpl_first_run_miss
    (coord : Coord32) (state : ProjectionCoordCache)
    (hcache : state.1 coord = none) :
    (projectionCoordLazyRandomImpl (.inr (.inl coord))).run state =
      (fun value : Projection32Value =>
        (value, (state.1.cacheQuery coord value, state.2))) <$>
          ($ᵗ Projection32Value) := by
  rw [projectionCoordLazyRandomImpl_first_run]
  unfold OracleSpec.randomOracle
  rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache]
  simp only [uniformSampleImpl, Functor.map_map]

/-- A cached nonce identity returns its stored value and changes neither cache. -/
theorem projectionCoordLazyRandomImpl_nonce_run_hit
    (coord : Coord12) (state : ProjectionCoordCache) (value : Projection12Value)
    (hcache : state.2 coord = some value) :
    (projectionCoordLazyRandomImpl (.inr (.inr coord))).run state =
      pure (value, state) := by
  rw [projectionCoordLazyRandomImpl_nonce_run]
  unfold OracleSpec.randomOracle
  rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache]
  rfl

/-- A fresh nonce identity samples and installs exactly one uniform 12-byte value. -/
theorem projectionCoordLazyRandomImpl_nonce_run_miss
    (coord : Coord12) (state : ProjectionCoordCache)
    (hcache : state.2 coord = none) :
    (projectionCoordLazyRandomImpl (.inr (.inr coord))).run state =
      (fun value : Projection12Value =>
        (value, (state.1, state.2.cacheQuery coord value))) <$>
          ($ᵗ Projection12Value) := by
  rw [projectionCoordLazyRandomImpl_nonce_run]
  unfold OracleSpec.randomOracle
  rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache]
  simp only [uniformSampleImpl, Functor.map_map]

/-- Accidental equality of two distinct cached 32-byte identities. -/
def ProjectionCacheBad32 (state : ProjectionCoordCache) : Prop :=
  CacheHasCollision state.1

/-- Accidental equality of two distinct cached nonce identities. -/
def ProjectionCacheBad12 (state : ProjectionCoordCache) : Prop :=
  CacheHasCollision state.2

/-- Same-address first/second equality is included because the identities are distinct. -/
theorem projectionCacheBad32_of_same_address_cross_slot
    (state : ProjectionCoordCache) (address : JointKdfAddress)
    (first second : Projection32Value)
    (hfirst : state.1 (firstCoord address) = some first)
    (hsecond : state.1 (secondCoord address) = some second)
    (hequal : first = second) :
    ProjectionCacheBad32 state := by
  exact ⟨firstCoord address, secondCoord address, first, second,
    firstCoord_ne_secondCoord address, hfirst, hsecond, heq_of_eq hequal⟩

/-- Equal-address repetitions cannot supply the distinct-input premise of cache collision. -/
theorem projectionCacheBad32_witnesses_distinct_identities
    (state : ProjectionCoordCache) (hbad : ProjectionCacheBad32 state) :
    ∃ left right : Coord32, left ≠ right ∧
      ∃ leftValue rightValue : Projection32Value,
        state.1 left = some leftValue ∧ state.1 right = some rightValue ∧
          leftValue = rightValue := by
  rcases hbad with ⟨left, right, leftValue, rightValue, hne, hleft, hright, heq⟩
  exact ⟨left, right, hne, leftValue, rightValue, hleft, hright, eq_of_heq heq⟩

/-- Exact correspondence between a 32-byte observation list and its coordinate cache. -/
def ProjectionObservationsMatch32
    (cache : Projection32RO.QueryCache) (observations : List Observation32) : Prop :=
  (∀ observation ∈ observations,
      cache observation.coord = some observation.value) ∧
    (∀ coord value, cache coord = some value →
      ⟨coord, value⟩ ∈ observations)

/-- Exact correspondence between a nonce observation list and its coordinate cache. -/
def ProjectionObservationsMatch12
    (cache : Projection12RO.QueryCache) (observations : List Observation12) : Prop :=
  (∀ observation ∈ observations,
      cache observation.coord = some observation.value) ∧
    (∀ coord value, cache coord = some value →
      ⟨coord, value⟩ ∈ observations)

/-- Both logs mention exactly and only coordinates actually requested from the normalized view. -/
def ProjectionObservationInvariant
    (cache : ProjectionCoordCache)
    (observations32 : List Observation32)
    (observations12 : List Observation12) : Prop :=
  ProjectionObservationsMatch32 cache.1 observations32 ∧
    ProjectionObservationsMatch12 cache.2 observations12

/-- Under exact cache/log correspondence, list-level 32-byte bad is exactly cache bad. -/
theorem bad32_iff_projectionCacheBad32
    (state : ProjectionCoordCache) (observations : List Observation32)
    (hmatch : ProjectionObservationsMatch32 state.1 observations) :
    Bad32 observations ↔ ProjectionCacheBad32 state := by
  constructor
  · rintro ⟨left, hleft, right, hright, hne, hequal⟩
    exact ⟨left.coord, right.coord, left.value, right.value, hne,
      hmatch.1 left hleft, hmatch.1 right hright, heq_of_eq hequal⟩
  · rintro ⟨left, right, leftValue, rightValue, hne, hleft, hright, hequal⟩
    exact ⟨⟨left, leftValue⟩, hmatch.2 left leftValue hleft,
      ⟨right, rightValue⟩, hmatch.2 right rightValue hright,
      hne, eq_of_heq hequal⟩

/-- Under exact cache/log correspondence, list-level nonce bad is exactly cache bad. -/
theorem bad12_iff_projectionCacheBad12
    (state : ProjectionCoordCache) (observations : List Observation12)
    (hmatch : ProjectionObservationsMatch12 state.2 observations) :
    Bad12 observations ↔ ProjectionCacheBad12 state := by
  constructor
  · rintro ⟨left, hleft, right, hright, hne, hequal⟩
    exact ⟨left.coord, right.coord, left.value, right.value, hne,
      hmatch.1 left hleft, hmatch.1 right hright, heq_of_eq hequal⟩
  · rintro ⟨left, right, leftValue, rightValue, hne, hleft, hright, hequal⟩
    exact ⟨⟨left, leftValue⟩, hmatch.2 left leftValue hleft,
      ⟨right, rightValue⟩, hmatch.2 right rightValue hright,
      hne, eq_of_heq hequal⟩

/-- Logging a consistent 32-byte answer preserves exact cache/list correspondence. -/
theorem ProjectionObservationsMatch32.cacheQuery_cons
    {cache : Projection32RO.QueryCache} {observations : List Observation32}
    (hmatch : ProjectionObservationsMatch32 cache observations)
    (coord : Coord32) (value : Projection32Value)
    (hconsistent : cache coord = none ∨ cache coord = some value) :
    ProjectionObservationsMatch32 (cache.cacheQuery coord value)
      (⟨coord, value⟩ :: observations) := by
  constructor
  · intro observation hobservation
    cases hobservation with
    | head => exact QueryCache.cacheQuery_self cache coord value
    | tail _ htail =>
        by_cases heq : observation.coord = coord
        · rcases hconsistent with hnone | hsome
          · have hobservation := hmatch.1 observation htail
            rw [heq, hnone] at hobservation
            contradiction
          · have hvalue : observation.value = value := by
              have hobservation := hmatch.1 observation htail
              rw [heq, hsome] at hobservation
              exact Option.some.inj hobservation.symm
            rw [heq, QueryCache.cacheQuery_self, hvalue]
        · rw [QueryCache.cacheQuery_of_ne cache value heq]
          exact hmatch.1 observation htail
  · intro other otherValue hcache
    by_cases heq : other = coord
    · subst heq
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hcache
      subst hcache
      exact List.Mem.head _
    · rw [QueryCache.cacheQuery_of_ne cache value heq] at hcache
      exact List.Mem.tail _ (hmatch.2 other otherValue hcache)

/-- Logging a consistent nonce answer preserves exact cache/list correspondence. -/
theorem ProjectionObservationsMatch12.cacheQuery_cons
    {cache : Projection12RO.QueryCache} {observations : List Observation12}
    (hmatch : ProjectionObservationsMatch12 cache observations)
    (coord : Coord12) (value : Projection12Value)
    (hconsistent : cache coord = none ∨ cache coord = some value) :
    ProjectionObservationsMatch12 (cache.cacheQuery coord value)
      (⟨coord, value⟩ :: observations) := by
  constructor
  · intro observation hobservation
    cases hobservation with
    | head => exact QueryCache.cacheQuery_self cache coord value
    | tail _ htail =>
        by_cases heq : observation.coord = coord
        · rcases hconsistent with hnone | hsome
          · have hobservation := hmatch.1 observation htail
            rw [heq, hnone] at hobservation
            contradiction
          · have hvalue : observation.value = value := by
              have hobservation := hmatch.1 observation htail
              rw [heq, hsome] at hobservation
              exact Option.some.inj hobservation.symm
            rw [heq, QueryCache.cacheQuery_self, hvalue]
        · rw [QueryCache.cacheQuery_of_ne cache value heq]
          exact hmatch.1 observation htail
  · intro other otherValue hcache
    by_cases heq : other = coord
    · subst heq
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hcache
      subst hcache
      exact List.Mem.head _
    · rw [QueryCache.cacheQuery_of_ne cache value heq] at hcache
      exact List.Mem.tail _ (hmatch.2 other otherValue hcache)

/-- Cache plus the exact sequence of coordinates returned to the source computation. -/
structure ProjectionObservationState where
  cache : ProjectionCoordCache
  observations32 : List Observation32
  observations12 : List Observation12

/-- Initial normalized cache/log state. -/
def emptyProjectionObservationState : ProjectionObservationState :=
  ⟨(∅, ∅), [], []⟩

/-- The observation state satisfies exact two-way cache/log correspondence. -/
def ProjectionObservationState.Invariant (state : ProjectionObservationState) : Prop :=
  ProjectionObservationInvariant state.cache state.observations32 state.observations12

@[simp] theorem emptyProjectionObservationState_invariant :
    emptyProjectionObservationState.Invariant := by
  constructor <;> constructor <;> simp [emptyProjectionObservationState]

/-- Record one returned 32-byte coordinate and update only its cache. -/
def ProjectionObservationState.log32 (state : ProjectionObservationState)
    (coord : Coord32) (value : Projection32Value) : ProjectionObservationState where
  cache := (state.cache.1.cacheQuery coord value, state.cache.2)
  observations32 := ⟨coord, value⟩ :: state.observations32
  observations12 := state.observations12

/-- Record one returned nonce coordinate and update only its cache. -/
def ProjectionObservationState.log12 (state : ProjectionObservationState)
    (coord : Coord12) (value : Projection12Value) : ProjectionObservationState where
  cache := (state.cache.1, state.cache.2.cacheQuery coord value)
  observations32 := state.observations32
  observations12 := ⟨coord, value⟩ :: state.observations12

/-- A consistent 32-byte response preserves the combined observation invariant. -/
theorem ProjectionObservationState.Invariant.log32
    {state : ProjectionObservationState} (hinvariant : state.Invariant)
    (coord : Coord32) (value : Projection32Value)
    (hconsistent : state.cache.1 coord = none ∨
      state.cache.1 coord = some value) :
    (state.log32 coord value).Invariant := by
  exact ⟨hinvariant.1.cacheQuery_cons coord value hconsistent, hinvariant.2⟩

/-- A consistent nonce response preserves the combined observation invariant. -/
theorem ProjectionObservationState.Invariant.log12
    {state : ProjectionObservationState} (hinvariant : state.Invariant)
    (coord : Coord12) (value : Projection12Value)
    (hconsistent : state.cache.2 coord = none ∨
      state.cache.2 coord = some value) :
    (state.log12 coord value).Invariant := by
  exact ⟨hinvariant.1, hinvariant.2.cacheQuery_cons coord value hconsistent⟩

/-- Normalized lazy coordinate handler augmented with exact returned-coordinate logs.

The handler never logs latent positions: a 32-byte query adds one `Observation32`, a nonce query
adds one `Observation12`, and adversary randomness adds neither. -/
noncomputable def projectionCoordCachingLoggingImpl :
    QueryImpl ProjectionCoordChallengeSpec
      (StateT ProjectionObservationState ProbComp)
  | .inl randomQuery => StateT.mk fun state =>
      (fun value => (value, state)) <$>
        uniformSampleImpl (spec := unifSpec) randomQuery
  | .inr (.inl coord) => StateT.mk fun state =>
      match state.cache.1 coord with
      | some value => pure (value, state.log32 coord value)
      | none => (fun value : Projection32Value =>
          (value, state.log32 coord value)) <$> ($ᵗ Projection32Value)
  | .inr (.inr coord) => StateT.mk fun state =>
      match state.cache.2 coord with
      | some value => pure (value, state.log12 coord value)
      | none => (fun value : Projection12Value =>
          (value, state.log12 coord value)) <$> ($ᵗ Projection12Value)

@[simp] theorem projectionCoordCachingLoggingImpl_uniform_run
    (query : unifSpec.Domain) (state : ProjectionObservationState) :
    (projectionCoordCachingLoggingImpl (.inl query)).run state =
      (fun value => (value, state)) <$>
        uniformSampleImpl (spec := unifSpec) query := by
  rfl

theorem projectionCoordCachingLoggingImpl_first_run_hit
    (coord : Coord32) (state : ProjectionObservationState)
    (value : Projection32Value) (hcache : state.cache.1 coord = some value) :
    (projectionCoordCachingLoggingImpl (.inr (.inl coord))).run state =
      pure (value, state.log32 coord value) := by
  simp [projectionCoordCachingLoggingImpl, hcache]

theorem projectionCoordCachingLoggingImpl_first_run_miss
    (coord : Coord32) (state : ProjectionObservationState)
    (hcache : state.cache.1 coord = none) :
    (projectionCoordCachingLoggingImpl (.inr (.inl coord))).run state =
      (fun value : Projection32Value =>
        (value, state.log32 coord value)) <$> ($ᵗ Projection32Value) := by
  simp [projectionCoordCachingLoggingImpl, hcache]

theorem projectionCoordCachingLoggingImpl_nonce_run_hit
    (coord : Coord12) (state : ProjectionObservationState)
    (value : Projection12Value) (hcache : state.cache.2 coord = some value) :
    (projectionCoordCachingLoggingImpl (.inr (.inr coord))).run state =
      pure (value, state.log12 coord value) := by
  simp [projectionCoordCachingLoggingImpl, hcache]

theorem projectionCoordCachingLoggingImpl_nonce_run_miss
    (coord : Coord12) (state : ProjectionObservationState)
    (hcache : state.cache.2 coord = none) :
    (projectionCoordCachingLoggingImpl (.inr (.inr coord))).run state =
      (fun value : Projection12Value =>
        (value, state.log12 coord value)) <$> ($ᵗ Projection12Value) := by
  simp [projectionCoordCachingLoggingImpl, hcache]

/-- Every single logged-coordinate step preserves exact two-way cache/log correspondence. -/
theorem projectionCoordCachingLoggingImpl_preserves_invariant
    (query : ProjectionCoordChallengeSpec.Domain)
    (state : ProjectionObservationState) (hinvariant : state.Invariant) :
    ∀ result ∈ support ((projectionCoordCachingLoggingImpl query).run state),
      result.2.Invariant := by
  rcases query with randomQuery | coordinateQuery
  · intro result hresult
    rw [projectionCoordCachingLoggingImpl_uniform_run] at hresult
    change result ∈ support (((fun value : unifSpec.Range randomQuery =>
      (value, state)) <$> uniformSampleImpl (spec := unifSpec) randomQuery) :
        ProbComp (unifSpec.Range randomQuery × ProjectionObservationState)) at hresult
    rw [support_map] at hresult
    obtain ⟨value, _, rfl⟩ := hresult
    exact hinvariant
  · rcases coordinateQuery with coord | nonceCoord
    · cases hcache : state.cache.1 coord with
      | none =>
          intro result hresult
          rw [projectionCoordCachingLoggingImpl_first_run_miss coord state hcache] at hresult
          change result ∈ support (((fun value : Projection32Value =>
            (value, state.log32 coord value)) <$> ($ᵗ Projection32Value)) :
              ProbComp (Projection32Value × ProjectionObservationState)) at hresult
          rw [support_map] at hresult
          obtain ⟨value, _, rfl⟩ := hresult
          exact hinvariant.log32 coord value (Or.inl hcache)
      | some value =>
          intro result hresult
          change Projection32Value × ProjectionObservationState at result
          rw [projectionCoordCachingLoggingImpl_first_run_hit coord state value hcache] at hresult
          change result ∈ support
            (pure (value, state.log32 coord value) :
              ProbComp (Projection32Value × ProjectionObservationState)) at hresult
          rw [support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hinvariant.log32 coord value (Or.inr hcache)
    · cases hcache : state.cache.2 nonceCoord with
      | none =>
          intro result hresult
          rw [projectionCoordCachingLoggingImpl_nonce_run_miss nonceCoord state hcache] at hresult
          change result ∈ support (((fun value : Projection12Value =>
            (value, state.log12 nonceCoord value)) <$> ($ᵗ Projection12Value)) :
              ProbComp (Projection12Value × ProjectionObservationState)) at hresult
          rw [support_map] at hresult
          obtain ⟨value, _, rfl⟩ := hresult
          exact hinvariant.log12 nonceCoord value (Or.inl hcache)
      | some value =>
          intro result hresult
          change Projection12Value × ProjectionObservationState at result
          rw [projectionCoordCachingLoggingImpl_nonce_run_hit nonceCoord state value hcache]
            at hresult
          change result ∈ support
            (pure (value, state.log12 nonceCoord value) :
              ProbComp (Projection12Value × ProjectionObservationState)) at hresult
          rw [support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hinvariant.log12 nonceCoord value (Or.inr hcache)

/-- Structural query step for the observation-logging handler. -/
private lemma run_simulateQ_projectionCoordCachingLogging_query_bind
    {beta : Type} (query : ProjectionCoordChallengeSpec.Domain)
    (rest : ProjectionCoordChallengeSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionObservationState) :
    (simulateQ projectionCoordCachingLoggingImpl
      (liftM (ProjectionCoordChallengeSpec.query query) >>= rest)).run state =
        (projectionCoordCachingLoggingImpl query).run state >>= fun result =>
          (simulateQ projectionCoordCachingLoggingImpl (rest result.1)).run result.2 := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  simp [OracleQuery.cont_query]

/-- Every complete normalized execution from an invariant state retains exact cache/log
correspondence. -/
theorem projectionCoordCachingLoggingImpl_simulateQ_invariant
    {beta : Type} (computation : OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionObservationState) (hinvariant : state.Invariant) :
    ∀ result ∈ support
        ((simulateQ projectionCoordCachingLoggingImpl computation).run state),
      result.2.Invariant := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure output =>
      intro result hresult
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact hinvariant
  | query_bind query rest ih =>
      intro result hresult
      rw [run_simulateQ_projectionCoordCachingLogging_query_bind, support_bind] at hresult
      simp only [Set.mem_iUnion] at hresult
      obtain ⟨middle, hmiddle, hresult⟩ := hresult
      exact ih middle.1 middle.2
        (projectionCoordCachingLoggingImpl_preserves_invariant
          query state hinvariant middle hmiddle)
        result hresult

/-- Reinstalling the already-cached answer is extensionally the same cache. -/
theorem queryCache_cacheQuery_eq_of_some
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι}
    (cache : QueryCache spec) (query : spec.Domain) (value : spec.Range query)
    (hcache : cache query = some value) :
    cache.cacheQuery query value = cache := by
  apply QueryCache.ext
  intro other
  by_cases heq : other = query
  · subst other
    rw [QueryCache.cacheQuery_self, hcache]
  · rw [QueryCache.cacheQuery_of_ne cache value heq]

/-- Erasing one logging step gives exactly the nonlogging lazy-cache step. -/
theorem projectionCoordCachingLoggingImpl_cache_marginal
    (query : ProjectionCoordChallengeSpec.Domain)
    (state : ProjectionObservationState) :
    (fun result => (result.1, result.2.cache)) <$>
        (projectionCoordCachingLoggingImpl query).run state =
      (projectionCoordLazyRandomImpl query).run state.cache := by
  rcases query with randomQuery | coordinateQuery
  · rw [projectionCoordCachingLoggingImpl_uniform_run,
      projectionCoordLazyRandomImpl_uniform_run]
    change (fun result : unifSpec.Range randomQuery × ProjectionObservationState =>
        (result.1, result.2.cache)) <$>
          ((fun value : unifSpec.Range randomQuery => (value, state)) <$>
            uniformSampleImpl (spec := unifSpec) randomQuery) =
      (fun value : unifSpec.Range randomQuery => (value, state.cache)) <$>
        uniformSampleImpl (spec := unifSpec) randomQuery
    simp only [Functor.map_map]
  · rcases coordinateQuery with coord | nonceCoord
    · cases hcache : state.cache.1 coord with
      | none =>
          rw [projectionCoordCachingLoggingImpl_first_run_miss coord state hcache,
            projectionCoordLazyRandomImpl_first_run_miss coord state.cache hcache]
          change (fun result : Projection32Value × ProjectionObservationState =>
              (result.1, result.2.cache)) <$>
                ((fun value : Projection32Value =>
                  (value, state.log32 coord value)) <$> ($ᵗ Projection32Value)) =
            (fun value : Projection32Value =>
              (value, (state.cache.1.cacheQuery coord value, state.cache.2))) <$>
                ($ᵗ Projection32Value)
          simp only [Functor.map_map]
          rfl
      | some value =>
          rw [projectionCoordCachingLoggingImpl_first_run_hit coord state value hcache,
            projectionCoordLazyRandomImpl_first_run_hit coord state.cache value hcache]
          change (fun result : Projection32Value × ProjectionObservationState =>
              (result.1, result.2.cache)) <$>
                pure (value, state.log32 coord value) = pure (value, state.cache)
          simp only [map_pure]
          have heq := queryCache_cacheQuery_eq_of_some state.cache.1 coord value hcache
          simp [ProjectionObservationState.log32, heq]
    · cases hcache : state.cache.2 nonceCoord with
      | none =>
          rw [projectionCoordCachingLoggingImpl_nonce_run_miss nonceCoord state hcache,
            projectionCoordLazyRandomImpl_nonce_run_miss nonceCoord state.cache hcache]
          change (fun result : Projection12Value × ProjectionObservationState =>
              (result.1, result.2.cache)) <$>
                ((fun value : Projection12Value =>
                  (value, state.log12 nonceCoord value)) <$> ($ᵗ Projection12Value)) =
            (fun value : Projection12Value =>
              (value, (state.cache.1,
                state.cache.2.cacheQuery nonceCoord value))) <$>
                  ($ᵗ Projection12Value)
          simp only [Functor.map_map]
          rfl
      | some value =>
          rw [projectionCoordCachingLoggingImpl_nonce_run_hit nonceCoord state value hcache,
            projectionCoordLazyRandomImpl_nonce_run_hit nonceCoord state.cache value hcache]
          change (fun result : Projection12Value × ProjectionObservationState =>
              (result.1, result.2.cache)) <$>
                pure (value, state.log12 nonceCoord value) = pure (value, state.cache)
          simp only [map_pure]
          have heq := queryCache_cacheQuery_eq_of_some state.cache.2 nonceCoord value hcache
          simp [ProjectionObservationState.log12, heq]

/-- Erasing the observation logs after any normalized computation gives exactly the original
nonlogging cache run. -/
theorem projectionCoordCachingLoggingImpl_simulateQ_cache_marginal
    {beta : Type} (computation : OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionObservationState) :
    Prod.map id ProjectionObservationState.cache <$>
        (simulateQ projectionCoordCachingLoggingImpl computation).run state =
      (simulateQ projectionCoordLazyRandomImpl computation).run state.cache := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    projectionCoordCachingLoggingImpl projectionCoordLazyRandomImpl
    ProjectionObservationState.cache
    (fun query state =>
      projectionCoordCachingLoggingImpl_cache_marginal query state)
    computation state

/-- Run the exact source computation against the normalized deferred-coordinate cache. -/
noncomputable def projectionCollisionRandomRun {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    ProbComp (Bool × ProjectionCoordCache) :=
  (simulateQ projectionCoordLazyRandomImpl
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main)).run (∅, ∅)

/-- The same normalized random experiment with the exact sequence of returned coordinates
retained for stating the source-level collision event. -/
noncomputable def projectionCollisionObservedRandomRun {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    ProbComp (Bool × ProjectionObservationState) :=
  (simulateQ projectionCoordCachingLoggingImpl
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main)).run
      emptyProjectionObservationState

/-- Random-world output/output collision event, kept separate by output width. -/
def ProjectionCollisionEvent (result : Bool × ProjectionCoordCache) : Prop :=
  ProjectionCacheBad32 result.2 ∨ ProjectionCacheBad12 result.2

/-- Source-visible collision event over exactly the projection coordinates returned by the
source-shaped interface. -/
def ProjectionObservedCollisionEvent
    (result : Bool × ProjectionObservationState) : Prop :=
  Bad32 result.2.observations32 ∨ Bad12 result.2.observations12

/-- Erasing source-visible logs from the observed run gives exactly the cache-only birthday
experiment, as a distribution equality. -/
theorem projectionCollisionObservedRandomRun_cache_marginal
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Prod.map id ProjectionObservationState.cache <$>
        projectionCollisionObservedRandomRun adversary =
      projectionCollisionRandomRun adversary := by
  unfold projectionCollisionObservedRandomRun projectionCollisionRandomRun
  exact projectionCoordCachingLoggingImpl_simulateQ_cache_marginal
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main)
    emptyProjectionObservationState

/-- On every reachable observed execution, list collision is exactly cache collision. -/
theorem projectionObservedCollisionEvent_iff_cache
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN)
    (result : Bool × ProjectionObservationState)
    (hresult : result ∈ support (projectionCollisionObservedRandomRun adversary)) :
    ProjectionObservedCollisionEvent result ↔
      ProjectionCollisionEvent (result.1, result.2.cache) := by
  have hinvariant := projectionCoordCachingLoggingImpl_simulateQ_invariant
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main)
    emptyProjectionObservationState emptyProjectionObservationState_invariant
    result hresult
  exact or_congr
    (bad32_iff_projectionCacheBad32 result.2.cache result.2.observations32
      hinvariant.1)
    (bad12_iff_projectionCacheBad12 result.2.cache result.2.observations12
      hinvariant.2)

/-- The logged source event and the cache birthday event have exactly equal probability. -/
theorem probEvent_projectionObservedCollision_eq_cache
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[ProjectionObservedCollisionEvent |
        projectionCollisionObservedRandomRun adversary] =
      Pr[ProjectionCollisionEvent | projectionCollisionRandomRun adversary] := by
  calc
    Pr[ProjectionObservedCollisionEvent |
        projectionCollisionObservedRandomRun adversary] =
        Pr[fun result => ProjectionCollisionEvent (result.1, result.2.cache) |
          projectionCollisionObservedRandomRun adversary] :=
      probEvent_congr'
        (fun result hresult =>
          projectionObservedCollisionEvent_iff_cache adversary result hresult)
        rfl
    _ = Pr[ProjectionCollisionEvent |
        Prod.map id ProjectionObservationState.cache <$>
          projectionCollisionObservedRandomRun adversary] := by
      rw [probEvent_map]
      congr 1
    _ = Pr[ProjectionCollisionEvent | projectionCollisionRandomRun adversary] := by
      rw [projectionCollisionObservedRandomRun_cache_marginal]

/-! ## Exact output-space sizes -/

/-- A 32-byte projection has exactly `2^256` possible values. -/
theorem projection32Value_card : Fintype.card Projection32Value = 2 ^ 256 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- A 12-byte nonce projection has exactly `2^96` possible values. -/
theorem projection12Value_card : Fintype.card Projection12Value = 2 ^ 96 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 12 = (2 ^ 8) ^ 12 := by norm_num
    _ = 2 ^ (8 * 12) := by rw [pow_mul]
    _ = 2 ^ 96 := by norm_num

/-! ## Predicate-aware birthday bounds -/

open Classical in
/-- At most one already-populated cache key can be charged for each colliding answer. -/
private lemma card_cacheQuery_collision_le_support
    {ι : Type} [DecidableEq ι] {spec : OracleSpec.{0, 0} ι} [spec.DecidableEq]
    [IsUniformSpec spec]
    {cache₀ : QueryCache spec} {query : spec.Domain}
    {supportKeys : Finset spec.Domain}
    (hnocoll : ¬CacheHasCollision cache₀)
    (hsupport : ∀ other, cache₀ other ≠ none → other ∈ supportKeys) :
    (Finset.univ.filter
      (fun value => CacheHasCollision (cache₀.cacheQuery query value))).card ≤
        supportKeys.card := by
  have hmust : ∀ value, CacheHasCollision (cache₀.cacheQuery query value) →
      ∃ other : spec.Domain, other ≠ query ∧
        ∃ oldValue : spec.Range other,
          cache₀ other = some oldValue ∧ HEq value oldValue := by
    intro value ⟨left, right, leftValue, rightValue, hne, hleft, hright, hequal⟩
    by_cases hleftQuery : left = query
    · subst hleftQuery
      refine ⟨right, hne.symm, rightValue,
        by rwa [QueryCache.cacheQuery_of_ne _ _ hne.symm] at hright, ?_⟩
      simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hleft
      subst hleft
      exact hequal
    · by_cases hrightQuery : right = query
      · subst hrightQuery
        refine ⟨left, hne, leftValue,
          by rwa [QueryCache.cacheQuery_of_ne _ _ hleftQuery] at hleft, ?_⟩
        simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hright
        subst hright
        exact hequal.symm
      · exact absurd ⟨left, right, leftValue, rightValue, hne,
          by rwa [QueryCache.cacheQuery_of_ne _ _ hleftQuery] at hleft,
          by rwa [QueryCache.cacheQuery_of_ne _ _ hrightQuery] at hright,
          hequal⟩ hnocoll
  let keyOf : spec.Range query → spec.Domain := fun value =>
    if hbad : CacheHasCollision (cache₀.cacheQuery query value) then
      (hmust value hbad).choose
    else query
  refine Finset.card_le_card_of_injOn keyOf (fun value hvalue => ?_)
    (fun value₁ hvalue₁ value₂ hvalue₂ hkeys => ?_)
  · have hbad := (Finset.mem_filter.mp hvalue).2
    obtain ⟨_, oldValue, hcache, _⟩ := (hmust value hbad).choose_spec
    rw [show keyOf value = _ from dif_pos hbad]
    exact hsupport _ (hcache ▸ Option.some_ne_none oldValue)
  · have hbad₁ := (Finset.mem_filter.mp hvalue₁).2
    have hbad₂ := (Finset.mem_filter.mp hvalue₂).2
    rw [show keyOf value₁ = _ from dif_pos hbad₁,
      show keyOf value₂ = _ from dif_pos hbad₂] at hkeys
    obtain ⟨_, oldValue₁, hcache₁, hequal₁⟩ := (hmust value₁ hbad₁).choose_spec
    obtain ⟨_, oldValue₂, hcache₂, hequal₂⟩ := (hmust value₂ hbad₂).choose_spec
    suffices hcached : ∀ (left right : spec.Domain)
        (leftValue : spec.Range left) (rightValue : spec.Range right),
        cache₀ left = some leftValue → cache₀ right = some rightValue →
          left = right → HEq leftValue rightValue from
      eq_of_heq (hequal₁.trans
        ((hcached _ _ _ _ hcache₁ hcache₂ hkeys).trans hequal₂.symm))
    intro left right leftValue rightValue hleft hright hsame
    subst hsame
    rw [hleft] at hright
    exact heq_of_eq (Option.some.inj hright)

/-- Structural query step for the normalized stateful handler. -/
private lemma run_simulateQ_projectionCoordLazyRandom_query_bind
    {beta : Type} (query : ProjectionCoordChallengeSpec.Domain)
    (rest : ProjectionCoordChallengeSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionCoordCache) :
    (simulateQ projectionCoordLazyRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query query) >>= rest)).run state =
        (projectionCoordLazyRandomImpl query).run state >>= fun result =>
          (simulateQ projectionCoordLazyRandomImpl (rest result.1)).run result.2 := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  simp [OracleQuery.cont_query]

private lemma run_simulateQ_projectionCoordLazyRandom_uniform_bind
    {beta : Type} (query : unifSpec.Domain)
    (rest : unifSpec.Range query → OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionCoordCache) :
    (simulateQ projectionCoordLazyRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inl query)) >>= rest)).run state =
        uniformSampleImpl query >>= fun value =>
          (simulateQ projectionCoordLazyRandomImpl (rest value)).run state := by
  rw [run_simulateQ_projectionCoordLazyRandom_query_bind,
    projectionCoordLazyRandomImpl_uniform_run]
  change (((fun value : unifSpec.Range query => (value, state)) <$>
      uniformSampleImpl query) >>= fun result : unifSpec.Range query × ProjectionCoordCache =>
        (simulateQ projectionCoordLazyRandomImpl (rest result.1)).run result.2) = _
  rw [bind_map_left]

private lemma run_simulateQ_projectionCoordLazyRandom_first_bind_hit
    {beta : Type} (coord : Coord32)
    (rest : Projection32Value → OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionCoordCache) (value : Projection32Value)
    (hcache : state.1 coord = some value) :
    (simulateQ projectionCoordLazyRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) >>= rest)).run state =
        (simulateQ projectionCoordLazyRandomImpl (rest value)).run state := by
  rw [run_simulateQ_projectionCoordLazyRandom_query_bind,
    projectionCoordLazyRandomImpl_first_run_hit coord state value hcache]
  change (pure (value, state) >>= fun result : Projection32Value × ProjectionCoordCache =>
    (simulateQ projectionCoordLazyRandomImpl (rest result.1)).run result.2) = _
  rw [pure_bind]

private lemma run_simulateQ_projectionCoordLazyRandom_first_bind_miss
    {beta : Type} (coord : Coord32)
    (rest : Projection32Value → OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionCoordCache) (hcache : state.1 coord = none) :
    (simulateQ projectionCoordLazyRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) >>= rest)).run state =
        ($ᵗ Projection32Value) >>= fun value =>
          (simulateQ projectionCoordLazyRandomImpl (rest value)).run
            (state.1.cacheQuery coord value, state.2) := by
  rw [run_simulateQ_projectionCoordLazyRandom_query_bind,
    projectionCoordLazyRandomImpl_first_run_miss coord state hcache]
  change (((fun value : Projection32Value =>
      (value, (state.1.cacheQuery coord value, state.2))) <$>
        ($ᵗ Projection32Value)) >>= fun result : Projection32Value × ProjectionCoordCache =>
          (simulateQ projectionCoordLazyRandomImpl (rest result.1)).run result.2) = _
  rw [bind_map_left]

private lemma run_simulateQ_projectionCoordLazyRandom_nonce_bind_hit
    {beta : Type} (coord : Coord12)
    (rest : Projection12Value → OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionCoordCache) (value : Projection12Value)
    (hcache : state.2 coord = some value) :
    (simulateQ projectionCoordLazyRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) >>= rest)).run state =
        (simulateQ projectionCoordLazyRandomImpl (rest value)).run state := by
  rw [run_simulateQ_projectionCoordLazyRandom_query_bind,
    projectionCoordLazyRandomImpl_nonce_run_hit coord state value hcache]
  change (pure (value, state) >>= fun result : Projection12Value × ProjectionCoordCache =>
    (simulateQ projectionCoordLazyRandomImpl (rest result.1)).run result.2) = _
  rw [pure_bind]

private lemma run_simulateQ_projectionCoordLazyRandom_nonce_bind_miss
    {beta : Type} (coord : Coord12)
    (rest : Projection12Value → OracleComp ProjectionCoordChallengeSpec beta)
    (state : ProjectionCoordCache) (hcache : state.2 coord = none) :
    (simulateQ projectionCoordLazyRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) >>= rest)).run state =
        ($ᵗ Projection12Value) >>= fun value =>
          (simulateQ projectionCoordLazyRandomImpl (rest value)).run
            (state.1, state.2.cacheQuery coord value) := by
  rw [run_simulateQ_projectionCoordLazyRandom_query_bind,
    projectionCoordLazyRandomImpl_nonce_run_miss coord state hcache]
  change (((fun value : Projection12Value =>
      (value, (state.1, state.2.cacheQuery coord value))) <$>
        ($ᵗ Projection12Value)) >>= fun result : Projection12Value × ProjectionCoordCache =>
          (simulateQ projectionCoordLazyRandomImpl (rest result.1)).run result.2) = _
  rw [bind_map_left]

/-- Predicate-aware cache-collision induction for 32-byte coordinates.

Uniform-adversary calls and nonce-coordinate calls may affect control flow and the nonce cache,
but they do not consume the 32-byte birthday budget. -/
private lemma probEvent_projectionCacheBad32_run_le_sum_aux
    {beta : Type}
    (computation : OracleComp ProjectionCoordChallengeSpec beta)
    (m k : ℕ)
    (hbound : computation.IsQueryBoundP IsProjection32Query m)
    (state₀ : ProjectionCoordCache)
    (hnocoll : ¬ProjectionCacheBad32 state₀)
    (hkeys : ∃ keys : Finset Coord32, keys.card ≤ k ∧
      ∀ coord, state₀.1 coord ≠ none → coord ∈ keys) :
    Pr[fun result => ProjectionCacheBad32 result.2 |
        (simulateQ projectionCoordLazyRandomImpl computation).run state₀] ≤
      ∑ j ∈ Finset.range m, ((k + j : ℕ) : ℝ≥0∞) *
        (Fintype.card Projection32Value : ℝ≥0∞)⁻¹ := by
  let cardinality := (Fintype.card Projection32Value : ℝ≥0∞)
  induction computation using OracleComp.inductionOn generalizing m k state₀ with
  | pure output =>
      rw [simulateQ_pure]
      refine le_of_eq_of_le (probEvent_eq_zero fun result hresult hbad => ?_) zero_le
      change result ∈ support (pure (output, state₀) : ProbComp _) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hnocoll hbad
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rcases query with randomQuery | coordinateQuery
      · rw [run_simulateQ_projectionCoordLazyRandom_uniform_bind]
        refine probEvent_bind_le_of_forall_le fun value _ => ?_
        have hrest := hbound.2 value
        simp only [IsProjection32Query, if_false] at hrest
        exact ih value m k hrest state₀ hnocoll hkeys
      · rcases coordinateQuery with coord | nonceCoord
        · have hmpos : 0 < m := hbound.1.resolve_left (by
            simp [IsProjection32Query])
          by_cases hhit : ∃ value, state₀.1 coord = some value
          · obtain ⟨value, hvalue⟩ := hhit
            rw [run_simulateQ_projectionCoordLazyRandom_first_bind_hit
              coord rest state₀ value hvalue]
            calc
              Pr[fun result => ProjectionCacheBad32 result.2 |
                  (simulateQ projectionCoordLazyRandomImpl (rest value)).run state₀]
                  ≤ ∑ j ∈ Finset.range (m - 1),
                      ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := by
                    apply ih value (m - 1) k
                    · simpa [IsProjection32Query] using hbound.2 value
                    · exact hnocoll
                    · exact hkeys
              _ ≤ ∑ j ∈ Finset.range m,
                    ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ :=
                Finset.sum_le_sum_of_subset
                  (Finset.range_mono (Nat.sub_le m 1))
          · push Not at hhit
            have hnone : state₀.1 coord = none :=
              Option.eq_none_iff_forall_ne_some.mpr hhit
            rw [run_simulateQ_projectionCoordLazyRandom_first_bind_miss
              coord rest state₀ hnone]
            have himmediate :
                Pr[fun value => CacheHasCollision (state₀.1.cacheQuery coord value) |
                    ($ᵗ Projection32Value)] ≤
                  (k : ℝ≥0∞) * cardinality⁻¹ := by
              classical
              obtain ⟨keys, hcard, hmem⟩ := hkeys
              rw [probEvent_uniformSample]
              have hbadCard :=
                (card_cacheQuery_collision_le_support
                  (spec := Projection32RO) (query := coord)
                  (supportKeys := keys) hnocoll hmem).trans hcard
              calc
                ((Finset.univ.filter
                    (fun value => CacheHasCollision
                      (state₀.1.cacheQuery coord value))).card : ℝ≥0∞) /
                    (Fintype.card Projection32Value : ℝ≥0∞)
                    ≤ (k : ℝ≥0∞) /
                        (Fintype.card Projection32Value : ℝ≥0∞) :=
                      ENNReal.div_le_div_right (by exact_mod_cast hbadCard) _
                _ = (k : ℝ≥0∞) * cardinality⁻¹ := by
                  rw [ENNReal.div_eq_inv_mul, mul_comm]
            have hcontinuation : ∀ value ∈ support ($ᵗ Projection32Value),
                ¬CacheHasCollision (state₀.1.cacheQuery coord value) →
                Pr[fun result => ProjectionCacheBad32 result.2 |
                    (simulateQ projectionCoordLazyRandomImpl (rest value)).run
                      (state₀.1.cacheQuery coord value, state₀.2)] ≤
                  ∑ j ∈ Finset.range (m - 1),
                    ((k + 1 + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := by
              intro value _ hnocoll'
              apply ih value (m - 1) (k + 1)
              · simpa [IsProjection32Query] using hbound.2 value
              · exact hnocoll'
              · obtain ⟨keys, hcard, hmem⟩ := hkeys
                exact ⟨insert coord keys,
                  le_trans (Finset.card_insert_le coord keys) (by omega),
                  fun other hother => by
                    by_cases heq : other = coord
                    · exact heq ▸ Finset.mem_insert_self _ keys
                    · change state₀.1.cacheQuery coord value other ≠ none at hother
                      rw [QueryCache.cacheQuery_of_ne state₀.1 _ heq] at hother
                      exact Finset.mem_insert_of_mem (hmem other hother)⟩
            have hcombine := probEvent_bind_le_add
              (mx := ($ᵗ Projection32Value))
              (my := fun value =>
                (simulateQ projectionCoordLazyRandomImpl (rest value)).run
                  (state₀.1.cacheQuery coord value, state₀.2))
              (p := fun value =>
                ¬CacheHasCollision (state₀.1.cacheQuery coord value))
              (q := fun result => ¬ProjectionCacheBad32 result.2)
              (ε₁ := (k : ℝ≥0∞) * cardinality⁻¹)
              (ε₂ := ∑ j ∈ Finset.range (m - 1),
                ((k + 1 + j : ℕ) : ℝ≥0∞) * cardinality⁻¹)
              (by simpa [not_not] using himmediate)
              (by simpa [not_not] using hcontinuation)
            simp only [not_not] at hcombine
            calc
              Pr[fun result => ProjectionCacheBad32 result.2 |
                  ($ᵗ Projection32Value) >>= fun value =>
                    (simulateQ projectionCoordLazyRandomImpl (rest value)).run
                      (state₀.1.cacheQuery coord value, state₀.2)]
                  ≤ (k : ℝ≥0∞) * cardinality⁻¹ +
                    ∑ j ∈ Finset.range (m - 1),
                      ((k + 1 + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := hcombine
              _ = ∑ j ∈ Finset.range m,
                    ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := by
                conv_rhs => rw [show m = (m - 1) + 1 by omega]
                rw [Finset.sum_range_succ'
                  (fun j => ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹)]
                simp only [Nat.add_zero]
                rw [add_comm, Finset.sum_congr rfl fun j _ => by
                  rw [show k + 1 + j = k + (j + 1) by omega]]
        · by_cases hhit : ∃ value, state₀.2 nonceCoord = some value
          · obtain ⟨value, hvalue⟩ := hhit
            rw [run_simulateQ_projectionCoordLazyRandom_nonce_bind_hit
              nonceCoord rest state₀ value hvalue]
            have hrest := hbound.2 value
            simp only [IsProjection32Query, if_false] at hrest
            exact ih value m k hrest state₀ hnocoll hkeys
          · push Not at hhit
            have hnone : state₀.2 nonceCoord = none :=
              Option.eq_none_iff_forall_ne_some.mpr hhit
            rw [run_simulateQ_projectionCoordLazyRandom_nonce_bind_miss
              nonceCoord rest state₀ hnone]
            refine probEvent_bind_le_of_forall_le fun value _ => ?_
            have hrest := hbound.2 value
            simp only [IsProjection32Query, if_false] at hrest
            exact ih value m k hrest
              (state₀.1, state₀.2.cacheQuery nonceCoord value) hnocoll hkeys

/-- Predicate-aware cache-collision induction for nonce coordinates.

Uniform-adversary calls and 32-byte-coordinate calls may affect control flow and the 32-byte
cache, but they do not consume the nonce birthday budget. -/
private lemma probEvent_projectionCacheBad12_run_le_sum_aux
    {beta : Type}
    (computation : OracleComp ProjectionCoordChallengeSpec beta)
    (m k : ℕ)
    (hbound : computation.IsQueryBoundP IsProjectionNonceQuery m)
    (state₀ : ProjectionCoordCache)
    (hnocoll : ¬ProjectionCacheBad12 state₀)
    (hkeys : ∃ keys : Finset Coord12, keys.card ≤ k ∧
      ∀ coord, state₀.2 coord ≠ none → coord ∈ keys) :
    Pr[fun result => ProjectionCacheBad12 result.2 |
        (simulateQ projectionCoordLazyRandomImpl computation).run state₀] ≤
      ∑ j ∈ Finset.range m, ((k + j : ℕ) : ℝ≥0∞) *
        (Fintype.card Projection12Value : ℝ≥0∞)⁻¹ := by
  let cardinality := (Fintype.card Projection12Value : ℝ≥0∞)
  induction computation using OracleComp.inductionOn generalizing m k state₀ with
  | pure output =>
      rw [simulateQ_pure]
      refine le_of_eq_of_le (probEvent_eq_zero fun result hresult hbad => ?_) zero_le
      change result ∈ support (pure (output, state₀) : ProbComp _) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hnocoll hbad
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rcases query with randomQuery | coordinateQuery
      · rw [run_simulateQ_projectionCoordLazyRandom_uniform_bind]
        refine probEvent_bind_le_of_forall_le fun value _ => ?_
        have hrest := hbound.2 value
        simp only [IsProjectionNonceQuery, if_false] at hrest
        exact ih value m k hrest state₀ hnocoll hkeys
      · rcases coordinateQuery with coord | nonceCoord
        · by_cases hhit : ∃ value, state₀.1 coord = some value
          · obtain ⟨value, hvalue⟩ := hhit
            rw [run_simulateQ_projectionCoordLazyRandom_first_bind_hit
              coord rest state₀ value hvalue]
            have hrest := hbound.2 value
            simp only [IsProjectionNonceQuery, if_false] at hrest
            exact ih value m k hrest state₀ hnocoll hkeys
          · push Not at hhit
            have hnone : state₀.1 coord = none :=
              Option.eq_none_iff_forall_ne_some.mpr hhit
            rw [run_simulateQ_projectionCoordLazyRandom_first_bind_miss
              coord rest state₀ hnone]
            refine probEvent_bind_le_of_forall_le fun value _ => ?_
            have hrest := hbound.2 value
            simp only [IsProjectionNonceQuery, if_false] at hrest
            exact ih value m k hrest
              (state₀.1.cacheQuery coord value, state₀.2) hnocoll hkeys
        · have hmpos : 0 < m := hbound.1.resolve_left (by
            simp [IsProjectionNonceQuery])
          by_cases hhit : ∃ value, state₀.2 nonceCoord = some value
          · obtain ⟨value, hvalue⟩ := hhit
            rw [run_simulateQ_projectionCoordLazyRandom_nonce_bind_hit
              nonceCoord rest state₀ value hvalue]
            calc
              Pr[fun result => ProjectionCacheBad12 result.2 |
                  (simulateQ projectionCoordLazyRandomImpl (rest value)).run state₀]
                  ≤ ∑ j ∈ Finset.range (m - 1),
                      ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := by
                    apply ih value (m - 1) k
                    · simpa [IsProjectionNonceQuery] using hbound.2 value
                    · exact hnocoll
                    · exact hkeys
              _ ≤ ∑ j ∈ Finset.range m,
                    ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ :=
                Finset.sum_le_sum_of_subset
                  (Finset.range_mono (Nat.sub_le m 1))
          · push Not at hhit
            have hnone : state₀.2 nonceCoord = none :=
              Option.eq_none_iff_forall_ne_some.mpr hhit
            rw [run_simulateQ_projectionCoordLazyRandom_nonce_bind_miss
              nonceCoord rest state₀ hnone]
            have himmediate :
                Pr[fun value => CacheHasCollision
                    (state₀.2.cacheQuery nonceCoord value) |
                    ($ᵗ Projection12Value)] ≤
                  (k : ℝ≥0∞) * cardinality⁻¹ := by
              classical
              obtain ⟨keys, hcard, hmem⟩ := hkeys
              rw [probEvent_uniformSample]
              have hbadCard :=
                (card_cacheQuery_collision_le_support
                  (spec := Projection12RO) (query := nonceCoord)
                  (supportKeys := keys) hnocoll hmem).trans hcard
              calc
                ((Finset.univ.filter
                    (fun value => CacheHasCollision
                      (state₀.2.cacheQuery nonceCoord value))).card : ℝ≥0∞) /
                    (Fintype.card Projection12Value : ℝ≥0∞)
                    ≤ (k : ℝ≥0∞) /
                        (Fintype.card Projection12Value : ℝ≥0∞) :=
                      ENNReal.div_le_div_right (by exact_mod_cast hbadCard) _
                _ = (k : ℝ≥0∞) * cardinality⁻¹ := by
                  rw [ENNReal.div_eq_inv_mul, mul_comm]
            have hcontinuation : ∀ value ∈ support ($ᵗ Projection12Value),
                ¬CacheHasCollision (state₀.2.cacheQuery nonceCoord value) →
                Pr[fun result => ProjectionCacheBad12 result.2 |
                    (simulateQ projectionCoordLazyRandomImpl (rest value)).run
                      (state₀.1, state₀.2.cacheQuery nonceCoord value)] ≤
                  ∑ j ∈ Finset.range (m - 1),
                    ((k + 1 + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := by
              intro value _ hnocoll'
              apply ih value (m - 1) (k + 1)
              · simpa [IsProjectionNonceQuery] using hbound.2 value
              · exact hnocoll'
              · obtain ⟨keys, hcard, hmem⟩ := hkeys
                exact ⟨insert nonceCoord keys,
                  le_trans (Finset.card_insert_le nonceCoord keys) (by omega),
                  fun other hother => by
                    by_cases heq : other = nonceCoord
                    · exact heq ▸ Finset.mem_insert_self _ keys
                    · change state₀.2.cacheQuery nonceCoord value other ≠ none at hother
                      rw [QueryCache.cacheQuery_of_ne state₀.2 _ heq] at hother
                      exact Finset.mem_insert_of_mem (hmem other hother)⟩
            have hcombine := probEvent_bind_le_add
              (mx := ($ᵗ Projection12Value))
              (my := fun value =>
                (simulateQ projectionCoordLazyRandomImpl (rest value)).run
                  (state₀.1, state₀.2.cacheQuery nonceCoord value))
              (p := fun value =>
                ¬CacheHasCollision (state₀.2.cacheQuery nonceCoord value))
              (q := fun result => ¬ProjectionCacheBad12 result.2)
              (ε₁ := (k : ℝ≥0∞) * cardinality⁻¹)
              (ε₂ := ∑ j ∈ Finset.range (m - 1),
                ((k + 1 + j : ℕ) : ℝ≥0∞) * cardinality⁻¹)
              (by simpa [not_not] using himmediate)
              (by simpa [not_not] using hcontinuation)
            simp only [not_not] at hcombine
            calc
              Pr[fun result => ProjectionCacheBad12 result.2 |
                  ($ᵗ Projection12Value) >>= fun value =>
                    (simulateQ projectionCoordLazyRandomImpl (rest value)).run
                      (state₀.1, state₀.2.cacheQuery nonceCoord value)]
                  ≤ (k : ℝ≥0∞) * cardinality⁻¹ +
                    ∑ j ∈ Finset.range (m - 1),
                      ((k + 1 + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := hcombine
              _ = ∑ j ∈ Finset.range m,
                    ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹ := by
                conv_rhs => rw [show m = (m - 1) + 1 by omega]
                rw [Finset.sum_range_succ'
                  (fun j => ((k + j : ℕ) : ℝ≥0∞) * cardinality⁻¹)]
                simp only [Nat.add_zero]
                rw [add_comm, Finset.sum_congr rfl fun j _ => by
                  rw [show k + 1 + j = k + (j + 1) by omega]]

/-- The selected-query Gaussian sum is exactly the unordered-pair count. -/
private lemma ennreal_sum_range_mul_inv_eq_choose (n : ℕ) (cardinality : ℝ≥0∞) :
    ∑ j ∈ Finset.range n, (j : ℝ≥0∞) * cardinality⁻¹ =
      (Nat.choose n 2 : ℝ≥0∞) / cardinality := by
  rw [← Finset.sum_mul, ENNReal.div_eq_inv_mul, mul_comm]
  congr 1
  have hchoose : ∑ j ∈ Finset.range n, j = Nat.choose n 2 := by
    rw [Nat.choose_two_right, Finset.sum_range_id]
  calc
    ∑ j ∈ Finset.range n, (j : ℝ≥0∞) =
        ((∑ j ∈ Finset.range n, j : ℕ) : ℝ≥0∞) := by simp
    _ = (Nat.choose n 2 : ℝ≥0∞) := by rw [hchoose]

/-- Tight birthday bound for the 32-byte cache using only logical 32-byte requests. -/
theorem probEvent_projectionCacheBad32_le_birthday
    {beta : Type} (computation : OracleComp ProjectionCoordChallengeSpec beta)
    (q32 : ℕ) (hbound : computation.IsQueryBoundP IsProjection32Query q32) :
    Pr[fun result => ProjectionCacheBad32 result.2 |
        (simulateQ projectionCoordLazyRandomImpl computation).run (∅, ∅)] ≤
      (Nat.choose q32 2 : ℝ≥0∞) /
        (Fintype.card Projection32Value : ℝ≥0∞) := by
  calc
    Pr[fun result => ProjectionCacheBad32 result.2 |
        (simulateQ projectionCoordLazyRandomImpl computation).run (∅, ∅)]
        ≤ ∑ j ∈ Finset.range q32, ((0 + j : ℕ) : ℝ≥0∞) *
            (Fintype.card Projection32Value : ℝ≥0∞)⁻¹ :=
          probEvent_projectionCacheBad32_run_le_sum_aux computation q32 0 hbound
            (∅, ∅)
            (by
              rintro ⟨left, right, leftValue, rightValue, hne, hleft, hright, hequal⟩
              simp at hleft)
            ⟨∅, by simp, fun coord hcoord => by
              exact absurd (by simp : (∅ : Projection32RO.QueryCache) coord = none) hcoord⟩
    _ = ∑ j ∈ Finset.range q32, (j : ℝ≥0∞) *
          (Fintype.card Projection32Value : ℝ≥0∞)⁻¹ := by simp
    _ = (Nat.choose q32 2 : ℝ≥0∞) /
          (Fintype.card Projection32Value : ℝ≥0∞) :=
      ennreal_sum_range_mul_inv_eq_choose q32 _

/-- Tight birthday bound for the nonce cache using only logical nonce requests. -/
theorem probEvent_projectionCacheBad12_le_birthday
    {beta : Type} (computation : OracleComp ProjectionCoordChallengeSpec beta)
    (q12 : ℕ) (hbound : computation.IsQueryBoundP IsProjectionNonceQuery q12) :
    Pr[fun result => ProjectionCacheBad12 result.2 |
        (simulateQ projectionCoordLazyRandomImpl computation).run (∅, ∅)] ≤
      (Nat.choose q12 2 : ℝ≥0∞) /
        (Fintype.card Projection12Value : ℝ≥0∞) := by
  calc
    Pr[fun result => ProjectionCacheBad12 result.2 |
        (simulateQ projectionCoordLazyRandomImpl computation).run (∅, ∅)]
        ≤ ∑ j ∈ Finset.range q12, ((0 + j : ℕ) : ℝ≥0∞) *
            (Fintype.card Projection12Value : ℝ≥0∞)⁻¹ :=
          probEvent_projectionCacheBad12_run_le_sum_aux computation q12 0 hbound
            (∅, ∅)
            (by
              rintro ⟨left, right, leftValue, rightValue, hne, hleft, hright, hequal⟩
              simp at hleft)
            ⟨∅, by simp, fun coord hcoord => by
              exact absurd (by simp : (∅ : Projection12RO.QueryCache) coord = none) hcoord⟩
    _ = ∑ j ∈ Finset.range q12, (j : ℝ≥0∞) *
          (Fintype.card Projection12Value : ℝ≥0∞)⁻¹ := by simp
    _ = (Nat.choose q12 2 : ℝ≥0∞) /
          (Fintype.card Projection12Value : ℝ≥0∞) :=
      ennreal_sum_range_mul_inv_eq_choose q12 _

/-- Exact source-accounted 32-byte collision bound in the normalized random world. -/
theorem sourceProjectionCacheBad32_random_le
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[fun result => ProjectionCacheBad32 result.2 |
        projectionCollisionRandomRun adversary] ≤
      (Nat.choose (sourceQ32 r i s pF pS) 2 : ℝ≥0∞) /
        (2 ^ 256 : ℝ≥0∞) := by
  unfold projectionCollisionRandomRun
  have hcard : (Fintype.card Projection32Value : ℝ≥0∞) =
      (2 ^ 256 : ℝ≥0∞) := by
    exact_mod_cast projection32Value_card
  rw [← hcard]
  exact probEvent_projectionCacheBad32_le_birthday
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main)
    (sourceQ32 r i s pF pS) adversary.coordinate32QueryBound

/-- Exact source-accounted nonce collision bound in the normalized random world. -/
theorem sourceProjectionCacheBad12_random_le
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[fun result => ProjectionCacheBad12 result.2 |
        projectionCollisionRandomRun adversary] ≤
      (Nat.choose (sourceQN s pN) 2 : ℝ≥0∞) /
        (2 ^ 96 : ℝ≥0∞) := by
  unfold projectionCollisionRandomRun
  have hcard : (Fintype.card Projection12Value : ℝ≥0∞) =
      (2 ^ 96 : ℝ≥0∞) := by
    exact_mod_cast projection12Value_card
  rw [← hcard]
  exact probEvent_projectionCacheBad12_le_birthday
    (simulateQ sourceKdfCoordinateForwardImpl adversary.main)
    (sourceQN s pN) adversary.coordinateNonceQueryBound

/-- The normalized random world pays the two width-specific birthday terms and nothing for
repeated identities or adversary-controlled uniform samples. -/
theorem sourceProjectionCollision_random_le
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[ProjectionCollisionEvent | projectionCollisionRandomRun adversary] ≤
      (Nat.choose (sourceQ32 r i s pF pS) 2 : ℝ≥0∞) /
          (2 ^ 256 : ℝ≥0∞) +
        (Nat.choose (sourceQN s pN) 2 : ℝ≥0∞) /
          (2 ^ 96 : ℝ≥0∞) := by
  exact (probEvent_or_le (projectionCollisionRandomRun adversary)
    (fun result => ProjectionCacheBad32 result.2)
    (fun result => ProjectionCacheBad12 result.2)).trans
      (add_le_add (sourceProjectionCacheBad32_random_le adversary)
        (sourceProjectionCacheBad12_random_le adversary))

/-! ## Exact complete-stream normalization -/

/-- Expand one complete-stream challenge query into the three canonical coordinate queries.

Adversary-controlled uniform queries remain transparent. A stream query eagerly reveals all
three independent coordinates, reconstructs the exact 76-byte answer, and performs no additional
randomness query. Later lemmas erase coordinates that the source call did not return.
-/
def jointKdfStreamEagerCoordinateForwardImpl :
    QueryImpl FixedHkdfSha512JointStreamSpec
      (OracleComp ProjectionCoordChallengeSpec)
  | .inl randomQuery =>
      liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery))
  | .inr address =>
      jointKdfStreamProjectionEquiv.symm <$> queryStepCoords address

/-- One cache over the sum of the two coordinate-oracle domains. The eager/deferred
normalization uses this cache so the generic dependent-range prefetch law applies only to the
coordinate oracle, never to adversary-controlled randomness. -/
abbrev ProjectionCoordUnifiedCache := ProjectionCoordSpec.QueryCache

/-- Fresh adversary randomness on the left and one unified lazy coordinate oracle on the right. -/
noncomputable def projectionCoordUnifiedRandomImpl :
    QueryImpl ProjectionCoordChallengeSpec
      (StateT ProjectionCoordUnifiedCache ProbComp) :=
  (uniformSampleImpl (spec := unifSpec)).liftTarget
      (StateT ProjectionCoordUnifiedCache ProbComp) +
    ProjectionCoordSpec.randomOracle

@[simp] theorem projectionCoordUnifiedRandomImpl_uniform_run
    (query : unifSpec.Domain) (cache : ProjectionCoordUnifiedCache) :
    (projectionCoordUnifiedRandomImpl (.inl query)).run cache =
      (fun value => (value, cache)) <$> uniformSampleImpl query := by
  rfl

@[simp] theorem projectionCoordUnifiedRandomImpl_coordinate_run
    (query : ProjectionCoordSpec.Domain) (cache : ProjectionCoordUnifiedCache) :
    (projectionCoordUnifiedRandomImpl (.inr query)).run cache =
      (ProjectionCoordSpec.randomOracle query).run cache := by
  rfl

theorem projectionCoordUnifiedRandomImpl_coordinate_run_hit
    (query : ProjectionCoordSpec.Domain) (cache : ProjectionCoordUnifiedCache)
    (value : ProjectionCoordSpec.Range query) (hcache : cache query = some value) :
    (projectionCoordUnifiedRandomImpl (.inr query)).run cache =
      pure (value, cache) := by
  rw [projectionCoordUnifiedRandomImpl_coordinate_run]
  unfold OracleSpec.randomOracle
  exact QueryImpl.withCaching_run_some uniformSampleImpl hcache

theorem projectionCoordUnifiedRandomImpl_coordinate_run_miss
    (query : ProjectionCoordSpec.Domain) (cache : ProjectionCoordUnifiedCache)
    (hcache : cache query = none) :
    (projectionCoordUnifiedRandomImpl (.inr query)).run cache =
      (fun value : ProjectionCoordSpec.Range query =>
        (value, cache.cacheQuery query value)) <$>
          ($ᵗ ProjectionCoordSpec.Range query) := by
  rw [projectionCoordUnifiedRandomImpl_coordinate_run]
  unfold OracleSpec.randomOracle
  exact QueryImpl.withCaching_run_none uniformSampleImpl hcache

/-- Split the unified sum-domain cache into the width-specific pair used by the birthday games. -/
def projectionCoordUnifiedCacheToPair
    (cache : ProjectionCoordUnifiedCache) : ProjectionCoordCache :=
  (fun coord => cache (.inl coord), fun coord => cache (.inr coord))

/-- Recombine the two width-specific caches into one sum-domain coordinate cache. -/
def projectionCoordPairCacheToUnified
    (cache : ProjectionCoordCache) : ProjectionCoordUnifiedCache
  | .inl coord => cache.1 coord
  | .inr coord => cache.2 coord

/-- The unified coordinate cache and the width-specific cache pair are exactly equivalent. -/
def projectionCoordCacheEquiv : ProjectionCoordUnifiedCache ≃ ProjectionCoordCache where
  toFun := projectionCoordUnifiedCacheToPair
  invFun := projectionCoordPairCacheToUnified
  left_inv cache := by
    funext query
    cases query <;> rfl
  right_inv cache := by
    apply Prod.ext <;> funext query <;> rfl

@[simp] theorem projectionCoordUnifiedCacheToPair_cacheQuery32
    (cache : ProjectionCoordUnifiedCache) (coord : Coord32)
    (value : Projection32Value) :
    projectionCoordUnifiedCacheToPair
        (cache.cacheQuery (.inl coord) value) =
      ((projectionCoordUnifiedCacheToPair cache).1.cacheQuery coord value,
        (projectionCoordUnifiedCacheToPair cache).2) := by
  apply Prod.ext
  · funext other
    by_cases heq : other = coord
    · subst other
      simp [projectionCoordUnifiedCacheToPair, QueryCache.cacheQuery]
    · simp [projectionCoordUnifiedCacheToPair, QueryCache.cacheQuery, heq]
  · funext other
    simp [projectionCoordUnifiedCacheToPair, QueryCache.cacheQuery]

@[simp] theorem projectionCoordUnifiedCacheToPair_cacheQuery12
    (cache : ProjectionCoordUnifiedCache) (coord : Coord12)
    (value : Projection12Value) :
    projectionCoordUnifiedCacheToPair
        (cache.cacheQuery (.inr coord) value) =
      ((projectionCoordUnifiedCacheToPair cache).1,
        (projectionCoordUnifiedCacheToPair cache).2.cacheQuery coord value) := by
  apply Prod.ext
  · funext other
    simp [projectionCoordUnifiedCacheToPair, QueryCache.cacheQuery]
  · funext other
    by_cases heq : other = coord
    · subst other
      simp [projectionCoordUnifiedCacheToPair, QueryCache.cacheQuery]
    · simp [projectionCoordUnifiedCacheToPair, QueryCache.cacheQuery, heq]

/-- Embed every cached complete stream into one unified entry for each canonical coordinate. -/
def jointKdfStreamCacheToUnifiedProjectionCoordCache
    (cache : JointKdfRO.QueryCache) : ProjectionCoordUnifiedCache
  | .inl coord => (cache coord.address).map coord.project
  | .inr address => (cache address).map (Coord12.project address)

@[simp] theorem jointKdfStreamCacheToUnifiedProjectionCoordCache_first
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) :
    jointKdfStreamCacheToUnifiedProjectionCoordCache cache
        (.inl (firstCoord address)) =
      (cache address).map (JointKdfProjection.first32.project) := by
  rfl

@[simp] theorem jointKdfStreamCacheToUnifiedProjectionCoordCache_second
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) :
    jointKdfStreamCacheToUnifiedProjectionCoordCache cache
        (.inl (secondCoord address)) =
      (cache address).map (JointKdfProjection.second32.project) := by
  rfl

@[simp] theorem jointKdfStreamCacheToUnifiedProjectionCoordCache_nonce
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) :
    jointKdfStreamCacheToUnifiedProjectionCoordCache cache (.inr address) =
      (cache address).map (JointKdfProjection.final12.project) := by
  rfl

/-- Project a complete-stream cache into the three coordinate caches. This embedding includes
latent coordinates and is used only for the eager intermediate game. -/
def jointKdfStreamCacheToProjectionCoordCache
    (cache : JointKdfRO.QueryCache) : ProjectionCoordCache :=
  projectionCoordUnifiedCacheToPair
    (jointKdfStreamCacheToUnifiedProjectionCoordCache cache)

theorem jointKdfStreamCache_unified_to_pair
    (cache : JointKdfRO.QueryCache) :
    projectionCoordUnifiedCacheToPair
        (jointKdfStreamCacheToUnifiedProjectionCoordCache cache) =
      jointKdfStreamCacheToProjectionCoordCache cache := by
  rfl

@[simp] theorem jointKdfStreamCacheToProjectionCoordCache_empty :
    jointKdfStreamCacheToProjectionCoordCache (∅ : JointKdfRO.QueryCache) =
      (∅, ∅) := by
  rfl

@[simp] theorem jointKdfStreamCacheToProjectionCoordCache_first
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) :
    (jointKdfStreamCacheToProjectionCoordCache cache).1 (firstCoord address) =
      (cache address).map (JointKdfProjection.first32.project) := by
  rfl

@[simp] theorem jointKdfStreamCacheToProjectionCoordCache_second
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) :
    (jointKdfStreamCacheToProjectionCoordCache cache).1 (secondCoord address) =
      (cache address).map (JointKdfProjection.second32.project) := by
  rfl

@[simp] theorem jointKdfStreamCacheToProjectionCoordCache_nonce
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) :
    (jointKdfStreamCacheToProjectionCoordCache cache).2 address =
      (cache address).map (JointKdfProjection.final12.project) := by
  rfl

theorem jointKdfStreamCacheToProjectionCoordCache_first_of_hit
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    (jointKdfStreamCacheToProjectionCoordCache cache).1 (firstCoord address) =
      some (JointKdfProjection.first32.project stream) := by
  simp [hcache]

theorem jointKdfStreamCacheToProjectionCoordCache_second_of_hit
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    (jointKdfStreamCacheToProjectionCoordCache cache).1 (secondCoord address) =
      some (JointKdfProjection.second32.project stream) := by
  simp [hcache]

theorem jointKdfStreamCacheToProjectionCoordCache_nonce_of_hit
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    (jointKdfStreamCacheToProjectionCoordCache cache).2 address =
      some (JointKdfProjection.final12.project stream) := by
  simp [hcache]

theorem jointKdfStreamCacheToProjectionCoordCache_first_of_miss
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (hcache : cache address = none) :
      (jointKdfStreamCacheToProjectionCoordCache cache).1 (firstCoord address) = none := by
  change (cache address).map _ = (none : Option Projection32Value)
  rw [hcache]
  rfl

theorem jointKdfStreamCacheToProjectionCoordCache_second_of_miss
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (hcache : cache address = none) :
      (jointKdfStreamCacheToProjectionCoordCache cache).1 (secondCoord address) = none := by
  change (cache address).map _ = (none : Option Projection32Value)
  rw [hcache]
  rfl

theorem jointKdfStreamCacheToProjectionCoordCache_nonce_of_miss
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (hcache : cache address = none) :
    (jointKdfStreamCacheToProjectionCoordCache cache).2 address = none := by
  change (cache address).map _ = (none : Option Projection12Value)
  rw [hcache]
  rfl

/-- Installing one complete stream corresponds exactly to installing its three split
coordinates in the eager intermediate cache. -/
theorem jointKdfStreamCacheToProjectionCoordCache_cacheQuery
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (stream : JointKdfStream) :
    jointKdfStreamCacheToProjectionCoordCache
        (cache.cacheQuery address stream) =
      (((jointKdfStreamCacheToProjectionCoordCache cache).1.cacheQuery
          (firstCoord address) (JointKdfProjection.first32.project stream)).cacheQuery
          (secondCoord address) (JointKdfProjection.second32.project stream),
        (jointKdfStreamCacheToProjectionCoordCache cache).2.cacheQuery address
          (JointKdfProjection.final12.project stream)) := by
  apply Prod.ext
  · funext coord
    rcases coord with ⟨other, slot⟩
    by_cases haddress : other = address
    · subst other
      cases slot <;>
        simp [jointKdfStreamCacheToProjectionCoordCache,
          projectionCoordUnifiedCacheToPair,
          jointKdfStreamCacheToUnifiedProjectionCoordCache,
          QueryCache.cacheQuery, firstCoord, secondCoord, Coord32.project]
    · cases slot <;>
        simp [jointKdfStreamCacheToProjectionCoordCache,
          projectionCoordUnifiedCacheToPair,
          jointKdfStreamCacheToUnifiedProjectionCoordCache,
          QueryCache.cacheQuery, firstCoord, secondCoord, haddress]
  · funext other
    by_cases haddress : other = address
    · subst other
      simp [jointKdfStreamCacheToProjectionCoordCache,
        projectionCoordUnifiedCacheToPair,
        jointKdfStreamCacheToUnifiedProjectionCoordCache,
        QueryCache.cacheQuery, Coord12.project]
    · simp [jointKdfStreamCacheToProjectionCoordCache,
        projectionCoordUnifiedCacheToPair,
        jointKdfStreamCacheToUnifiedProjectionCoordCache,
        QueryCache.cacheQuery, haddress]

/-- The corresponding cache-update equation in the unified sum-domain representation. -/
theorem jointKdfStreamCacheToUnifiedProjectionCoordCache_cacheQuery
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (stream : JointKdfStream) :
    jointKdfStreamCacheToUnifiedProjectionCoordCache
        (cache.cacheQuery address stream) =
      (((jointKdfStreamCacheToUnifiedProjectionCoordCache cache).cacheQuery
          (.inl (firstCoord address))
          (JointKdfProjection.first32.project stream)).cacheQuery
          (.inl (secondCoord address))
          (JointKdfProjection.second32.project stream)).cacheQuery
          (.inr address) (JointKdfProjection.final12.project stream) := by
  apply projectionCoordCacheEquiv.injective
  simp only [projectionCoordCacheEquiv, Equiv.coe_fn_mk,
    projectionCoordUnifiedCacheToPair_cacheQuery32,
    projectionCoordUnifiedCacheToPair_cacheQuery12]
  exact jointKdfStreamCacheToProjectionCoordCache_cacheQuery cache address stream

/-- Structural query step for the transparent-uniform unified-coordinate handler. -/
private lemma run_simulateQ_projectionCoordUnifiedRandom_query_bind
    {beta : Type} (query : ProjectionCoordChallengeSpec.Domain)
    (rest : ProjectionCoordChallengeSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query query) >>= rest)).run cache =
        (projectionCoordUnifiedRandomImpl query).run cache >>= fun result =>
          (simulateQ projectionCoordUnifiedRandomImpl (rest result.1)).run result.2 := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  simp [OracleQuery.cont_query]

private lemma run_simulateQ_projectionCoordUnifiedRandom_uniform_bind
    {beta : Type} (query : unifSpec.Domain)
    (rest : unifSpec.Range query → OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inl query)) >>= rest)).run cache =
        uniformSampleImpl query >>= fun value =>
          (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run cache := by
  rw [run_simulateQ_projectionCoordUnifiedRandom_query_bind,
    projectionCoordUnifiedRandomImpl_uniform_run]
  change (((fun value : unifSpec.Range query => (value, cache)) <$>
      uniformSampleImpl query) >>= fun result :
        unifSpec.Range query × ProjectionCoordUnifiedCache =>
          (simulateQ projectionCoordUnifiedRandomImpl (rest result.1)).run result.2) = _
  rw [bind_map_left]

private lemma run'_simulateQ_projectionCoordUnifiedRandom_uniform_bind
    {beta : Type} (query : unifSpec.Domain)
    (rest : unifSpec.Range query → OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inl query)) >>= rest)).run' cache =
        uniformSampleImpl query >>= fun value =>
          (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run' cache := by
  rw [StateT.run'_eq, run_simulateQ_projectionCoordUnifiedRandom_uniform_bind, map_bind]
  rfl

private lemma run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
    {beta : Type} (query : ProjectionCoordSpec.Domain)
    (rest : ProjectionCoordSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache)
    (value : ProjectionCoordSpec.Range query) (hcache : cache query = some value) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr query)) >>= rest)).run cache =
        (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run cache := by
  rw [run_simulateQ_projectionCoordUnifiedRandom_query_bind,
    projectionCoordUnifiedRandomImpl_coordinate_run_hit query cache value hcache]
  change (pure (value, cache) >>= fun result :
      ProjectionCoordSpec.Range query × ProjectionCoordUnifiedCache =>
        (simulateQ projectionCoordUnifiedRandomImpl (rest result.1)).run result.2) = _
  rw [pure_bind]

private lemma run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
    {beta : Type} (query : ProjectionCoordSpec.Domain)
    (rest : ProjectionCoordSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache)
    (value : ProjectionCoordSpec.Range query) (hcache : cache query = some value) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr query)) >>= rest)).run' cache =
        (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run' cache := by
  rw [StateT.run'_eq,
    run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
      query rest cache value hcache]
  rw [StateT.run'_eq]

private lemma run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
    {beta : Type} (query : ProjectionCoordSpec.Domain)
    (rest : ProjectionCoordSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache) (hcache : cache query = none) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr query)) >>= rest)).run cache =
        ($ᵗ ProjectionCoordSpec.Range query) >>= fun value =>
          (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run
            (cache.cacheQuery query value) := by
  rw [run_simulateQ_projectionCoordUnifiedRandom_query_bind,
    projectionCoordUnifiedRandomImpl_coordinate_run_miss query cache hcache]
  change (((fun value : ProjectionCoordSpec.Range query =>
      (value, cache.cacheQuery query value)) <$>
        ($ᵗ ProjectionCoordSpec.Range query)) >>= fun result :
          ProjectionCoordSpec.Range query × ProjectionCoordUnifiedCache =>
            (simulateQ projectionCoordUnifiedRandomImpl (rest result.1)).run result.2) = _
  rw [bind_map_left]

private lemma run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
    {beta : Type} (query : ProjectionCoordSpec.Domain)
    (rest : ProjectionCoordSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec beta)
    (cache : ProjectionCoordUnifiedCache) (hcache : cache query = none) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr query)) >>= rest)).run' cache =
        ($ᵗ ProjectionCoordSpec.Range query) >>= fun value =>
          (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run'
            (cache.cacheQuery query value) := by
  rw [StateT.run'_eq,
    run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
      query rest cache hcache, map_bind]
  rfl

/-- A cached complete stream becomes three cache hits in the eager-coordinate game and
reconstructs exactly the cached 76-byte answer. -/
private lemma run_simulateQ_jointKdfStreamEagerCoordinateForwardImpl_hit
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (jointKdfStreamEagerCoordinateForwardImpl (.inr address))).run
        (jointKdfStreamCacheToUnifiedProjectionCoordCache cache) =
      pure (stream, jointKdfStreamCacheToUnifiedProjectionCoordCache cache) := by
  change (simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (firstCoord address))))
      let second ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (secondCoord address))))
      let nonce ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inr address)))
      pure (jointKdfStreamProjectionEquiv.symm (first, second, nonce)))).run
        (jointKdfStreamCacheToUnifiedProjectionCoordCache cache) = _
  have hfirst : jointKdfStreamCacheToUnifiedProjectionCoordCache cache
      (.inl (firstCoord address)) =
        some (JointKdfProjection.first32.project stream) := by
    simp [hcache]
  have hsecond : jointKdfStreamCacheToUnifiedProjectionCoordCache cache
      (.inl (secondCoord address)) =
        some (JointKdfProjection.second32.project stream) := by
    simp [hcache]
  have hnonce : jointKdfStreamCacheToUnifiedProjectionCoordCache cache
      (.inr address) = some (JointKdfProjection.final12.project stream) := by
    simp [hcache]
  rw [run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
    (.inl (firstCoord address)) _ _
      (JointKdfProjection.first32.project stream) hfirst]
  rw [run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
    (.inl (secondCoord address)) _ _
      (JointKdfProjection.second32.project stream) hsecond]
  rw [run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
    (.inr address) _ _ (JointKdfProjection.final12.project stream) hnonce]
  simp only [simulateQ_pure, StateT.run_pure]
  congr 2
  have hparts :
      (JointKdfProjection.first32.project stream,
        JointKdfProjection.second32.project stream,
        JointKdfProjection.final12.project stream) =
          jointKdfStreamProjectionEquiv stream := by
    apply Prod.ext
    · exact (jointKdfStreamProjectionEquiv_first stream).symm
    · apply Prod.ext
      · exact (jointKdfStreamProjectionEquiv_second stream).symm
      · exact (jointKdfStreamProjectionEquiv_nonce stream).symm
  exact (congrArg jointKdfStreamProjectionEquiv.symm hparts).trans
    (jointKdfStreamProjectionEquiv.symm_apply_apply stream)

/-- A fresh complete-stream address is exactly three independent coordinate samples, installed
under their canonical identities and reassembled into one 76-byte answer. -/
private lemma run_simulateQ_jointKdfStreamEagerCoordinateForwardImpl_miss
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (hcache : cache address = none) :
    (simulateQ projectionCoordUnifiedRandomImpl
      (jointKdfStreamEagerCoordinateForwardImpl (.inr address))).run
        (jointKdfStreamCacheToUnifiedProjectionCoordCache cache) = (do
      let first ← $ᵗ Projection32Value
      let second ← $ᵗ Projection32Value
      let nonce ← $ᵗ Projection12Value
      let stream : FixedHkdfSha512JointStreamSpec.Range (.inr address) :=
        jointKdfStreamProjectionEquiv.symm (first, second, nonce)
      pure (stream,
        jointKdfStreamCacheToUnifiedProjectionCoordCache
          (cache.cacheQuery address stream))) := by
  change (simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (firstCoord address))))
      let second ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (secondCoord address))))
      let nonce ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inr address)))
      pure (jointKdfStreamProjectionEquiv.symm (first, second, nonce)))).run
        (jointKdfStreamCacheToUnifiedProjectionCoordCache cache) = _
  let base := jointKdfStreamCacheToUnifiedProjectionCoordCache cache
  have hfirst : base (.inl (firstCoord address)) = none := by
    simp [base, hcache]
    rfl
  have hsecond : base (.inl (secondCoord address)) = none := by
    simp [base, hcache]
    rfl
  have hnonce : base (.inr address) = none := by
    simp [base, hcache]
    rfl
  rw [run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
    (.inl (firstCoord address)) _ base hfirst]
  congr 1
  funext first
  have hsecondAfterFirst :
      (base.cacheQuery (.inl (firstCoord address)) first)
          (.inl (secondCoord address)) = none := by
    rw [QueryCache.cacheQuery_of_ne]
    · exact hsecond
    · intro equality
      exact firstCoord_ne_secondCoord address (Sum.inl.inj equality).symm
  rw [run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
    (.inl (secondCoord address)) _ _ hsecondAfterFirst]
  congr 1
  funext second
  have hnonceAfter32 :
      ((base.cacheQuery (.inl (firstCoord address)) first).cacheQuery
          (.inl (secondCoord address)) second) (.inr address) = none := by
    rw [QueryCache.cacheQuery_of_ne]
    · rw [QueryCache.cacheQuery_of_ne]
      · exact hnonce
      · simp
    · simp
  rw [run_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
    (.inr address) _ _ hnonceAfter32]
  congr 1
  funext nonce
  simp only [simulateQ_pure, StateT.run_pure]
  congr 2
  rw [jointKdfStreamCacheToUnifiedProjectionCoordCache_cacheQuery]
  simp
  rfl

/-- The eager-coordinate miss has exactly the same output-and-cache distribution as one uniform
76-byte stream miss. -/
private lemma evalDist_run_jointKdfStreamEagerCoordinateForwardImpl_miss
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (hcache : cache address = none) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
      (jointKdfStreamEagerCoordinateForwardImpl (.inr address))).run
        (jointKdfStreamCacheToUnifiedProjectionCoordCache cache)) =
      evalDist ((fun stream : JointKdfStream =>
        ((show FixedHkdfSha512JointStreamSpec.Range (.inr address) from stream),
          jointKdfStreamCacheToUnifiedProjectionCoordCache
          (cache.cacheQuery address stream))) <$> ($ᵗ JointKdfStream)) := by
  rw [run_simulateQ_jointKdfStreamEagerCoordinateForwardImpl_miss address cache hcache]
  let outputOfParts :
      (Projection32Value × Projection32Value × Projection12Value) →
        (FixedHkdfSha512JointStreamSpec.Range (.inr address) ×
          ProjectionCoordUnifiedCache) :=
    fun parts : Projection32Value × Projection32Value × Projection12Value =>
      let stream : FixedHkdfSha512JointStreamSpec.Range (.inr address) :=
        jointKdfStreamProjectionEquiv.symm parts
      (stream, jointKdfStreamCacheToUnifiedProjectionCoordCache
        (cache.cacheQuery address stream))
  have hfactor := map_uniformSample_prod_prod_eq outputOfParts
  have hfactor' :
      (do
        let first ← $ᵗ Projection32Value
        let second ← $ᵗ Projection32Value
        let nonce ← $ᵗ Projection12Value
        let stream : FixedHkdfSha512JointStreamSpec.Range (.inr address) :=
          jointKdfStreamProjectionEquiv.symm (first, second, nonce)
        pure (stream, jointKdfStreamCacheToUnifiedProjectionCoordCache
          (cache.cacheQuery address stream))) = outputOfParts <$> (do
            let first ← $ᵗ Projection32Value
            let second ← $ᵗ Projection32Value
            let nonce ← $ᵗ Projection12Value
            pure (first, second, nonce)) := by
    simpa only [outputOfParts] using hfactor
  rw [hfactor', uniformSample_prod_prod_eq]
  have htransport := evalDist_map_eq_of_evalDist_eq
    evalDist_split_uniformJointKdfStream outputOfParts
  simpa only [Functor.map_map, Function.comp_apply, outputOfParts,
    Equiv.symm_apply_apply] using htransport.symm

/-- One full-stream random-oracle step, including its resulting cache, has exactly the eager
coordinate-step distribution after applying the complete-cache embedding. -/
private lemma evalDist_map_fixedJointStreamRandom_query_eq_eagerCoordinates
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (cache : JointKdfRO.QueryCache) :
    evalDist (Prod.map id jointKdfStreamCacheToUnifiedProjectionCoordCache <$>
        (fixedHkdfSha512JointStreamRandomImpl query).run cache) =
      evalDist (((projectionCoordUnifiedRandomImpl ∘ₛ
        jointKdfStreamEagerCoordinateForwardImpl) query).run
          (jointKdfStreamCacheToUnifiedProjectionCoordCache cache)) := by
  rcases query with randomQuery | address
  · simp [fixedHkdfSha512JointStreamRandomImpl,
      jointKdfStreamEagerCoordinateForwardImpl,
      projectionCoordUnifiedRandomImpl, QueryImpl.compose,
      Functor.map_map]
    exact (evalDist_uniformSample
      (α := unifSpec.Range randomQuery)).symm
  · cases hcache : cache address with
    | some stream =>
        unfold QueryImpl.compose
        change evalDist (Prod.map id jointKdfStreamCacheToUnifiedProjectionCoordCache <$>
            (jointKdfLazyRandomStreamImpl address).run cache) =
          evalDist ((simulateQ projectionCoordUnifiedRandomImpl
            (jointKdfStreamEagerCoordinateForwardImpl (.inr address))).run
              (jointKdfStreamCacheToUnifiedProjectionCoordCache cache))
        rw [jointKdfLazyRandomStreamImpl_run_hit address cache stream hcache,
          run_simulateQ_jointKdfStreamEagerCoordinateForwardImpl_hit
            address cache stream hcache]
        simp
    | none =>
        unfold QueryImpl.compose
        change evalDist (Prod.map id jointKdfStreamCacheToUnifiedProjectionCoordCache <$>
            (jointKdfLazyRandomStreamImpl address).run cache) =
          evalDist ((simulateQ projectionCoordUnifiedRandomImpl
            (jointKdfStreamEagerCoordinateForwardImpl (.inr address))).run
              (jointKdfStreamCacheToUnifiedProjectionCoordCache cache))
        rw [jointKdfLazyRandomStreamImpl_run_miss address cache hcache,
          Functor.map_map]
        exact (evalDist_run_jointKdfStreamEagerCoordinateForwardImpl_miss
          address cache hcache).symm

/-- Distributional state-map transport for an arbitrary stateful oracle simulation. Unlike the
pure state-projection theorem, this permits a per-query coupling that is exact only after
`evalDist`, which is required by the stream-splitting bijection. -/
private theorem evalDist_map_run_simulateQ_eq_of_query_map_evalDist_eq
    {iota sigma tau alpha : Type} {spec : OracleSpec.{0, 0} iota}
    (impl₁ : QueryImpl spec (StateT sigma ProbComp))
    (impl₂ : QueryImpl spec (StateT tau ProbComp))
    (stateMap : sigma → tau)
    (hquery : ∀ query state,
      evalDist (Prod.map id stateMap <$> (impl₁ query).run state) =
        evalDist ((impl₂ query).run (stateMap state)))
    (computation : OracleComp spec alpha) (state : sigma) :
    evalDist (Prod.map id stateMap <$>
        (simulateQ impl₁ computation).run state) =
      evalDist ((simulateQ impl₂ computation).run (stateMap state)) := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure output => simp
  | query_bind query rest ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run_bind, id_map, map_bind]
      calc
        evalDist ((impl₁ query).run state >>= fun result =>
            Prod.map id stateMap <$>
              (simulateQ impl₁ (rest result.1)).run result.2) =
          evalDist ((impl₁ query).run state >>= fun result =>
            (simulateQ impl₂ (rest result.1)).run (stateMap result.2)) := by
              apply evalDist_bind_congr'
              intro result
              exact ih result.1 result.2
        _ = evalDist ((Prod.map id stateMap <$> (impl₁ query).run state) >>=
            fun result =>
              (simulateQ impl₂ (rest result.1)).run result.2) := by
                rw [bind_map_left]
                rfl
        _ = evalDist ((impl₂ query).run (stateMap state) >>= fun result =>
            (simulateQ impl₂ (rest result.1)).run result.2) := by
              rw [evalDist_bind, evalDist_bind, hquery query state]

open Classical in
/-- Replacing the complete-stream lazy random oracle by eager independent coordinates preserves
the output distribution of every adaptive computation. Final caches are deliberately discarded. -/
theorem evalDist_fixedJointStreamRandom_eq_eagerCoordinates
    {alpha : Type}
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha)
    (cache : JointKdfRO.QueryCache) :
    evalDist ((simulateQ fixedHkdfSha512JointStreamRandomImpl computation).run' cache) =
      evalDist ((simulateQ
        (projectionCoordUnifiedRandomImpl ∘ₛ jointKdfStreamEagerCoordinateForwardImpl)
        computation).run'
          (jointKdfStreamCacheToUnifiedProjectionCoordCache cache)) := by
  have hrun := evalDist_map_run_simulateQ_eq_of_query_map_evalDist_eq
    fixedHkdfSha512JointStreamRandomImpl
    (projectionCoordUnifiedRandomImpl ∘ₛ jointKdfStreamEagerCoordinateForwardImpl)
    jointKdfStreamCacheToUnifiedProjectionCoordCache
    evalDist_map_fixedJointStreamRandom_query_eq_eagerCoordinates
    computation cache
  have hout := evalDist_map_eq_of_evalDist_eq hrun Prod.fst
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_apply,
    Prod.map] using hout

open Classical in
/-- A fresh coordinate may be sampled and cached before any adaptive computation while
adversary-controlled uniform queries remain fresh and leave the coordinate cache untouched. -/
theorem evalDist_projectionCoordUnifiedRandom_eq_uniform_prefill
    {alpha : Type} (target : ProjectionCoordSpec.Domain)
    (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) (hcache : cache target = none) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl computation).run' cache) =
      evalDist (($ᵗ ProjectionCoordSpec.Range target) >>= fun value =>
        (simulateQ projectionCoordUnifiedRandomImpl computation).run'
          (cache.cacheQuery target value)) := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure output =>
      letI : DecidableEq alpha := Classical.decEq alpha
      apply evalDist_ext
      intro candidate
      simp
  | query_bind query rest ih =>
      rcases query with randomQuery | coordinateQuery
      · change (unifSpec.Range randomQuery →
          OracleComp ProjectionCoordChallengeSpec alpha) at rest
        rw [run'_simulateQ_projectionCoordUnifiedRandom_uniform_bind
          randomQuery rest cache]
        simp_rw [run'_simulateQ_projectionCoordUnifiedRandom_uniform_bind
          randomQuery rest]
        calc
          evalDist (do
              let response ← uniformSampleImpl randomQuery
              (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run' cache) =
            evalDist (do
              let response ← uniformSampleImpl randomQuery
              let targetValue ← $ᵗ ProjectionCoordSpec.Range target
              (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                (cache.cacheQuery target targetValue)) := by
              apply OracleComp.DeferredSampling.evalDist_bind_congr_left
              intro response
              exact ih response cache hcache
          _ = evalDist (do
              let targetValue ← $ᵗ ProjectionCoordSpec.Range target
              let response ← uniformSampleImpl randomQuery
              (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                (cache.cacheQuery target targetValue)) :=
            OracleComp.DeferredSampling.evalDist_bind_comm
              (uniformSampleImpl randomQuery)
              ($ᵗ ProjectionCoordSpec.Range target)
              fun response targetValue =>
                (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                  (cache.cacheQuery target targetValue)
      · change (ProjectionCoordSpec.Range coordinateQuery →
          OracleComp ProjectionCoordChallengeSpec alpha) at rest
        cases hquery : cache coordinateQuery with
        | some response =>
            have hne : coordinateQuery ≠ target := by
              intro heq
              subst coordinateQuery
              rw [hcache] at hquery
              contradiction
            have hstepPrefill (targetValue : ProjectionCoordSpec.Range target) :
                (simulateQ projectionCoordUnifiedRandomImpl
                  (liftM (ProjectionCoordChallengeSpec.query (.inr coordinateQuery)) >>=
                    rest)).run' (cache.cacheQuery target targetValue) =
                  (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                    (cache.cacheQuery target targetValue) := by
              have hcached :
                  (cache.cacheQuery target targetValue) coordinateQuery = some response := by
                rw [QueryCache.cacheQuery_of_ne cache targetValue hne]
                exact hquery
              exact run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
                coordinateQuery rest _ response hcached
            rw [run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
              coordinateQuery rest cache response hquery]
            simp_rw [hstepPrefill]
            exact ih response cache hcache
        | none =>
            by_cases heq : coordinateQuery = target
            · subst coordinateQuery
              have hstepPrefill (value : ProjectionCoordSpec.Range target) :
                  (simulateQ projectionCoordUnifiedRandomImpl
                    (liftM (ProjectionCoordChallengeSpec.query (.inr target)) >>=
                      rest)).run' (cache.cacheQuery target value) =
                    (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run'
                      (cache.cacheQuery target value) :=
                run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_hit
                  target rest _ value (QueryCache.cacheQuery_self cache target value)
              rw [run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
                target rest cache hcache]
              simp_rw [hstepPrefill]
            · have hstepPrefill (targetValue : ProjectionCoordSpec.Range target) :
                  (simulateQ projectionCoordUnifiedRandomImpl
                    (liftM (ProjectionCoordChallengeSpec.query (.inr coordinateQuery)) >>=
                      rest)).run' (cache.cacheQuery target targetValue) =
                    ($ᵗ ProjectionCoordSpec.Range coordinateQuery) >>= fun value =>
                      (simulateQ projectionCoordUnifiedRandomImpl (rest value)).run'
                        ((cache.cacheQuery target targetValue).cacheQuery
                          coordinateQuery value) := by
                have hnone :
                    (cache.cacheQuery target targetValue) coordinateQuery = none := by
                  rw [QueryCache.cacheQuery_of_ne cache targetValue heq]
                  exact hquery
                exact run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
                  coordinateQuery rest _ hnone
              rw [run'_simulateQ_projectionCoordUnifiedRandom_coordinate_bind_miss
                coordinateQuery rest cache hquery]
              simp_rw [hstepPrefill]
              calc
                evalDist (do
                    let response ← $ᵗ ProjectionCoordSpec.Range coordinateQuery
                    (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                      (cache.cacheQuery coordinateQuery response)) =
                  evalDist (do
                    let response ← $ᵗ ProjectionCoordSpec.Range coordinateQuery
                    let targetValue ← $ᵗ ProjectionCoordSpec.Range target
                    (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                      ((cache.cacheQuery coordinateQuery response).cacheQuery
                        target targetValue)) := by
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro response
                  apply ih response
                  rw [QueryCache.cacheQuery_of_ne cache response (Ne.symm heq)]
                  exact hcache
                _ = evalDist (do
                    let targetValue ← $ᵗ ProjectionCoordSpec.Range target
                    let response ← $ᵗ ProjectionCoordSpec.Range coordinateQuery
                    (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                      ((cache.cacheQuery coordinateQuery response).cacheQuery
                        target targetValue)) :=
                  OracleComp.DeferredSampling.evalDist_bind_comm
                    ($ᵗ ProjectionCoordSpec.Range coordinateQuery)
                    ($ᵗ ProjectionCoordSpec.Range target)
                    fun response targetValue =>
                      (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                        ((cache.cacheQuery coordinateQuery response).cacheQuery
                          target targetValue)
                _ = evalDist (do
                    let targetValue ← $ᵗ ProjectionCoordSpec.Range target
                    let response ← $ᵗ ProjectionCoordSpec.Range coordinateQuery
                    (simulateQ projectionCoordUnifiedRandomImpl (rest response)).run'
                      ((cache.cacheQuery target targetValue).cacheQuery
                        coordinateQuery response)) := by
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro targetValue
                  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
                  intro response
                  rw [dependentQueryCache_cacheQuery_comm cache coordinateQuery target
                    response targetValue heq]

open Classical in
/-- Querying and ignoring one coordinate is output-law inert even across intervening fresh
adversary randomness and an adaptive later reveal of that coordinate. -/
theorem evalDist_projectionCoordUnifiedRandom_prefetch_irrelevant
    {alpha : Type} (target : ProjectionCoordSpec.Domain)
    (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((projectionCoordUnifiedRandomImpl (.inr target) >>= fun _ =>
          simulateQ projectionCoordUnifiedRandomImpl computation).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl computation).run' cache) := by
  change evalDist (((projectionCoordUnifiedRandomImpl (.inr target) :
      StateT ProjectionCoordUnifiedCache ProbComp
        (ProjectionCoordSpec.Range target)) >>= fun _ =>
        simulateQ projectionCoordUnifiedRandomImpl computation).run' cache) = _
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  cases hcache : cache target with
  | some value =>
      rw [projectionCoordUnifiedRandomImpl_coordinate_run_hit target cache value hcache]
      simp
  | none =>
      rw [projectionCoordUnifiedRandomImpl_coordinate_run_miss target cache hcache]
      change evalDist ((((fun value : ProjectionCoordSpec.Range target =>
          (value, cache.cacheQuery target value)) <$>
            ($ᵗ ProjectionCoordSpec.Range target)) >>= fun result :
              ProjectionCoordSpec.Range target × ProjectionCoordUnifiedCache =>
                (fun x => x.1) <$>
                  (simulateQ projectionCoordUnifiedRandomImpl computation).run result.2)) = _
      rw [bind_map_left]
      change evalDist (do
          let value ← $ᵗ ProjectionCoordSpec.Range target
          (simulateQ projectionCoordUnifiedRandomImpl computation).run'
            (cache.cacheQuery target value)) =
        evalDist ((simulateQ projectionCoordUnifiedRandomImpl computation).run' cache)
      exact (evalDist_projectionCoordUnifiedRandom_eq_uniform_prefill
        target computation cache hcache).symm

/-- Oracle-computation form of ignored-coordinate prefetch erasure. -/
theorem evalDist_projectionCoordUnifiedRandom_query_prefetch_irrelevant
    {alpha : Type} (target : ProjectionCoordSpec.Domain)
    (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        (liftM (ProjectionCoordChallengeSpec.query (.inr target)) >>= fun _ =>
          computation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl computation).run' cache) := by
  simpa only [simulateQ_bind, simulateQ_spec_query] using
    (evalDist_projectionCoordUnifiedRandom_prefetch_irrelevant
      target computation cache)

/-- An ignored coordinate query may be erased after an arbitrary adaptive prefix. The prefix may
contain fresh adversary randomness and may itself have populated any coordinate cache entries. -/
theorem evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
    {alpha beta : Type} (before : OracleComp ProjectionCoordChallengeSpec beta)
    (target : ProjectionCoordSpec.Domain)
    (continuation : beta → OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (before >>= fun value =>
        liftM (ProjectionCoordChallengeSpec.query (.inr target)) >>= fun _ =>
          continuation value)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        (before >>= continuation)).run' cache) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq,
    StateT.run_bind, map_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro result
  simpa only [StateT.run'_eq, StateT.run_bind, map_bind] using
    (evalDist_projectionCoordUnifiedRandom_prefetch_irrelevant
      target (continuation result.1) result.2)

/-! ## Source-visible eager-to-deferred normalization -/

/-- Interpret the existing complete-stream observation handler through the eager coordinate view. -/
noncomputable def sourceKdfEagerCoordinateObservationForwardImpl :
    QueryImpl SourceKdfAdversarySpec
      (StateT SourceProjectionLog (OracleComp ProjectionCoordChallengeSpec)) :=
  jointKdfStreamEagerCoordinateForwardImpl.mapStateTBase
    sourceKdfStreamObservationForwardImpl

/-- Selective-coordinate observation handler. It records only coordinates returned by the source
call and never issues a query for a latent coordinate. -/
def sourceKdfCoordinateObservationForwardImpl :
    QueryImpl SourceKdfAdversarySpec
      (StateT SourceProjectionLog (OracleComp ProjectionCoordChallengeSpec))
  | .inl randomQuery => StateT.mk fun log =>
      (fun value => (value, log)) <$>
        liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery))
  | .inr sourceQuery => StateT.mk fun log => do
      let output ← sourceKdfCoordinateForwardImpl (.inr sourceQuery)
      pure (output, log.recordOutput sourceQuery output)

/-- Eager complete-coordinate source computation retaining exactly the source-visible trace. -/
noncomputable def sourceKdfEagerCoordinateObservedMain {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    OracleComp ProjectionCoordChallengeSpec (Bool × SourceProjectionLog) :=
  (simulateQ sourceKdfEagerCoordinateObservationForwardImpl adversary.main).run
    emptySourceProjectionLog

/-- Deferred selective-coordinate source computation retaining exactly the same trace type. -/
def sourceKdfCoordinateObservedMain {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    OracleComp ProjectionCoordChallengeSpec (Bool × SourceProjectionLog) :=
  (simulateQ sourceKdfCoordinateObservationForwardImpl adversary.main).run
    emptySourceProjectionLog

/-- Mapping the complete-stream observation handler through eager coordinates gives the explicit
eager source computation exactly, before any random-oracle interpretation. -/
theorem simulateQ_jointKdfStreamEagerCoordinate_sourceKdfStreamObservedMain
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    simulateQ jointKdfStreamEagerCoordinateForwardImpl
        (sourceKdfStreamObservedMain adversary) =
      sourceKdfEagerCoordinateObservedMain adversary := by
  unfold sourceKdfStreamObservedMain sourceKdfEagerCoordinateObservedMain
    sourceKdfEagerCoordinateObservationForwardImpl
  exact QueryImpl.simulateQ_mapStateTBase_run
    jointKdfStreamEagerCoordinateForwardImpl
    sourceKdfStreamObservationForwardImpl adversary.main emptySourceProjectionLog

@[simp] theorem sourceKdfEagerCoordinateObservationForwardImpl_uniform_run
    (query : unifSpec.Domain) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl (.inl query)).run log =
      (fun value => (value, log)) <$>
        liftM (ProjectionCoordChallengeSpec.query (.inl query)) := by
  simp [sourceKdfEagerCoordinateObservationForwardImpl, QueryImpl.mapStateTBase,
    sourceKdfStreamObservationForwardImpl, jointKdfStreamEagerCoordinateForwardImpl]

theorem sourceKdfEagerCoordinateObservationForwardImpl_source_run
    (query : SourceKdfQuery) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl (.inr query)).run log = (do
      let stream ← jointKdfStreamEagerCoordinateForwardImpl (.inr query.address)
      pure (query.output stream, log.record query stream)) := by
  simp [sourceKdfEagerCoordinateObservationForwardImpl, QueryImpl.mapStateTBase,
    sourceKdfStreamObservationForwardImpl]

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_uniform_run
    (query : unifSpec.Domain) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl (.inl query)).run log =
      (fun value => (value, log)) <$>
        liftM (ProjectionCoordChallengeSpec.query (.inl query)) := by
  rfl

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_source_run
    (query : SourceKdfQuery) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl (.inr query)).run log = (do
      let output ← sourceKdfCoordinateForwardImpl (.inr query)
      pure (output, log.recordOutput query output)) := by
  rfl

theorem sourceKdfEagerCoordinateObservationForwardImpl_root_run
    (input : Pqxdh.Bytes) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl
      (.inr (.root input))).run log = (do
        let first ← queryFirstCoord (FixedHkdfDomain.pqxdh.address input)
        let _ ← querySecondCoord (FixedHkdfDomain.pqxdh.address input)
        let _ ← queryNonceCoord (FixedHkdfDomain.pqxdh.address input)
        pure (first, log.recordOutput (.root input) first)) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_source_run]
  simp [jointKdfStreamEagerCoordinateForwardImpl, queryStepCoords,
    SourceKdfQuery.output, SourceKdfQuery.address, SourceProjectionLog.record,
    SourceProjectionLog.recordOutput, SourceKdfQuery.observations32,
    SourceKdfQuery.observations12]

theorem sourceKdfEagerCoordinateObservationForwardImpl_initial_run
    (input : Pqxdh.Bytes) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl
      (.inr (.initial input))).run log = (do
        let first ← queryFirstCoord (FixedHkdfDomain.ratchet.address input)
        let second ← querySecondCoord (FixedHkdfDomain.ratchet.address input)
        let _ ← queryNonceCoord (FixedHkdfDomain.ratchet.address input)
        pure ((first, second), log.recordOutput (.initial input) (first, second))) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_source_run]
  simp [jointKdfStreamEagerCoordinateForwardImpl, queryStepCoords,
    SourceKdfQuery.output, SourceKdfQuery.address, SourceProjectionLog.record,
    SourceProjectionLog.recordOutput, SourceKdfQuery.observations32,
    SourceKdfQuery.observations12]

theorem sourceKdfEagerCoordinateObservationForwardImpl_step_run
    (input : Pqxdh.Bytes) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl
      (.inr (.step input))).run log = (do
        let first ← queryFirstCoord (FixedHkdfDomain.ratchet.address input)
        let second ← querySecondCoord (FixedHkdfDomain.ratchet.address input)
        let nonce ← queryNonceCoord (FixedHkdfDomain.ratchet.address input)
        pure ((first, second, nonce),
          log.recordOutput (.step input) (first, second, nonce))) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_source_run]
  simp [jointKdfStreamEagerCoordinateForwardImpl, queryStepCoords,
    SourceKdfQuery.output, SourceKdfQuery.address, SourceProjectionLog.record,
    SourceProjectionLog.recordOutput, SourceKdfQuery.observations32,
    SourceKdfQuery.observations12]

theorem sourceKdfEagerCoordinateObservationForwardImpl_project_first_run
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl
      (.inr (.project ⟨input, domain, .first32⟩))).run log = (do
        let first ← queryFirstCoord (domain.address input)
        let _ ← querySecondCoord (domain.address input)
        let _ ← queryNonceCoord (domain.address input)
        pure (first,
          log.recordOutput (.project ⟨input, domain, .first32⟩) first)) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_source_run]
  simp [jointKdfStreamEagerCoordinateForwardImpl, queryStepCoords,
    SourceKdfQuery.output, SourceKdfQuery.address, JointKdfViewQuery.address,
    JointKdfViewQuery.project,
    SourceProjectionLog.record, SourceProjectionLog.recordOutput,
    SourceKdfQuery.observations32, SourceKdfQuery.observations12]

theorem sourceKdfEagerCoordinateObservationForwardImpl_project_second_run
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl
      (.inr (.project ⟨input, domain, .second32⟩))).run log = (do
        let _ ← queryFirstCoord (domain.address input)
        let second ← querySecondCoord (domain.address input)
        let _ ← queryNonceCoord (domain.address input)
        pure (second,
          log.recordOutput (.project ⟨input, domain, .second32⟩) second)) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_source_run]
  simp [jointKdfStreamEagerCoordinateForwardImpl, queryStepCoords,
    SourceKdfQuery.output, SourceKdfQuery.address, JointKdfViewQuery.address,
    JointKdfViewQuery.project,
    SourceProjectionLog.record, SourceProjectionLog.recordOutput,
    SourceKdfQuery.observations32, SourceKdfQuery.observations12]

theorem sourceKdfEagerCoordinateObservationForwardImpl_project_nonce_run
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (log : SourceProjectionLog) :
    (sourceKdfEagerCoordinateObservationForwardImpl
      (.inr (.project ⟨input, domain, .final12⟩))).run log = (do
        let _ ← queryFirstCoord (domain.address input)
        let _ ← querySecondCoord (domain.address input)
        let nonce ← queryNonceCoord (domain.address input)
        pure (nonce,
          log.recordOutput (.project ⟨input, domain, .final12⟩) nonce)) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_source_run]
  simp [jointKdfStreamEagerCoordinateForwardImpl, queryStepCoords,
    SourceKdfQuery.output, SourceKdfQuery.address, JointKdfViewQuery.address,
    JointKdfViewQuery.project,
    SourceProjectionLog.record, SourceProjectionLog.recordOutput,
    SourceKdfQuery.observations32, SourceKdfQuery.observations12]

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_root_run
    (input : Pqxdh.Bytes) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl (.inr (.root input))).run log = (do
      let first ← queryFirstCoord (FixedHkdfDomain.pqxdh.address input)
      pure (first, log.recordOutput (.root input) first)) := by
  rfl

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_initial_run
    (input : Pqxdh.Bytes) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl (.inr (.initial input))).run log = (do
      let first ← queryFirstCoord (FixedHkdfDomain.ratchet.address input)
      let second ← querySecondCoord (FixedHkdfDomain.ratchet.address input)
      pure ((first, second), log.recordOutput (.initial input) (first, second))) := by
  rfl

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_step_run
    (input : Pqxdh.Bytes) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl (.inr (.step input))).run log = (do
      let first ← queryFirstCoord (FixedHkdfDomain.ratchet.address input)
      let second ← querySecondCoord (FixedHkdfDomain.ratchet.address input)
      let nonce ← queryNonceCoord (FixedHkdfDomain.ratchet.address input)
      pure ((first, second, nonce),
        log.recordOutput (.step input) (first, second, nonce))) := by
  rfl

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_project_first_run
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl
      (.inr (.project ⟨input, domain, .first32⟩))).run log = (do
        let first ← queryFirstCoord (domain.address input)
        pure (first,
          log.recordOutput (.project ⟨input, domain, .first32⟩) first)) := by
  rfl

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_project_second_run
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl
      (.inr (.project ⟨input, domain, .second32⟩))).run log = (do
        let second ← querySecondCoord (domain.address input)
        pure (second,
          log.recordOutput (.project ⟨input, domain, .second32⟩) second)) := by
  rfl

@[simp] theorem sourceKdfCoordinateObservationForwardImpl_project_nonce_run
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain) (log : SourceProjectionLog) :
    (sourceKdfCoordinateObservationForwardImpl
      (.inr (.project ⟨input, domain, .final12⟩))).run log = (do
        let nonce ← queryNonceCoord (domain.address input)
        pure (nonce,
          log.recordOutput (.project ⟨input, domain, .final12⟩) nonce)) := by
  rfl

/-- Contextual eager-to-deferred law for a public second-coordinate call. This is the hardest
ordering case: an ignored first coordinate precedes the returned second coordinate, while an
ignored nonce follows it. -/
theorem evalDist_sourceKdfEager_project_second_bind_eq_deferred
    {alpha : Type} (input : Pqxdh.Bytes) (domain : FixedHkdfDomain)
    (log : SourceProjectionLog)
    (continuation : Projection32Value × SourceProjectionLog →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl
          (.inr (.project ⟨input, domain, .second32⟩))).run log >>=
            continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl
          (.inr (.project ⟨input, domain, .second32⟩))).run log >>=
            continuation)).run' cache) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_project_second_run,
    sourceKdfCoordinateObservationForwardImpl_project_second_run]
  simp only [bind_assoc, pure_bind]
  let address := domain.address input
  let next : Projection32Value → OracleComp ProjectionCoordChallengeSpec alpha :=
    fun second => continuation (second,
      log.recordOutput (.project ⟨input, domain, .second32⟩) second)
  change evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let _ ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (firstCoord address))))
      let second ← querySecondCoord address
      let _ ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inr address)))
      next second)).run' cache) =
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let second ← querySecondCoord address
      next second)).run' cache)
  calc
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let _ ← liftM (ProjectionCoordChallengeSpec.query
          (.inr (.inl (firstCoord address))))
        let second ← querySecondCoord address
        let _ ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inr address)))
        next second)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let second ← querySecondCoord address
        let _ ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inr address)))
        next second)).run' cache) :=
      evalDist_projectionCoordUnifiedRandom_query_prefetch_irrelevant
        (.inl (firstCoord address)) _ cache
    _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let second ← querySecondCoord address
        next second)).run' cache) := by
      exact evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
        (querySecondCoord address) (.inr address) next cache

theorem evalDist_sourceKdfEager_root_bind_eq_deferred
    {alpha : Type} (input : Pqxdh.Bytes) (log : SourceProjectionLog)
    (continuation : Projection32Value × SourceProjectionLog →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl
          (.inr (.root input))).run log >>= continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl
          (.inr (.root input))).run log >>= continuation)).run' cache) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_root_run,
    sourceKdfCoordinateObservationForwardImpl_root_run]
  simp only [bind_assoc, pure_bind]
  let address := FixedHkdfDomain.pqxdh.address input
  let next : Projection32Value → OracleComp ProjectionCoordChallengeSpec alpha :=
    fun first => continuation (first, log.recordOutput (.root input) first)
  change evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← queryFirstCoord address
      let _ ← querySecondCoord address
      let _ ← queryNonceCoord address
      next first)).run' cache) =
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← queryFirstCoord address
      next first)).run' cache)
  calc
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let first ← queryFirstCoord address
        let _ ← querySecondCoord address
        let _ ← queryNonceCoord address
        next first)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let first ← queryFirstCoord address
        let _ ← querySecondCoord address
        next first)).run' cache) := by
      simpa [queryNonceCoord, monad_norm] using
        (evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
          (do
            let first ← queryFirstCoord address
            let _ ← querySecondCoord address
            pure first)
          (.inr address) next cache)
    _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let first ← queryFirstCoord address
        next first)).run' cache) := by
      simpa [querySecondCoord] using
        (evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
          (queryFirstCoord address) (.inl (secondCoord address)) next cache)

theorem evalDist_sourceKdfEager_initial_bind_eq_deferred
    {alpha : Type} (input : Pqxdh.Bytes) (log : SourceProjectionLog)
    (continuation : (Projection32Value × Projection32Value) × SourceProjectionLog →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl
          (.inr (.initial input))).run log >>= continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl
          (.inr (.initial input))).run log >>= continuation)).run' cache) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_initial_run,
    sourceKdfCoordinateObservationForwardImpl_initial_run]
  simp only [bind_assoc, pure_bind]
  let address := FixedHkdfDomain.ratchet.address input
  let next : Projection32Value × Projection32Value →
      OracleComp ProjectionCoordChallengeSpec alpha :=
    fun output => continuation (output,
      log.recordOutput (.initial input) output)
  change evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← queryFirstCoord address
      let second ← querySecondCoord address
      let _ ← queryNonceCoord address
      next (first, second))).run' cache) =
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← queryFirstCoord address
      let second ← querySecondCoord address
      next (first, second))).run' cache)
  simpa [queryNonceCoord, queryInitialCoords, monad_norm] using
    (evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
      (queryInitialCoords address) (.inr address) next cache)

theorem evalDist_sourceKdfEager_step_bind_eq_deferred
    {alpha : Type} (input : Pqxdh.Bytes) (log : SourceProjectionLog)
    (continuation :
      (Projection32Value × Projection32Value × Projection12Value) ×
        SourceProjectionLog → OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl
          (.inr (.step input))).run log >>= continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl
          (.inr (.step input))).run log >>= continuation)).run' cache) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_step_run,
    sourceKdfCoordinateObservationForwardImpl_step_run]

theorem evalDist_sourceKdfEager_project_first_bind_eq_deferred
    {alpha : Type} (input : Pqxdh.Bytes) (domain : FixedHkdfDomain)
    (log : SourceProjectionLog)
    (continuation : Projection32Value × SourceProjectionLog →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl
          (.inr (.project ⟨input, domain, .first32⟩))).run log >>=
            continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl
          (.inr (.project ⟨input, domain, .first32⟩))).run log >>=
            continuation)).run' cache) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_project_first_run,
    sourceKdfCoordinateObservationForwardImpl_project_first_run]
  simp only [bind_assoc, pure_bind]
  let address := domain.address input
  let next : Projection32Value → OracleComp ProjectionCoordChallengeSpec alpha :=
    fun first => continuation (first,
      log.recordOutput (.project ⟨input, domain, .first32⟩) first)
  change evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← queryFirstCoord address
      let _ ← querySecondCoord address
      let _ ← queryNonceCoord address
      next first)).run' cache) =
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let first ← queryFirstCoord address
      next first)).run' cache)
  calc
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let first ← queryFirstCoord address
        let _ ← querySecondCoord address
        let _ ← queryNonceCoord address
        next first)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let first ← queryFirstCoord address
        let _ ← querySecondCoord address
        next first)).run' cache) := by
      simpa [queryNonceCoord, monad_norm] using
        (evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
          (do
            let first ← queryFirstCoord address
            let _ ← querySecondCoord address
            pure first)
          (.inr address) next cache)
    _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let first ← queryFirstCoord address
        next first)).run' cache) := by
      simpa [querySecondCoord] using
        (evalDist_projectionCoordUnifiedRandom_insert_prefetch_irrelevant
          (queryFirstCoord address) (.inl (secondCoord address)) next cache)

theorem evalDist_sourceKdfEager_project_nonce_bind_eq_deferred
    {alpha : Type} (input : Pqxdh.Bytes) (domain : FixedHkdfDomain)
    (log : SourceProjectionLog)
    (continuation : Projection12Value × SourceProjectionLog →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl
          (.inr (.project ⟨input, domain, .final12⟩))).run log >>=
            continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl
          (.inr (.project ⟨input, domain, .final12⟩))).run log >>=
            continuation)).run' cache) := by
  rw [sourceKdfEagerCoordinateObservationForwardImpl_project_nonce_run,
    sourceKdfCoordinateObservationForwardImpl_project_nonce_run]
  simp only [bind_assoc, pure_bind]
  let address := domain.address input
  let next : Projection12Value → OracleComp ProjectionCoordChallengeSpec alpha :=
    fun nonce => continuation (nonce,
      log.recordOutput (.project ⟨input, domain, .final12⟩) nonce)
  change evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let _ ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (firstCoord address))))
      let _ ← liftM (ProjectionCoordChallengeSpec.query
        (.inr (.inl (secondCoord address))))
      let nonce ← queryNonceCoord address
      next nonce)).run' cache) =
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
      let nonce ← queryNonceCoord address
      next nonce)).run' cache)
  calc
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let _ ← liftM (ProjectionCoordChallengeSpec.query
          (.inr (.inl (firstCoord address))))
        let _ ← liftM (ProjectionCoordChallengeSpec.query
          (.inr (.inl (secondCoord address))))
        let nonce ← queryNonceCoord address
        next nonce)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let _ ← liftM (ProjectionCoordChallengeSpec.query
          (.inr (.inl (secondCoord address))))
        let nonce ← queryNonceCoord address
        next nonce)).run' cache) :=
      evalDist_projectionCoordUnifiedRandom_query_prefetch_irrelevant
        (.inl (firstCoord address)) _ cache
    _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl (do
        let nonce ← queryNonceCoord address
        next nonce)).run' cache) :=
      evalDist_projectionCoordUnifiedRandom_query_prefetch_irrelevant
        (.inl (secondCoord address)) _ cache

/-- Every single source-surface query has the same contextual output law in the eager and
selective-coordinate views. The continuation may reveal any previously hidden coordinate. -/
theorem evalDist_sourceKdfEager_query_bind_eq_deferred
    {alpha : Type} (query : SourceKdfAdversarySpec.Domain)
    (log : SourceProjectionLog)
    (continuation : SourceKdfAdversarySpec.Range query × SourceProjectionLog →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfEagerCoordinateObservationForwardImpl query).run log >>=
          continuation)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((sourceKdfCoordinateObservationForwardImpl query).run log >>=
          continuation)).run' cache) := by
  rcases query with randomQuery | sourceQuery
  · rw [sourceKdfEagerCoordinateObservationForwardImpl_uniform_run,
      sourceKdfCoordinateObservationForwardImpl_uniform_run]
  · rcases sourceQuery with input | input | input | ⟨input, domain, projection⟩
    · exact evalDist_sourceKdfEager_root_bind_eq_deferred
        input log continuation cache
    · exact evalDist_sourceKdfEager_initial_bind_eq_deferred
        input log continuation cache
    · exact evalDist_sourceKdfEager_step_bind_eq_deferred
        input log continuation cache
    · cases projection
      · exact evalDist_sourceKdfEager_project_first_bind_eq_deferred
          input domain log continuation cache
      · exact evalDist_sourceKdfEager_project_second_bind_eq_deferred
          input domain log continuation cache
      · exact evalDist_sourceKdfEager_project_nonce_bind_eq_deferred
          input domain log continuation cache

private lemma run_simulateQ_sourceProjectionObservation_query_bind
    {alpha : Type}
    (impl : QueryImpl SourceKdfAdversarySpec
      (StateT SourceProjectionLog (OracleComp ProjectionCoordChallengeSpec)))
    (query : SourceKdfAdversarySpec.Domain)
    (rest : SourceKdfAdversarySpec.Range query →
      OracleComp SourceKdfAdversarySpec alpha)
    (log : SourceProjectionLog) :
    (simulateQ impl
      (liftM (SourceKdfAdversarySpec.query query) >>= rest)).run log =
        (impl query).run log >>= fun result =>
          (simulateQ impl (rest result.1)).run result.2 := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  simp [OracleQuery.cont_query]

/-- Eager complete-coordinate sampling and selective deferred-coordinate sampling have exactly
the same output-plus-visible-log law for every adaptive source computation. Final coordinate
caches are deliberately not compared. -/
theorem evalDist_sourceKdfEagerCoordinate_eq_deferred
    {alpha : Type} (computation : OracleComp SourceKdfAdversarySpec alpha)
    (log : SourceProjectionLog) (cache : ProjectionCoordUnifiedCache) :
    evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((simulateQ sourceKdfEagerCoordinateObservationForwardImpl computation).run
          log)).run' cache) =
      evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        ((simulateQ sourceKdfCoordinateObservationForwardImpl computation).run
          log)).run' cache) := by
  induction computation using OracleComp.inductionOn generalizing log cache with
  | pure output => simp
  | query_bind query rest ih =>
      rw [run_simulateQ_sourceProjectionObservation_query_bind,
        run_simulateQ_sourceProjectionObservation_query_bind]
      calc
        evalDist ((simulateQ projectionCoordUnifiedRandomImpl
            ((sourceKdfEagerCoordinateObservationForwardImpl query).run log >>= fun result =>
              (simulateQ sourceKdfEagerCoordinateObservationForwardImpl
                (rest result.1)).run result.2)).run' cache) =
          evalDist ((simulateQ projectionCoordUnifiedRandomImpl
            ((sourceKdfCoordinateObservationForwardImpl query).run log >>= fun result =>
              (simulateQ sourceKdfEagerCoordinateObservationForwardImpl
                (rest result.1)).run result.2)).run' cache) :=
          evalDist_sourceKdfEager_query_bind_eq_deferred query log
            (fun result =>
              (simulateQ sourceKdfEagerCoordinateObservationForwardImpl
                (rest result.1)).run result.2) cache
        _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl
            ((sourceKdfCoordinateObservationForwardImpl query).run log >>= fun result =>
              (simulateQ sourceKdfCoordinateObservationForwardImpl
                (rest result.1)).run result.2)).run' cache) := by
          simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
          apply OracleComp.DeferredSampling.evalDist_bind_congr_left
          intro result
          exact ih result.1.1 result.1.2 result.2

/-- The unified dependent-range coordinate cache is exactly the existing pair of width-specific
caches, query by query; transparent uniform samples touch neither representation. -/
theorem projectionCoordUnifiedRandomImpl_toPair_query
    (query : ProjectionCoordChallengeSpec.Domain)
    (cache : ProjectionCoordUnifiedCache) :
    Prod.map id projectionCoordUnifiedCacheToPair <$>
        (projectionCoordUnifiedRandomImpl query).run cache =
      (projectionCoordLazyRandomImpl query).run
        (projectionCoordUnifiedCacheToPair cache) := by
  rcases query with randomQuery | coordinateQuery
  · rw [projectionCoordUnifiedRandomImpl_uniform_run,
      projectionCoordLazyRandomImpl_uniform_run]
    change Prod.map id projectionCoordUnifiedCacheToPair <$>
        ((fun value : unifSpec.Range randomQuery => (value, cache)) <$>
          uniformSampleImpl randomQuery) =
      (fun value : unifSpec.Range randomQuery =>
        (value, projectionCoordUnifiedCacheToPair cache)) <$>
          uniformSampleImpl randomQuery
    simp only [Functor.map_map]
    rfl
  · rcases coordinateQuery with coord | nonce
    · cases hcache : cache (.inl coord) with
      | none =>
          have hpair : (projectionCoordUnifiedCacheToPair cache).1 coord = none := hcache
          rw [projectionCoordUnifiedRandomImpl_coordinate_run_miss
              (.inl coord) cache hcache,
            projectionCoordLazyRandomImpl_first_run_miss coord _ hpair]
          change Prod.map id projectionCoordUnifiedCacheToPair <$>
              ((fun value : Projection32Value =>
                (value, cache.cacheQuery (.inl coord) value)) <$>
                  ($ᵗ Projection32Value)) =
            (fun value : Projection32Value =>
              (value, ((projectionCoordUnifiedCacheToPair cache).1.cacheQuery
                coord value, (projectionCoordUnifiedCacheToPair cache).2))) <$>
                  ($ᵗ Projection32Value)
          rw [Functor.map_map]
          apply congrArg (fun function => function <$> ($ᵗ Projection32Value))
          funext value
          change (value, projectionCoordUnifiedCacheToPair
              (cache.cacheQuery (.inl coord) value)) = _
          rw [projectionCoordUnifiedCacheToPair_cacheQuery32]
      | some value =>
          have hpair : (projectionCoordUnifiedCacheToPair cache).1 coord = some value :=
            hcache
          rw [projectionCoordUnifiedRandomImpl_coordinate_run_hit
              (.inl coord) cache value hcache,
            projectionCoordLazyRandomImpl_first_run_hit coord _ value hpair]
          simp
    · cases hcache : cache (.inr nonce) with
      | none =>
          have hpair : (projectionCoordUnifiedCacheToPair cache).2 nonce = none := hcache
          rw [projectionCoordUnifiedRandomImpl_coordinate_run_miss
              (.inr nonce) cache hcache,
            projectionCoordLazyRandomImpl_nonce_run_miss nonce _ hpair]
          change Prod.map id projectionCoordUnifiedCacheToPair <$>
              ((fun value : Projection12Value =>
                (value, cache.cacheQuery (.inr nonce) value)) <$>
                  ($ᵗ Projection12Value)) =
            (fun value : Projection12Value =>
              (value, ((projectionCoordUnifiedCacheToPair cache).1,
                (projectionCoordUnifiedCacheToPair cache).2.cacheQuery
                  nonce value))) <$> ($ᵗ Projection12Value)
          rw [Functor.map_map]
          apply congrArg (fun function => function <$> ($ᵗ Projection12Value))
          funext value
          change (value, projectionCoordUnifiedCacheToPair
              (cache.cacheQuery (.inr nonce) value)) = _
          rw [projectionCoordUnifiedCacheToPair_cacheQuery12]
      | some value =>
          have hpair : (projectionCoordUnifiedCacheToPair cache).2 nonce = some value :=
            hcache
          rw [projectionCoordUnifiedRandomImpl_coordinate_run_hit
              (.inr nonce) cache value hcache,
            projectionCoordLazyRandomImpl_nonce_run_hit nonce _ value hpair]
          simp

/-- Whole-run exact cache-representation bridge. -/
theorem projectionCoordUnifiedRandomImpl_simulateQ_run_toPair
    {alpha : Type} (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    Prod.map id projectionCoordUnifiedCacheToPair <$>
        (simulateQ projectionCoordUnifiedRandomImpl computation).run cache =
      (simulateQ projectionCoordLazyRandomImpl computation).run
        (projectionCoordUnifiedCacheToPair cache) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    projectionCoordUnifiedRandomImpl projectionCoordLazyRandomImpl
    projectionCoordUnifiedCacheToPair
    projectionCoordUnifiedRandomImpl_toPair_query computation cache

/-- Output-only corollary of the exact cache-representation bridge. -/
theorem projectionCoordUnifiedRandomImpl_simulateQ_run'_eq_toPair
    {alpha : Type} (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (cache : ProjectionCoordUnifiedCache) :
    (simulateQ projectionCoordUnifiedRandomImpl computation).run' cache =
      (simulateQ projectionCoordLazyRandomImpl computation).run'
        (projectionCoordUnifiedCacheToPair cache) := by
  have hrun := congrArg (Functor.map Prod.fst)
    (projectionCoordUnifiedRandomImpl_simulateQ_run_toPair computation cache)
  simpa [StateT.run'_eq, Functor.map_map, Function.comp_apply, Prod.map] using hrun

/-- Add one returned 32-byte coordinate to the source-visible trace. -/
def SourceProjectionLog.log32 (log : SourceProjectionLog)
    (coord : Coord32) (value : Projection32Value) : SourceProjectionLog :=
  ⟨⟨coord, value⟩ :: log.observations32, log.observations12⟩

/-- Add one returned nonce coordinate to the source-visible trace. -/
def SourceProjectionLog.log12 (log : SourceProjectionLog)
    (coord : Coord12) (value : Projection12Value) : SourceProjectionLog :=
  ⟨log.observations32, ⟨coord, value⟩ :: log.observations12⟩

/-- Forward the normalized challenge while logging exactly the coordinates actually queried.
Uniform adversary randomness is forwarded without a log entry. -/
def projectionCoordVisibleTraceForwardImpl :
    QueryImpl ProjectionCoordChallengeSpec
      (StateT SourceProjectionLog (OracleComp ProjectionCoordChallengeSpec))
  | .inl randomQuery => StateT.mk fun log => do
      let value ← liftM (ProjectionCoordChallengeSpec.query (.inl randomQuery))
      pure (value, log)
  | .inr (.inl coord) => StateT.mk fun log => do
      let value ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord)))
      pure (value, log.log32 coord value)
  | .inr (.inr coord) => StateT.mk fun log => do
      let value ← liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord)))
      pure (value, log.log12 coord value)

/-- Structural query step for the source-visible coordinate trace. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query_bind
    {alpha : Type} (query : ProjectionCoordChallengeSpec.Domain)
    (rest : ProjectionCoordChallengeSpec.Range query →
      OracleComp ProjectionCoordChallengeSpec alpha)
    (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      (liftM (ProjectionCoordChallengeSpec.query query) >>= rest)).run log =
        (projectionCoordVisibleTraceForwardImpl query).run log >>= fun result =>
          (simulateQ projectionCoordVisibleTraceForwardImpl (rest result.1)).run result.2 := by
  simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
  simp [OracleQuery.cont_query]

/-- A single source-visible coordinate query is interpreted by the trace handler itself. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query
    (query : ProjectionCoordChallengeSpec.Domain) (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      (liftM (ProjectionCoordChallengeSpec.query query))).run log =
        (projectionCoordVisibleTraceForwardImpl query).run log := by
  rw [simulateQ_spec_query]

/-- Concrete 32-byte form of the visible-trace query law. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query32
    (coord : Coord32) (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection32Value)).run log =
      (fun value => (value, log.log32 coord value)) <$>
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) := by
  have h := simulateQ_spec_query projectionCoordVisibleTraceForwardImpl
    (.inr (.inl coord))
  have hrun := congrArg (fun computation => computation.run log) h
  exact hrun.trans rfl

/-- Concrete nonce form of the visible-trace query law. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query12
    (coord : Coord12) (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection12Value)).run log =
      (fun value => (value, log.log12 coord value)) <$>
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
          OracleComp ProjectionCoordChallengeSpec Projection12Value) := by
  have h := simulateQ_spec_query projectionCoordVisibleTraceForwardImpl
    (.inr (.inr coord))
  have hrun := congrArg (fun computation => computation.run log) h
  exact hrun.trans rfl

/-- Map form of one 32-byte visible coordinate query. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_map_query32
    {alpha : Type} (coord : Coord32) (mapOutput : Projection32Value → alpha)
    (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      (mapOutput <$> (liftM
        (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value))).run log =
      (fun value => (mapOutput value, log.log32 coord value)) <$>
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) := by
  have hmap := congrArg (fun computation => computation.run log)
    (simulateQ_map projectionCoordVisibleTraceForwardImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection32Value) mapOutput)
  calc
    _ = (fun result => (mapOutput result.1, result.2)) <$>
          (simulateQ projectionCoordVisibleTraceForwardImpl
            (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
              OracleComp ProjectionCoordChallengeSpec Projection32Value)).run log := by
        simpa only [StateT.run_map] using hmap
    _ = _ := by
      rw [run_simulateQ_projectionCoordVisibleTrace_query32]
      simp only [Functor.map_map]

/-- Map form of one visible nonce coordinate query. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_map_query12
    {alpha : Type} (coord : Coord12) (mapOutput : Projection12Value → alpha)
    (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      (mapOutput <$> (liftM
        (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
          OracleComp ProjectionCoordChallengeSpec Projection12Value))).run log =
      (fun value => (mapOutput value, log.log12 coord value)) <$>
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
          OracleComp ProjectionCoordChallengeSpec Projection12Value) := by
  have hmap := congrArg (fun computation => computation.run log)
    (simulateQ_map projectionCoordVisibleTraceForwardImpl
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection12Value) mapOutput)
  calc
    _ = (fun result => (mapOutput result.1, result.2)) <$>
          (simulateQ projectionCoordVisibleTraceForwardImpl
            (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
              OracleComp ProjectionCoordChallengeSpec Projection12Value)).run log := by
        simpa only [StateT.run_map] using hmap
    _ = _ := by
      rw [run_simulateQ_projectionCoordVisibleTrace_query12]
      simp only [Functor.map_map]

/-- Concrete 32-byte bind form of the visible-trace query law. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query32_bind
    {alpha : Type} (coord : Coord32)
    (rest : Projection32Value → OracleComp ProjectionCoordChallengeSpec alpha)
    (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      ((liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= rest)).run log =
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun value =>
          (simulateQ projectionCoordVisibleTraceForwardImpl (rest value)).run
            (log.log32 coord value) := by
  have h := run_simulateQ_projectionCoordVisibleTrace_query_bind
    (.inr (.inl coord)) rest log
  exact h.trans (by
    simp [projectionCoordVisibleTraceForwardImpl, StateT.run_mk])

/-- Concrete nonce bind form of the visible-trace query law. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query12_bind
    {alpha : Type} (coord : Coord12)
    (rest : Projection12Value → OracleComp ProjectionCoordChallengeSpec alpha)
    (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl
      ((liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection12Value) >>= rest)).run log =
      (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr coord))) :
        OracleComp ProjectionCoordChallengeSpec Projection12Value) >>= fun value =>
          (simulateQ projectionCoordVisibleTraceForwardImpl (rest value)).run
            (log.log12 coord value) := by
  have h := run_simulateQ_projectionCoordVisibleTrace_query_bind
    (.inr (.inr coord)) rest log
  exact h.trans (by
    simp [projectionCoordVisibleTraceForwardImpl, StateT.run_mk])

/-- Two visible 32-byte queries are logged in their exact return order. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query32_pair
    (first second : Coord32) (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl (do
      let firstValue ←
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value)
      let secondValue ←
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value)
      pure (firstValue, secondValue))).run log =
        (fun output => (output,
          (log.log32 first output.1).log32 second output.2)) <$> (do
            let firstValue ←
              (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
                OracleComp ProjectionCoordChallengeSpec Projection32Value)
            let secondValue ←
              (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
                OracleComp ProjectionCoordChallengeSpec Projection32Value)
            pure (firstValue, secondValue)) := by
  calc
    _ = (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun firstValue =>
        (simulateQ projectionCoordVisibleTraceForwardImpl
          ((fun secondValue => (firstValue, secondValue)) <$>
            (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
              OracleComp ProjectionCoordChallengeSpec Projection32Value))).run
                (log.log32 first firstValue) :=
      run_simulateQ_projectionCoordVisibleTrace_query32_bind first _ log
    _ = (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun firstValue =>
        (fun secondValue => ((firstValue, secondValue),
          (log.log32 first firstValue).log32 second secondValue)) <$>
            (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
              OracleComp ProjectionCoordChallengeSpec Projection32Value) := by
      refine bind_congr (m := OracleComp ProjectionCoordChallengeSpec) fun firstValue => ?_
      exact run_simulateQ_projectionCoordVisibleTrace_map_query32 second
        (Prod.mk firstValue) (log.log32 first firstValue)
    _ = _ := by
      simp [map_bind]

/-- A step call logs its two 32-byte coordinates and nonce, with no latent observations. -/
private lemma run_simulateQ_projectionCoordVisibleTrace_query32_pair_query12
    (first second : Coord32) (nonce : Coord12) (log : SourceProjectionLog) :
    (simulateQ projectionCoordVisibleTraceForwardImpl (do
      let firstValue ←
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value)
      let secondValue ←
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value)
      let nonceValue ←
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr nonce))) :
          OracleComp ProjectionCoordChallengeSpec Projection12Value)
      pure (firstValue, secondValue, nonceValue))).run log =
        (fun output => (output,
          ((log.log32 first output.1).log32 second output.2.1).log12
            nonce output.2.2)) <$> (do
              let firstValue ←
                (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
                  OracleComp ProjectionCoordChallengeSpec Projection32Value)
              let secondValue ←
                (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
                  OracleComp ProjectionCoordChallengeSpec Projection32Value)
              let nonceValue ←
                (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr nonce))) :
                  OracleComp ProjectionCoordChallengeSpec Projection12Value)
              pure (firstValue, secondValue, nonceValue)) := by
  calc
    _ = (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun firstValue =>
        (simulateQ projectionCoordVisibleTraceForwardImpl (do
          let secondValue ←
            (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
              OracleComp ProjectionCoordChallengeSpec Projection32Value)
          (fun nonceValue => (firstValue, secondValue, nonceValue)) <$>
            (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr nonce))) :
              OracleComp ProjectionCoordChallengeSpec Projection12Value))).run
                (log.log32 first firstValue) :=
      run_simulateQ_projectionCoordVisibleTrace_query32_bind first _ log
    _ = (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun firstValue =>
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun secondValue =>
            (simulateQ projectionCoordVisibleTraceForwardImpl
              ((fun nonceValue => (firstValue, secondValue, nonceValue)) <$>
                (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr nonce))) :
                  OracleComp ProjectionCoordChallengeSpec Projection12Value))).run
                    ((log.log32 first firstValue).log32 second secondValue) := by
      refine bind_congr (m := OracleComp ProjectionCoordChallengeSpec) fun firstValue => ?_
      exact run_simulateQ_projectionCoordVisibleTrace_query32_bind second _
        (log.log32 first firstValue)
    _ = (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl first))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun firstValue =>
        (liftM (ProjectionCoordChallengeSpec.query (.inr (.inl second))) :
          OracleComp ProjectionCoordChallengeSpec Projection32Value) >>= fun secondValue =>
            (fun nonceValue => ((firstValue, secondValue, nonceValue),
              ((log.log32 first firstValue).log32 second secondValue).log12
                nonce nonceValue)) <$>
                  (liftM (ProjectionCoordChallengeSpec.query (.inr (.inr nonce))) :
                    OracleComp ProjectionCoordChallengeSpec Projection12Value) := by
      refine bind_congr (m := OracleComp ProjectionCoordChallengeSpec) fun firstValue => ?_
      refine bind_congr (m := OracleComp ProjectionCoordChallengeSpec) fun secondValue => ?_
      exact run_simulateQ_projectionCoordVisibleTrace_map_query12 nonce
        (fun nonceValue => (firstValue, secondValue, nonceValue))
        ((log.log32 first firstValue).log32 second secondValue)
    _ = _ := by
      simp [map_bind]

/-- Logging the selective coordinate forwarding one coordinate at a time is exactly the same
source computation as recording its typed result once at the source-call boundary. -/
theorem projectionCoordVisibleTrace_comp_sourceKdfCoordinateForwardImpl :
    projectionCoordVisibleTraceForwardImpl ∘ₛ sourceKdfCoordinateForwardImpl =
      sourceKdfCoordinateObservationForwardImpl := by
  funext query
  funext log
  change (simulateQ projectionCoordVisibleTraceForwardImpl
      (sourceKdfCoordinateForwardImpl query)).run log =
    (sourceKdfCoordinateObservationForwardImpl query).run log
  rcases query with randomQuery | sourceQuery
  · simp [StateT.run_mk,
      projectionCoordVisibleTraceForwardImpl,
      sourceKdfCoordinateForwardImpl,
      sourceKdfCoordinateObservationForwardImpl]
  · rcases sourceQuery with input | input | input | ⟨input, domain, projection⟩
    · change (simulateQ projectionCoordVisibleTraceForwardImpl
          (queryFirstCoord (FixedHkdfDomain.pqxdh.address input))).run log =
        (fun output => (output,
          log.log32 (firstCoord (FixedHkdfDomain.pqxdh.address input)) output)) <$>
            queryFirstCoord (FixedHkdfDomain.pqxdh.address input)
      unfold queryFirstCoord
      exact run_simulateQ_projectionCoordVisibleTrace_query32 _ log
    · let address := FixedHkdfDomain.ratchet.address input
      change (simulateQ projectionCoordVisibleTraceForwardImpl
          (queryInitialCoords address)).run log =
        (fun output => (output,
          (log.log32 (firstCoord address) output.1).log32
            (secondCoord address) output.2)) <$> queryInitialCoords address
      unfold queryInitialCoords queryFirstCoord querySecondCoord
      exact run_simulateQ_projectionCoordVisibleTrace_query32_pair
        (firstCoord address) (secondCoord address) log
    · let address := FixedHkdfDomain.ratchet.address input
      change (simulateQ projectionCoordVisibleTraceForwardImpl
          (queryStepCoords address)).run log =
        (fun output => (output,
          ((log.log32 (firstCoord address) output.1).log32
            (secondCoord address) output.2.1).log12 address output.2.2)) <$>
              queryStepCoords address
      unfold queryStepCoords queryFirstCoord querySecondCoord queryNonceCoord
      exact run_simulateQ_projectionCoordVisibleTrace_query32_pair_query12
        (firstCoord address) (secondCoord address) address log
    · cases projection with
      | first32 =>
          change (simulateQ projectionCoordVisibleTraceForwardImpl
            (queryFirstCoord (domain.address input))).run log =
              (fun output => (output,
                log.log32 (firstCoord (domain.address input)) output)) <$>
                  queryFirstCoord (domain.address input)
          unfold queryFirstCoord
          exact run_simulateQ_projectionCoordVisibleTrace_query32 _ log
      | second32 =>
          change (simulateQ projectionCoordVisibleTraceForwardImpl
            (querySecondCoord (domain.address input))).run log =
              (fun output => (output,
                log.log32 (secondCoord (domain.address input)) output)) <$>
                  querySecondCoord (domain.address input)
          unfold querySecondCoord
          exact run_simulateQ_projectionCoordVisibleTrace_query32 _ log
      | final12 =>
          change (simulateQ projectionCoordVisibleTraceForwardImpl
            (queryNonceCoord (domain.address input))).run log =
              (fun output => (output,
                log.log12 (domain.address input) output)) <$>
                  queryNonceCoord (domain.address input)
          unfold queryNonceCoord
          exact run_simulateQ_projectionCoordVisibleTrace_query12 _ log

/-! ## Visible-log bridge to the birthday experiment -/

/-- Interpret visible trace queries through the width-separated lazy caches and flatten the
two states in `(visible log, coordinate cache)` order. -/
noncomputable def projectionCoordVisibleTraceLazyImpl :
    QueryImpl ProjectionCoordChallengeSpec
      (StateT (SourceProjectionLog × ProjectionCoordCache) ProbComp) :=
  (projectionCoordLazyRandomImpl.mapStateTBase
    projectionCoordVisibleTraceForwardImpl).flattenStateT

/-- Reassociate the explicit source log and pair cache into the existing observation state. -/
def sourceProjectionLogCacheToObservationState
    (state : SourceProjectionLog × ProjectionCoordCache) : ProjectionObservationState :=
  ⟨state.2, state.1.observations32, state.1.observations12⟩

@[simp] theorem sourceProjectionLogCacheToObservationState_empty :
    sourceProjectionLogCacheToObservationState
      (emptySourceProjectionLog, (∅, ∅)) = emptyProjectionObservationState := by
  rfl

/-- The flattened visible-trace/lazy-cache handler is exactly the existing combined
cache-and-observation handler, up to the explicit state reassociation. -/
theorem projectionCoordVisibleTraceLazyImpl_toObservation_query
    (query : ProjectionCoordChallengeSpec.Domain)
    (state : SourceProjectionLog × ProjectionCoordCache) :
    (fun result =>
      (result.1, sourceProjectionLogCacheToObservationState result.2)) <$>
        (projectionCoordVisibleTraceLazyImpl query).run state =
      (projectionCoordCachingLoggingImpl query).run
        (sourceProjectionLogCacheToObservationState state) := by
  rcases query with randomQuery | coordinateQuery
  · simp [projectionCoordVisibleTraceLazyImpl,
      sourceProjectionLogCacheToObservationState,
      projectionCoordVisibleTraceForwardImpl,
      QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
      Functor.map_map]
    have hlazy := projectionCoordLazyRandomImpl_uniform_run randomQuery state.2
    have hlogging := projectionCoordCachingLoggingImpl_uniform_run randomQuery
      (sourceProjectionLogCacheToObservationState state)
    calc
      _ = (fun result : unifSpec.Range randomQuery × ProjectionCoordCache =>
            (result.1, sourceProjectionLogCacheToObservationState
              (state.1, result.2))) <$>
          ((fun value : unifSpec.Range randomQuery => (value, state.2)) <$>
            uniformSampleImpl randomQuery) := congrArg
              (Functor.map fun result :
                unifSpec.Range randomQuery × ProjectionCoordCache =>
                  (result.1, sourceProjectionLogCacheToObservationState
                    (state.1, result.2))) hlazy
      _ = (fun value : unifSpec.Range randomQuery =>
            (value, sourceProjectionLogCacheToObservationState state)) <$>
              uniformSampleImpl randomQuery := by
        simp only [Functor.map_map]
      _ = _ := hlogging.symm
  · rcases coordinateQuery with coord | nonce
    · cases hcache : state.2.1 coord with
      | none =>
        simp [projectionCoordVisibleTraceLazyImpl,
          sourceProjectionLogCacheToObservationState,
          projectionCoordVisibleTraceForwardImpl,
          projectionCoordCachingLoggingImpl, hcache,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
          SourceProjectionLog.log32, ProjectionObservationState.log32,
          Functor.map_map]
        have hlazy := projectionCoordLazyRandomImpl_first_run_miss
          coord state.2 hcache
        calc
          _ = (fun result : Projection32Value × ProjectionCoordCache =>
                (result.1,
                  sourceProjectionLogCacheToObservationState
                    (state.1.log32 coord result.1, result.2))) <$>
              ((fun value : Projection32Value =>
                (value, (state.2.1.cacheQuery coord value, state.2.2))) <$>
                  ($ᵗ Projection32Value)) := congrArg
                    (Functor.map fun result : Projection32Value × ProjectionCoordCache =>
                      (result.1,
                        sourceProjectionLogCacheToObservationState
                          (state.1.log32 coord result.1, result.2))) hlazy
          _ = _ := by
            simp only [Functor.map_map]
            rfl
      | some value =>
        simp [projectionCoordVisibleTraceLazyImpl,
          sourceProjectionLogCacheToObservationState,
          projectionCoordVisibleTraceForwardImpl,
          projectionCoordCachingLoggingImpl, hcache,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
          SourceProjectionLog.log32, ProjectionObservationState.log32,
          Functor.map_map]
        have hlazy := projectionCoordLazyRandomImpl_first_run_hit
          coord state.2 value hcache
        have heq := queryCache_cacheQuery_eq_of_some state.2.1 coord value hcache
        calc
          _ = (fun result : Projection32Value × ProjectionCoordCache =>
                (result.1,
                  sourceProjectionLogCacheToObservationState
                    (state.1.log32 coord result.1, result.2))) <$>
              pure (value, state.2) := congrArg
                (Functor.map fun result : Projection32Value × ProjectionCoordCache =>
                  (result.1,
                    sourceProjectionLogCacheToObservationState
                      (state.1.log32 coord result.1, result.2))) hlazy
          _ = _ := by
            simp [sourceProjectionLogCacheToObservationState,
              SourceProjectionLog.log32, heq]
    · cases hcache : state.2.2 nonce with
      | none =>
        simp [projectionCoordVisibleTraceLazyImpl,
          sourceProjectionLogCacheToObservationState,
          projectionCoordVisibleTraceForwardImpl,
          projectionCoordCachingLoggingImpl, hcache,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
          SourceProjectionLog.log12, ProjectionObservationState.log12,
          Functor.map_map]
        have hlazy := projectionCoordLazyRandomImpl_nonce_run_miss
          nonce state.2 hcache
        calc
          _ = (fun result : Projection12Value × ProjectionCoordCache =>
                (result.1,
                  sourceProjectionLogCacheToObservationState
                    (state.1.log12 nonce result.1, result.2))) <$>
              ((fun value : Projection12Value =>
                (value, (state.2.1, state.2.2.cacheQuery nonce value))) <$>
                  ($ᵗ Projection12Value)) := congrArg
                    (Functor.map fun result :
                      Projection12Value × ProjectionCoordCache =>
                        (result.1,
                          sourceProjectionLogCacheToObservationState
                            (state.1.log12 nonce result.1, result.2))) hlazy
          _ = _ := by
            simp only [Functor.map_map]
            rfl
      | some value =>
        simp [projectionCoordVisibleTraceLazyImpl,
          sourceProjectionLogCacheToObservationState,
          projectionCoordVisibleTraceForwardImpl,
          projectionCoordCachingLoggingImpl, hcache,
          QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
          SourceProjectionLog.log12, ProjectionObservationState.log12,
          Functor.map_map]
        have hlazy := projectionCoordLazyRandomImpl_nonce_run_hit
          nonce state.2 value hcache
        have heq := queryCache_cacheQuery_eq_of_some state.2.2 nonce value hcache
        calc
          _ = (fun result : Projection12Value × ProjectionCoordCache =>
                (result.1,
                  sourceProjectionLogCacheToObservationState
                    (state.1.log12 nonce result.1, result.2))) <$>
              pure (value, state.2) := congrArg
                (Functor.map fun result : Projection12Value × ProjectionCoordCache =>
                  (result.1,
                    sourceProjectionLogCacheToObservationState
                      (state.1.log12 nonce result.1, result.2))) hlazy
          _ = _ := by
            simp [sourceProjectionLogCacheToObservationState,
              SourceProjectionLog.log12, heq]

/-- Whole-run exact state-map bridge from separated visible-log/lazy-cache state to the
combined observation state. -/
theorem projectionCoordVisibleTraceLazyImpl_simulateQ_toObservation
    {alpha : Type} (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (state : SourceProjectionLog × ProjectionCoordCache) :
    Prod.map id sourceProjectionLogCacheToObservationState <$>
        (simulateQ projectionCoordVisibleTraceLazyImpl computation).run state =
      (simulateQ projectionCoordCachingLoggingImpl computation).run
        (sourceProjectionLogCacheToObservationState state) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq
    projectionCoordVisibleTraceLazyImpl projectionCoordCachingLoggingImpl
    sourceProjectionLogCacheToObservationState
    projectionCoordVisibleTraceLazyImpl_toObservation_query computation state

/-- Forget the cache while retaining precisely the two source-visible observation lists. -/
def projectionObservationStateToSourceProjectionLog
    (state : ProjectionObservationState) : SourceProjectionLog :=
  ⟨state.observations32, state.observations12⟩

@[simp] theorem projectionObservationStateToSourceProjectionLog_stateMap
    (state : SourceProjectionLog × ProjectionCoordCache) :
    projectionObservationStateToSourceProjectionLog
      (sourceProjectionLogCacheToObservationState state) = state.1 := by
  rfl

/-- Running the explicit visible trace through the pair cache has exactly the same
output-plus-visible-log law as the combined observation handler. The final caches are erased. -/
theorem projectionCoordVisibleTraceLazyImpl_outputLog_eq_observation
    {alpha : Type} (computation : OracleComp ProjectionCoordChallengeSpec alpha)
    (log : SourceProjectionLog) (cache : ProjectionCoordCache) :
    (simulateQ projectionCoordLazyRandomImpl
        ((simulateQ projectionCoordVisibleTraceForwardImpl computation).run log)).run' cache =
      Prod.map id projectionObservationStateToSourceProjectionLog <$>
        (simulateQ projectionCoordCachingLoggingImpl computation).run
          (sourceProjectionLogCacheToObservationState (log, cache)) := by
  have hflatten := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    projectionCoordLazyRandomImpl projectionCoordVisibleTraceForwardImpl
    computation log cache
  have hflattenOutput := congrArg (Functor.map Prod.fst) hflatten
  have hstate := projectionCoordVisibleTraceLazyImpl_simulateQ_toObservation
    computation (log, cache)
  have hstateOutput := congrArg
    (Functor.map (Prod.map id projectionObservationStateToSourceProjectionLog)) hstate
  calc
    _ = (fun result : alpha × (SourceProjectionLog × ProjectionCoordCache) =>
          (result.1, result.2.1)) <$>
        (simulateQ projectionCoordVisibleTraceLazyImpl computation).run (log, cache) := by
      simpa only [StateT.run'_eq, projectionCoordVisibleTraceLazyImpl,
        Functor.map_map, Function.comp_apply] using hflattenOutput
    _ = _ := by
      simpa only [Functor.map_map, Function.comp_apply,
        projectionObservationStateToSourceProjectionLog_stateMap,
        Prod.map, id_eq] using hstateOutput

/-! ## Full-random to logged-birthday experiment -/

/-- Deferred-coordinate random experiment, retaining the adversary bit and exact source log while
discarding the pair cache. -/
noncomputable def sourceProjectionObservedDeferredRandomRun
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    ProbComp (Bool × SourceProjectionLog) :=
  (simulateQ projectionCoordLazyRandomImpl
    (sourceKdfCoordinateObservedMain adversary)).run' (∅, ∅)

/-- The selective source observation computation is exactly coordinate forwarding followed by
one-coordinate-at-a-time visible logging. -/
theorem sourceKdfCoordinateObservedMain_eq_visibleTrace
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    sourceKdfCoordinateObservedMain adversary =
      (simulateQ projectionCoordVisibleTraceForwardImpl
        (simulateQ sourceKdfCoordinateForwardImpl adversary.main)).run
          emptySourceProjectionLog := by
  unfold sourceKdfCoordinateObservedMain
  rw [← projectionCoordVisibleTrace_comp_sourceKdfCoordinateForwardImpl]
  simp only [QueryImpl.simulateQ_compose]

/-- The deferred source-visible experiment is exactly the existing logged birthday experiment
after forgetting its cache. -/
theorem sourceProjectionObservedDeferredRandomRun_eq_observed
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    sourceProjectionObservedDeferredRandomRun adversary =
      Prod.map id projectionObservationStateToSourceProjectionLog <$>
        projectionCollisionObservedRandomRun adversary := by
  unfold sourceProjectionObservedDeferredRandomRun
  rw [sourceKdfCoordinateObservedMain_eq_visibleTrace]
  unfold projectionCollisionObservedRandomRun
  simpa only [sourceProjectionLogCacheToObservationState_empty] using
    (projectionCoordVisibleTraceLazyImpl_outputLog_eq_observation
      (simulateQ sourceKdfCoordinateForwardImpl adversary.main)
      emptySourceProjectionLog (∅, ∅))

/-- The complete-stream lazy random oracle and the deferred pair-cache experiment have identical
output-plus-source-log distributions for every adaptively chosen source computation. -/
theorem evalDist_sourceProjectionObservedFullRandom_eq_deferred
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    evalDist (sourceProjectionObservedFullRandomRun adversary) =
      evalDist (sourceProjectionObservedDeferredRandomRun adversary) := by
  unfold sourceProjectionObservedFullRandomRun
    sourceProjectionObservedDeferredRandomRun
  calc
    evalDist ((simulateQ fixedHkdfSha512JointStreamRandomImpl
        (sourceKdfStreamObservedMain adversary)).run' ∅) =
      evalDist ((simulateQ
        (projectionCoordUnifiedRandomImpl ∘ₛ jointKdfStreamEagerCoordinateForwardImpl)
          (sourceKdfStreamObservedMain adversary)).run'
            (jointKdfStreamCacheToUnifiedProjectionCoordCache ∅)) :=
      evalDist_fixedJointStreamRandom_eq_eagerCoordinates
        (sourceKdfStreamObservedMain adversary) ∅
    _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        (sourceKdfEagerCoordinateObservedMain adversary)).run' ∅) := by
      simp only [QueryImpl.simulateQ_compose,
        simulateQ_jointKdfStreamEagerCoordinate_sourceKdfStreamObservedMain]
      have hempty : jointKdfStreamCacheToUnifiedProjectionCoordCache ∅ = ∅ := by
        funext query
        rcases query with coord | nonce
        · simp [jointKdfStreamCacheToUnifiedProjectionCoordCache]
        · simp [jointKdfStreamCacheToUnifiedProjectionCoordCache]
      rw [hempty]
    _ = evalDist ((simulateQ projectionCoordUnifiedRandomImpl
        (sourceKdfCoordinateObservedMain adversary)).run' ∅) :=
      evalDist_sourceKdfEagerCoordinate_eq_deferred adversary.main
        emptySourceProjectionLog ∅
    _ = evalDist ((simulateQ projectionCoordLazyRandomImpl
        (sourceKdfCoordinateObservedMain adversary)).run' (∅, ∅)) := by
      rw [projectionCoordUnifiedRandomImpl_simulateQ_run'_eq_toPair]
      rfl

/-- Collision event over the exact source-visible output log. The adversary's Boolean result is
retained by normalization but is irrelevant to this event. -/
def SourceProjectionCollisionEvent
    (result : Bool × SourceProjectionLog) : Prop :=
  result.2.HasCollision

/-- The full-stream random source event is exactly the cache collision event bounded above. -/
theorem probEvent_sourceProjectionCollision_fullRandom_eq_cache
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedFullRandomRun adversary] =
      Pr[ProjectionCollisionEvent | projectionCollisionRandomRun adversary] := by
  calc
    Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedFullRandomRun adversary] =
      Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedDeferredRandomRun adversary] :=
      probEvent_congr' (fun _ _ => Iff.rfl)
        (evalDist_sourceProjectionObservedFullRandom_eq_deferred adversary)
    _ = Pr[ProjectionObservedCollisionEvent |
        projectionCollisionObservedRandomRun adversary] := by
      rw [sourceProjectionObservedDeferredRandomRun_eq_observed, probEvent_map]
      rfl
    _ = Pr[ProjectionCollisionEvent | projectionCollisionRandomRun adversary] :=
      probEvent_projectionObservedCollision_eq_cache adversary

/-- Exact source-accounted collision bound for the complete-stream random world. Uniform
adversary samples are absent from both birthday terms. -/
theorem sourceProjectionCollision_fullRandom_le
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedFullRandomRun adversary] ≤
      (Nat.choose (sourceQ32 r i s pF pS) 2 : ℝ≥0∞) /
          (2 ^ 256 : ℝ≥0∞) +
        (Nat.choose (sourceQN s pN) 2 : ℝ≥0∞) /
          (2 ^ 96 : ℝ≥0∞) := by
  rw [probEvent_sourceProjectionCollision_fullRandom_eq_cache]
  exact sourceProjectionCollision_random_le adversary

/-! ## One fixed-HKDF reduction and exact challenger accounting -/

/-- One observation-forwarding step charges a uniform primitive query exactly when the source
query is adversary-controlled uniform sampling. -/
theorem sourceKdfStreamObservationForwardImpl_uniform_bound_step
    (query : SourceKdfAdversarySpec.Domain) (log : SourceProjectionLog) :
    ((sourceKdfStreamObservationForwardImpl query).run log).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery
      (if IsSourceKdfUniformQuery query then 1 else 0) := by
  rcases query with randomQuery | sourceQuery
  · simp only [sourceKdfStreamObservationForwardImpl, StateT.run_mk,
      IsSourceKdfUniformQuery, if_true]
    change (liftM (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
      OracleComp FixedHkdfSha512JointStreamSpec
        (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
          IsFixedHkdfSha512UniformQuery 1
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512UniformQuery]
  · simp only [sourceKdfStreamObservationForwardImpl, StateT.run_mk,
      IsSourceKdfUniformQuery, if_false, bind_pure_comp]
    change ((fun stream : FixedHkdfSha512JointStreamSpec.Range
        (.inr sourceQuery.address) =>
      (sourceQuery.output stream, log.record sourceQuery stream)) <$>
        (liftM (FixedHkdfSha512JointStreamSpec.query (.inr sourceQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr sourceQuery.address)))).IsQueryBoundP
            IsFixedHkdfSha512UniformQuery 0
    rw [OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512UniformQuery]

/-- One observation-forwarding step charges exactly one complete-stream primitive query for each
source KDF call and none for adversary-controlled uniform sampling. -/
theorem sourceKdfStreamObservationForwardImpl_stream_bound_step
    (query : SourceKdfAdversarySpec.Domain) (log : SourceProjectionLog) :
    ((sourceKdfStreamObservationForwardImpl query).run log).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery
      (if IsSourceKdfCallQuery query then 1 else 0) := by
  rcases query with randomQuery | sourceQuery
  · simp only [sourceKdfStreamObservationForwardImpl, StateT.run_mk,
      IsSourceKdfCallQuery, if_false]
    change (liftM (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
      OracleComp FixedHkdfSha512JointStreamSpec
        (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
          IsFixedHkdfSha512StreamQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512StreamQuery]
  · simp only [sourceKdfStreamObservationForwardImpl, StateT.run_mk,
      IsSourceKdfCallQuery, if_true, bind_pure_comp]
    change ((fun stream : FixedHkdfSha512JointStreamSpec.Range
        (.inr sourceQuery.address) =>
      (sourceQuery.output stream, log.record sourceQuery stream)) <$>
        (liftM (FixedHkdfSha512JointStreamSpec.query (.inr sourceQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr sourceQuery.address)))).IsQueryBoundP
            IsFixedHkdfSha512StreamQuery 1
    rw [OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512StreamQuery]

/-- Every source-shaped call uses one of the two exact production address images. -/
theorem sourceKdfQuery_address_not_untyped (query : SourceKdfQuery) :
    ¬IsFixedHkdfSha512UntypedStreamQuery (.inr query.address) := by
  rcases query with input | input | input | ⟨input, domain, projection⟩
  · simp only [SourceKdfQuery.address, FixedHkdfDomain.address_pqxdh,
      IsFixedHkdfSha512UntypedStreamQuery, not_and_or]
    exact Or.inl (not_not_intro rfl)
  · simp only [SourceKdfQuery.address, FixedHkdfDomain.address_ratchet,
      IsFixedHkdfSha512UntypedStreamQuery, not_and_or]
    exact Or.inr (not_not_intro rfl)
  · simp only [SourceKdfQuery.address, FixedHkdfDomain.address_ratchet,
      IsFixedHkdfSha512UntypedStreamQuery, not_and_or]
    exact Or.inr (not_not_intro rfl)
  · cases domain with
    | pqxdh =>
        simp only [SourceKdfQuery.address, JointKdfViewQuery.address,
          FixedHkdfDomain.address_pqxdh,
          IsFixedHkdfSha512UntypedStreamQuery, not_and_or]
        exact Or.inl (not_not_intro rfl)
    | ratchet =>
        simp only [SourceKdfQuery.address, JointKdfViewQuery.address,
          FixedHkdfDomain.address_ratchet,
          IsFixedHkdfSha512UntypedStreamQuery, not_and_or]
        exact Or.inr (not_not_intro rfl)

/-- No observation-forwarding step emits a raw stream address outside the exact `INFO_PQ` and
`INFO_R` production images. -/
theorem sourceKdfStreamObservationForwardImpl_no_untyped_step
    (query : SourceKdfAdversarySpec.Domain) (log : SourceProjectionLog) :
    ((sourceKdfStreamObservationForwardImpl query).run log).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  rcases query with randomQuery | sourceQuery
  · simp only [sourceKdfStreamObservationForwardImpl, StateT.run_mk]
    change (liftM (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
      OracleComp FixedHkdfSha512JointStreamSpec
        (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
          IsFixedHkdfSha512UntypedStreamQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512UntypedStreamQuery]
  · simp only [sourceKdfStreamObservationForwardImpl, StateT.run_mk,
      bind_pure_comp]
    change ((fun stream : FixedHkdfSha512JointStreamSpec.Range
        (.inr sourceQuery.address) =>
      (sourceQuery.output stream, log.record sourceQuery stream)) <$>
        (liftM (FixedHkdfSha512JointStreamSpec.query (.inr sourceQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr sourceQuery.address)))).IsQueryBoundP
            IsFixedHkdfSha512UntypedStreamQuery 0
    rw [OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff]
    exact fun hquery => (sourceKdfQuery_address_not_untyped sourceQuery hquery).elim

/-- The observed complete-stream computation preserves the adversary's uniform-query cap. -/
theorem SourceKdfAdversary.streamObservedUniformQueryBound
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceKdfStreamObservedMain adversary).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery qU := by
  unfold sourceKdfStreamObservedMain
  exact adversary.uniformQueryBound.simulateQ_run_StateT_of_step
    sourceKdfStreamObservationForwardImpl_uniform_bound_step
    emptySourceProjectionLog

/-- The observed computation makes one challenger-facing complete-stream query per source call. -/
theorem SourceKdfAdversary.streamObservedStreamQueryBound
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceKdfStreamObservedMain adversary).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery (sourceQStream r i s pF pS pN) := by
  unfold sourceKdfStreamObservedMain
  exact adversary.sourceCallQueryBound.simulateQ_run_StateT_of_step
    sourceKdfStreamObservationForwardImpl_stream_bound_step
    emptySourceProjectionLog

/-- The whole observed reduction emits only exact `INFO_PQ` and `INFO_R` addresses. -/
theorem SourceKdfAdversary.streamObservedNoUntypedQueries
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceKdfStreamObservedMain adversary).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  unfold sourceKdfStreamObservedMain
  have hfalse : adversary.main.IsQueryBoundP (fun _ => False) 0 :=
    OracleComp.isQueryBoundP_false adversary.main 0
  refine hfalse.simulateQ_run_StateT_of_step ?_ emptySourceProjectionLog
  intro query log
  simpa using sourceKdfStreamObservationForwardImpl_no_untyped_step query log

/-- Boolean primitive distinguisher that reports exactly whether the source-visible projection
log contains a same-width collision between distinct canonical identities. -/
noncomputable def sourceProjectionCollisionBit
    (result : Bool × SourceProjectionLog) : Bool :=
  @decide (SourceProjectionCollisionEvent result) (Classical.propDecidable _)

/-- Boolean primitive distinguisher that reports exactly whether the source-visible projection
log contains a same-width collision between distinct canonical identities. -/
noncomputable def sourceProjectionCollisionReductionMain
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    OracleComp FixedHkdfSha512JointStreamSpec Bool :=
  sourceProjectionCollisionBit <$>
    sourceKdfStreamObservedMain adversary

/-- Package the single collision bit as one fixed-HKDF joint-stream distinguisher. -/
noncomputable def sourceProjectionCollisionReduction
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    FixedHkdfSha512JointStreamAdversary qU
      (sourceQStream r i s pF pS pN) where
  main := sourceProjectionCollisionReductionMain adversary
  uniformQueryBound := by
    unfold sourceProjectionCollisionReductionMain
    rw [OracleComp.isQueryBoundP_map_iff]
    exact adversary.streamObservedUniformQueryBound
  streamQueryBound := by
    unfold sourceProjectionCollisionReductionMain
    rw [OracleComp.isQueryBoundP_map_iff]
    exact adversary.streamObservedStreamQueryBound

/-- The packaged distinguisher has the exact challenger-facing `qU` uniform-query cap. -/
theorem sourceProjectionCollisionReduction_uniform_query_bound
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceProjectionCollisionReduction adversary).main.IsQueryBoundP
      IsFixedHkdfSha512UniformQuery qU :=
  (sourceProjectionCollisionReduction adversary).uniformQueryBound

/-- The packaged distinguisher has the exact factor-one source-call stream cap. -/
theorem sourceProjectionCollisionReduction_stream_query_bound
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceProjectionCollisionReduction adversary).main.IsQueryBoundP
      IsFixedHkdfSha512StreamQuery (sourceQStream r i s pF pS pN) :=
  (sourceProjectionCollisionReduction adversary).streamQueryBound

/-- The collision-bit map introduces no untyped stream address. -/
theorem sourceProjectionCollisionReduction_no_untyped_stream_queries
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceProjectionCollisionReduction adversary).main.IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  unfold sourceProjectionCollisionReduction sourceProjectionCollisionReductionMain
  rw [OracleComp.isQueryBoundP_map_iff]
  exact adversary.streamObservedNoUntypedQueries

/-- The factor-one challenger query accounting is `qU + sourceQStream`. Lazy-random
implementation sampling is internal to the challenger and is not added here. -/
theorem sourceProjectionCollisionReduction_totalQueryBound
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    (sourceProjectionCollisionReduction adversary).main.IsTotalQueryBound
      (qU + sourceQStream r i s pF pS pN) :=
  (sourceProjectionCollisionReduction adversary).totalQueryBound

/-- Real fixed-source run retaining the adversary output and exact visible projection log. -/
def sourceProjectionObservedRealRun
    (source : FixedHkdfSha512NoSaltSource) {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    ProbComp (Bool × SourceProjectionLog) :=
  simulateQ (fixedHkdfSha512JointStreamRealImpl source)
    (sourceKdfStreamObservedMain adversary)

/-- The reduction's real experiment is exactly the collision bit mapped from the real visible
source log. -/
theorem fixedHkdfSha512JointStreamRealExp_collisionReduction
    (source : FixedHkdfSha512NoSaltSource) {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    fixedHkdfSha512JointStreamRealExp source
        (sourceProjectionCollisionReduction adversary) =
      sourceProjectionCollisionBit <$>
        sourceProjectionObservedRealRun source adversary := by
  unfold fixedHkdfSha512JointStreamRealExp
    sourceProjectionCollisionReduction sourceProjectionCollisionReductionMain
    sourceProjectionObservedRealRun
  rw [simulateQ_map]

/-- The reduction's random experiment is exactly the collision bit mapped from the normalized
full-stream random source log. -/
theorem fixedHkdfSha512JointStreamRandomExp_collisionReduction
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    fixedHkdfSha512JointStreamRandomExp
        (sourceProjectionCollisionReduction adversary) =
      sourceProjectionCollisionBit <$>
        sourceProjectionObservedFullRandomRun adversary := by
  unfold fixedHkdfSha512JointStreamRandomExp
    sourceProjectionCollisionReduction sourceProjectionCollisionReductionMain
    sourceProjectionObservedFullRandomRun
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- Mapping the decidable collision predicate to a Boolean preserves exactly its event
probability. -/
theorem probOutput_collisionBit_eq_probEvent
    (game : ProbComp (Bool × SourceProjectionLog)) :
    Pr[= true |
      sourceProjectionCollisionBit <$> game] =
      Pr[SourceProjectionCollisionEvent | game] := by
  rw [← probEvent_eq_eq_probOutput, probEvent_map]
  apply OracleComp.probEvent_congr' _ rfl
  intro result _
  simp only [Function.comp_apply, sourceProjectionCollisionBit,
    decide_eq_true_eq]

/-- The reduction's real `true` probability is the exact real source-visible collision event. -/
theorem probOutput_collisionReduction_real_eq_sourceEvent
    (source : FixedHkdfSha512NoSaltSource) {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[= true | fixedHkdfSha512JointStreamRealExp source
        (sourceProjectionCollisionReduction adversary)] =
      Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedRealRun source adversary] := by
  rw [fixedHkdfSha512JointStreamRealExp_collisionReduction]
  exact probOutput_collisionBit_eq_probEvent _

/-- The reduction's random `true` probability is the exact random source-visible collision
event, after the full-stream/deferred normalization. -/
theorem probOutput_collisionReduction_random_eq_sourceEvent
    {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[= true | fixedHkdfSha512JointStreamRandomExp
        (sourceProjectionCollisionReduction adversary)] =
      Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedFullRandomRun adversary] := by
  rw [fixedHkdfSha512JointStreamRandomExp_collisionReduction]
  exact probOutput_collisionBit_eq_probEvent _

/-- Final source-shaped computational projection-collision bound.

The named fixed HKDF-SHA-512/no-salt joint-stream advantage is charged exactly once. The random
world then pays one 256-bit birthday term over all visible first/second identities and one 96-bit
birthday term over visible nonce identities. No claim about HKDF, HMAC, or SHA-512 internals is
made here. -/
theorem sourceProjectionCollision_real_le
    (source : FixedHkdfSha512NoSaltSource) {qU r i s pF pS pN : ℕ}
    (adversary : SourceKdfAdversary qU r i s pF pS pN) :
    Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedRealRun source adversary] ≤
      ENNReal.ofReal (fixedHkdfSha512JointStreamAdvantage source
          (sourceProjectionCollisionReduction adversary)) +
        (Nat.choose (sourceQ32 r i s pF pS) 2 : ℝ≥0∞) /
          (2 ^ 256 : ℝ≥0∞) +
        (Nat.choose (sourceQN s pN) 2 : ℝ≥0∞) /
          (2 ^ 96 : ℝ≥0∞) := by
  let reduction := sourceProjectionCollisionReduction adversary
  calc
    Pr[SourceProjectionCollisionEvent |
        sourceProjectionObservedRealRun source adversary] =
      Pr[= true | fixedHkdfSha512JointStreamRealExp source reduction] := by
        rw [probOutput_collisionReduction_real_eq_sourceEvent]
    _ ≤ Pr[= true | fixedHkdfSha512JointStreamRandomExp reduction] +
        ENNReal.ofReal
          ((fixedHkdfSha512JointStreamRealExp source reduction).boolDistAdvantage
            (fixedHkdfSha512JointStreamRandomExp reduction)) :=
      ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage _ _
    _ = Pr[SourceProjectionCollisionEvent |
          sourceProjectionObservedFullRandomRun adversary] +
        ENNReal.ofReal (fixedHkdfSha512JointStreamAdvantage source reduction) := by
      rw [probOutput_collisionReduction_random_eq_sourceEvent]
      rfl
    _ ≤ ((Nat.choose (sourceQ32 r i s pF pS) 2 : ℝ≥0∞) /
          (2 ^ 256 : ℝ≥0∞) +
        (Nat.choose (sourceQN s pN) 2 : ℝ≥0∞) /
          (2 ^ 96 : ℝ≥0∞)) +
        ENNReal.ofReal (fixedHkdfSha512JointStreamAdvantage source reduction) :=
      add_le_add (sourceProjectionCollision_fullRandom_le adversary) le_rfl
    _ = _ := by
      dsimp only [reduction]
      ac_rfl

/--
info: 'BeaconcryptCore.Computational.PqxdhProjectionCollisions.sourceProjectionCollision_real_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sourceProjectionCollision_real_le

end BeaconcryptCore.Computational.PqxdhProjectionCollisions
