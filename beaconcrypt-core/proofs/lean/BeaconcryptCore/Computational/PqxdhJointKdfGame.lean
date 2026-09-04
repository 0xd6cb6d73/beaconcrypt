import BeaconcryptCore.Computational.PqxdhJointKdf
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Bounded real-or-random game for the joint BeaconCrypt HKDF stream

This module exposes exactly the two production HKDF-SHA-512/no-salt domains and the three public stream projections used by the symbolic model.
Every projection at one exact `(input, domain)` address is backed by one shared 76-byte stream.

The real world calls the fixed production source through `Pqxdh.Crypto.hkdf` and carries the separate functional prefix-consistency contract from `PqxdhJointKdf`.
The random world lazily samples one 76-byte stream on a cache miss and returns that same stream on every hit.

The named joint-stream real-or-random advantage is the primitive endpoint of this component reduction.
It is not an ordinary secret-key PRF assumption, and this module proves no property of HKDF, HMAC, or SHA-512 internals.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhJointKdfGame

open PqxdhJointKdf

/-- The only two public HKDF domains fixed by the BeaconCrypt source. -/
inductive FixedHkdfDomain where
  | pqxdh
  | ratchet
deriving DecidableEq

/-- Map a typed public domain to its exact production `info` bytes. -/
def FixedHkdfDomain.info : FixedHkdfDomain → Pqxdh.Bytes
  | .pqxdh => Pqxdh.INFO_PQ
  | .ratchet => Pqxdh.INFO_R

@[simp] theorem FixedHkdfDomain.info_pqxdh :
    FixedHkdfDomain.pqxdh.info = Pqxdh.INFO_PQ := by
  rfl

@[simp] theorem FixedHkdfDomain.info_ratchet :
    FixedHkdfDomain.ratchet.info = Pqxdh.INFO_R := by
  rfl

/-- The typed domain map is injective because the two exact source labels differ. -/
theorem FixedHkdfDomain.info_injective :
    Function.Injective FixedHkdfDomain.info := by
  intro left right equality
  cases left <;> cases right
  · rfl
  · exact (Pqxdh.INFO_PQ_ne_INFO_R equality).elim
  · exact (Pqxdh.INFO_PQ_ne_INFO_R equality.symm).elim
  · rfl

/-- Map the public `(input, domain)` pair to the one canonical internal stream address. -/
def FixedHkdfDomain.address (domain : FixedHkdfDomain)
    (input : Pqxdh.Bytes) : JointKdfAddress :=
  ⟨domain.info, input⟩

@[simp] theorem FixedHkdfDomain.address_pqxdh (input : Pqxdh.Bytes) :
    FixedHkdfDomain.pqxdh.address input = rootAddress input := by
  rfl

@[simp] theorem FixedHkdfDomain.address_ratchet (input : Pqxdh.Bytes) :
    FixedHkdfDomain.ratchet.address input = ratchetAddress input := by
  rfl

/-- Typed public addresses are equal exactly when both the source domain and input agree. -/
theorem FixedHkdfDomain.address_injective :
    Function.Injective (fun pair : FixedHkdfDomain × Pqxdh.Bytes =>
      pair.1.address pair.2) := by
  rintro ⟨leftDomain, leftInput⟩ ⟨rightDomain, rightInput⟩ equality
  have infoEquality := congrArg JointKdfAddress.info equality
  have domainEquality := FixedHkdfDomain.info_injective infoEquality
  have inputEquality := congrArg JointKdfAddress.input equality
  exact Prod.ext domainEquality inputEquality

/-- The three public positions of the shared production stream. -/
inductive JointKdfProjection where
  | first32
  | second32
  | final12
deriving DecidableEq

/-- Exact byte width returned by each public projection. -/
def JointKdfProjection.width : JointKdfProjection → ℕ
  | .first32 => 32
  | .second32 => 32
  | .final12 => 12

/-- Project a single shared 76-byte answer at the requested public position. -/
def JointKdfProjection.project (projection : JointKdfProjection)
    (stream : JointKdfStream) : List.Vector UInt8 projection.width :=
  match projection with
  | .first32 =>
      ⟨PqxdhJointKdf.first32 stream, PqxdhJointKdf.first32_length stream⟩
  | .second32 =>
      ⟨PqxdhJointKdf.second32 stream, PqxdhJointKdf.second32_length stream⟩
  | .final12 =>
      ⟨PqxdhJointKdf.final12 stream, PqxdhJointKdf.final12_length stream⟩

/-- One public request, ordered like source `hkdf(input, domain)`, plus its projection. -/
structure JointKdfViewQuery where
  input : Pqxdh.Bytes
  domain : FixedHkdfDomain
  projection : JointKdfProjection
deriving DecidableEq

/-- The canonical internal address queried by a public projection request. -/
def JointKdfViewQuery.address (query : JointKdfViewQuery) : JointKdfAddress :=
  query.domain.address query.input

/-- Dependent public query surface with exact 32-, 32-, and 12-byte response widths. -/
def JointKdfViewSpec : OracleSpec JointKdfViewQuery :=
  fun query => List.Vector UInt8 query.projection.width

/-- Apply one public request to the complete stream returned at its canonical address. -/
def JointKdfViewQuery.project (query : JointKdfViewQuery)
    (stream : JointKdfStream) : JointKdfViewSpec.Range query :=
  query.projection.project stream

/-- The fixed production implementation together with its functional prefix contract.

This bundle selects BeaconCrypt's HKDF-SHA-512/no-salt source surface; it does not assert or prove primitive security.
-/
structure FixedHkdfSha512NoSaltSource where
  crypto : Pqxdh.Crypto
  prefixConsistent : ProductionHkdfPrefixConsistent crypto

/-- Public component interface: adversary randomness plus the exact projection surface. -/
abbrev JointKdfViewAdversarySpec := unifSpec + JointKdfViewSpec

/-- Primitive challenge interface: adversary randomness plus one complete stream per address. -/
abbrev FixedHkdfSha512JointStreamSpec := unifSpec + JointKdfRO

/-- The random challenge interprets every complete-stream answer as uniform. -/
noncomputable instance jointKdfROIsUniformSpec : IsUniformSpec JointKdfRO :=
  OracleSpec.IsUniformSpec.ofFintypeInhabited _

/-- Forward every projection through exactly one canonical complete-stream query. -/
def jointKdfViewForwardImpl :
    QueryImpl JointKdfViewAdversarySpec
      (OracleComp FixedHkdfSha512JointStreamSpec) :=
  fun query =>
    match query with
    | .inl randomQuery =>
        liftM (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery))
    | .inr viewQuery => do
        let stream ←
          liftM (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address))
        pure (viewQuery.project stream)

@[simp] theorem jointKdfViewForwardImpl_uniform (query : unifSpec.Domain) :
    jointKdfViewForwardImpl (.inl query) =
      liftM (FixedHkdfSha512JointStreamSpec.query (.inl query)) := by
  rfl

@[simp] theorem jointKdfViewForwardImpl_projection (query : JointKdfViewQuery) :
    jointKdfViewForwardImpl (.inr query) = (do
      let stream ←
        liftM (FixedHkdfSha512JointStreamSpec.query (.inr query.address))
      pure (query.project stream)) := by
  rfl

/-- Real complete-stream handler fixed by the source implementation. -/
def fixedHkdfSha512JointStreamRealImpl
    (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl FixedHkdfSha512JointStreamSpec ProbComp :=
  let streamImpl : QueryImpl JointKdfRO ProbComp :=
    fun address => pure (productionStream source.crypto address)
  QueryImpl.ofLift unifSpec ProbComp + streamImpl

/-- The canonical lazy random complete-stream handler. -/
noncomputable def jointKdfLazyRandomStreamImpl :
    QueryImpl JointKdfRO (StateT JointKdfRO.QueryCache ProbComp) :=
  JointKdfRO.randomOracle

/-- Random complete-stream handler, transparent on adversary randomness. -/
noncomputable def fixedHkdfSha512JointStreamRandomImpl :
    QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT JointKdfRO.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT JointKdfRO.QueryCache ProbComp) +
    jointKdfLazyRandomStreamImpl

/-- Production component handler obtained by projecting complete HKDF streams. -/
def jointKdfViewRealImpl (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl JointKdfViewAdversarySpec ProbComp :=
  fixedHkdfSha512JointStreamRealImpl source ∘ₛ jointKdfViewForwardImpl

/-- Lazy-random component handler obtained by projecting cached complete streams. -/
noncomputable def jointKdfViewRandomImpl :
    QueryImpl JointKdfViewAdversarySpec
      (StateT JointKdfRO.QueryCache ProbComp) :=
  fixedHkdfSha512JointStreamRandomImpl ∘ₛ jointKdfViewForwardImpl

/-- Changing only the requested projection leaves the canonical stream address unchanged. -/
theorem jointKdfViewQuery_address_independent_of_projection
    (input : Pqxdh.Bytes) (domain : FixedHkdfDomain)
    (left right : JointKdfProjection) :
    (JointKdfViewQuery.mk input domain left).address =
      (JointKdfViewQuery.mk input domain right).address := by
  rfl

/-- A real primitive stream query is exactly the fixed 76-byte production call. -/
@[simp] theorem fixedHkdfSha512JointStreamRealImpl_stream
    (source : FixedHkdfSha512NoSaltSource) (address : JointKdfAddress) :
    fixedHkdfSha512JointStreamRealImpl source (.inr address) =
      pure (productionStream source.crypto address) := by
  rfl

/-- The production component returns the requested slice of its one complete stream. -/
@[simp] theorem jointKdfViewRealImpl_projection
    (source : FixedHkdfSha512NoSaltSource) (query : JointKdfViewQuery) :
    jointKdfViewRealImpl source (.inr query) =
      pure (query.project (productionStream source.crypto query.address)) := by
  simp [jointKdfViewRealImpl, fixedHkdfSha512JointStreamRealImpl,
    jointKdfViewForwardImpl]

/-- The random component projects the one lazy stream queried at the public request's address. -/
@[simp] theorem jointKdfViewRandomImpl_projection
    (query : JointKdfViewQuery) :
    jointKdfViewRandomImpl (.inr query) =
      query.project <$> jointKdfLazyRandomStreamImpl query.address := by
  simp [jointKdfViewRandomImpl, fixedHkdfSha512JointStreamRandomImpl,
    jointKdfViewForwardImpl]

/-- On a cache hit, the lazy handler returns the stored stream with unchanged cache and no fresh sample. -/
theorem jointKdfLazyRandomStreamImpl_run_hit
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    (jointKdfLazyRandomStreamImpl address).run cache =
      pure (stream, cache) := by
  unfold jointKdfLazyRandomStreamImpl OracleSpec.randomOracle
  exact QueryImpl.withCaching_run_some uniformSampleImpl hcache

/-- On a cache miss, the lazy handler samples one complete stream and installs it once. -/
theorem jointKdfLazyRandomStreamImpl_run_miss
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (hcache : cache address = none) :
    (jointKdfLazyRandomStreamImpl address).run cache =
      (fun stream : JointKdfStream =>
        (stream, cache.cacheQuery address stream)) <$> ($ᵗ JointKdfStream) := by
  unfold jointKdfLazyRandomStreamImpl OracleSpec.randomOracle
  exact QueryImpl.withCaching_run_none uniformSampleImpl hcache

/-- A public projection hit returns a slice of the stored stream and leaves the cache unchanged. -/
theorem jointKdfViewRandomImpl_projection_run_hit
    (query : JointKdfViewQuery) (cache : JointKdfRO.QueryCache)
    (stream : JointKdfStream) (hcache : cache query.address = some stream) :
    (jointKdfViewRandomImpl (.inr query)).run cache =
      pure (query.project stream, cache) := by
  apply Eq.trans (congrArg (fun computation => computation.run cache)
    (jointKdfViewRandomImpl_projection query))
  change ((query.project <$> jointKdfLazyRandomStreamImpl query.address) :
    StateT JointKdfRO.QueryCache ProbComp (JointKdfViewSpec.Range query)).run cache = _
  rw [StateT.run_map,
    jointKdfLazyRandomStreamImpl_run_hit query.address cache stream hcache]
  rfl

/-- A public projection miss samples and stores one stream before returning only its requested slice. -/
theorem jointKdfViewRandomImpl_projection_run_miss
    (query : JointKdfViewQuery) (cache : JointKdfRO.QueryCache)
    (hcache : cache query.address = none) :
    (jointKdfViewRandomImpl (.inr query)).run cache =
      (fun stream : JointKdfStream =>
        (query.project stream, cache.cacheQuery query.address stream)) <$>
          ($ᵗ JointKdfStream) := by
  apply Eq.trans (congrArg (fun computation => computation.run cache)
    (jointKdfViewRandomImpl_projection query))
  change ((query.project <$> jointKdfLazyRandomStreamImpl query.address) :
    StateT JointKdfRO.QueryCache ProbComp (JointKdfViewSpec.Range query)).run cache = _
  rw [StateT.run_map,
    jointKdfLazyRandomStreamImpl_run_miss query.address cache hcache,
    Functor.map_map]

/-- Sampling one uniform byte consumes one underlying uniform query. -/
theorem uniformUInt8_isTotalQueryBound :
    ($ᵗ UInt8).IsTotalQueryBound 1 := by
  change IsTotalQueryBound
    ((@FinEnum.equiv UInt8 FinEnum.instUInt8).symm <$>
      ($[0..255] : ProbComp (Fin 256))) 1
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff]
  change OracleComp.IsQueryBound
    (liftM (unifSpec.query 255) : ProbComp (Fin 256)) 1
      (fun _ budget => 0 < budget) (fun _ budget => budget - 1)
  rw [OracleComp.isQueryBound_query_iff]
  omega

/-- Sampling a fixed byte vector consumes one underlying uniform query per byte. -/
theorem uniformFixedBytes_isTotalQueryBound (n : ℕ) :
    ($ᵗ List.Vector UInt8 n).IsTotalQueryBound n := by
  have hvector : ($ᵗ Vector UInt8 n).IsTotalQueryBound n := by
    induction n with
    | zero =>
        change IsTotalQueryBound (pure #v[]) 0
        trivial
    | succ n ih =>
        change IsTotalQueryBound
          (Vector.push <$> ($ᵗ Vector UInt8 n) <*> ($ᵗ UInt8)) (n + 1)
        exact OracleComp.isTotalQueryBound_seq
          ((OracleComp.isQueryBound_map_iff _ _ _ _ _).2 ih)
          uniformUInt8_isTotalQueryBound
  change IsTotalQueryBound
    (List.Vector.ofFn <$>
      ((fun (bytes : Vector UInt8 n) (index : Fin n) => bytes.get index) <$>
        ($ᵗ Vector UInt8 n))) n
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff, OracleComp.isQueryBound_map_iff]
  exact hvector

/-- Byte-sampling cost charged by one lazy stream query: zero on a hit, 76 on a miss. -/
def jointKdfLazyRandomStreamByteCost
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress) : ℕ :=
  if (cache address).isSome then 0 else 76

@[simp] theorem jointKdfLazyRandomStreamByteCost_of_hit
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    jointKdfLazyRandomStreamByteCost cache address = 0 := by
  simp [jointKdfLazyRandomStreamByteCost, hcache]

@[simp] theorem jointKdfLazyRandomStreamByteCost_of_miss
    (cache : JointKdfRO.QueryCache) (address : JointKdfAddress)
    (hcache : cache address = none) :
    jointKdfLazyRandomStreamByteCost cache address = 76 := by
  simp [jointKdfLazyRandomStreamByteCost, hcache]

/-- A repeated address consumes no fresh uniform-byte query. -/
theorem jointKdfLazyRandomStreamImpl_hit_query_bound
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (stream : JointKdfStream) (hcache : cache address = some stream) :
    ((jointKdfLazyRandomStreamImpl address).run cache).IsTotalQueryBound 0 := by
  rw [jointKdfLazyRandomStreamImpl_run_hit address cache stream hcache]
  trivial

/-- A new address consumes the 76 uniform-byte queries for exactly one complete stream sample. -/
theorem jointKdfLazyRandomStreamImpl_miss_query_bound
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache)
    (hcache : cache address = none) :
    ((jointKdfLazyRandomStreamImpl address).run cache).IsTotalQueryBound 76 := by
  rw [jointKdfLazyRandomStreamImpl_run_miss address cache hcache]
  unfold IsTotalQueryBound
  rw [OracleComp.isQueryBound_map_iff]
  exact uniformFixedBytes_isTotalQueryBound 76

/-- The per-query sampling cap charges 76 bytes only when the canonical address was absent. -/
theorem jointKdfLazyRandomStreamImpl_query_bound
    (address : JointKdfAddress) (cache : JointKdfRO.QueryCache) :
    ((jointKdfLazyRandomStreamImpl address).run cache).IsTotalQueryBound
      (jointKdfLazyRandomStreamByteCost cache address) := by
  cases hcache : cache address with
  | none =>
      rw [jointKdfLazyRandomStreamByteCost_of_miss cache address hcache]
      exact jointKdfLazyRandomStreamImpl_miss_query_bound address cache hcache
  | some stream =>
      rw [jointKdfLazyRandomStreamByteCost_of_hit cache address stream hcache]
      exact jointKdfLazyRandomStreamImpl_hit_query_bound address cache stream hcache

/-- The fixed-source root wrapper is the real stream's root-domain first projection. -/
theorem FixedHkdfSha512NoSaltSource.rootSecret_eq_realStream
    (source : FixedHkdfSha512NoSaltSource) (input : Pqxdh.Bytes) :
    Pqxdh.rootSecret source.crypto input =
      rootProjection
        (productionStream source.crypto (FixedHkdfDomain.pqxdh.address input)) := by
  simpa using rootSecret_eq_rootProjection source.crypto
    source.prefixConsistent input

/-- The fixed-source initialization wrapper is the real stream's two shared ratchet projections. -/
theorem FixedHkdfSha512NoSaltSource.rootChains_eq_realStream
    (source : FixedHkdfSha512NoSaltSource) (input : Pqxdh.Bytes) :
    Pqxdh.rootChains source.crypto input =
      initialProjection
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address input)) := by
  simpa using rootChains_eq_initialProjection source.crypto
    source.prefixConsistent input

/-- Select adversary-controlled uniform-sampling queries on the public view interface. -/
def IsJointKdfViewUniformQuery : JointKdfViewAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsJointKdfViewUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Select public HKDF projection queries on the public view interface. -/
def IsJointKdfViewProjectionQuery : JointKdfViewAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsJointKdfViewProjectionQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Select adversary-controlled uniform-sampling queries on the primitive interface. -/
def IsFixedHkdfSha512UniformQuery :
    FixedHkdfSha512JointStreamSpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsFixedHkdfSha512UniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Select complete-stream queries on the primitive interface. -/
def IsFixedHkdfSha512StreamQuery :
    FixedHkdfSha512JointStreamSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsFixedHkdfSha512StreamQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- Select raw stream requests outside both exact production-domain address images. -/
def IsFixedHkdfSha512UntypedStreamQuery :
    FixedHkdfSha512JointStreamSpec.Domain → Prop
  | .inl _ => False
  | .inr address =>
      address ≠ FixedHkdfDomain.pqxdh.address address.input ∧
        address ≠ FixedHkdfDomain.ratchet.address address.input

instance : DecidablePred IsFixedHkdfSha512UntypedStreamQuery
  | .inl _ => isFalse id
  | .inr address => inferInstanceAs (Decidable
      (address ≠ FixedHkdfDomain.pqxdh.address address.input ∧
        address ≠ FixedHkdfDomain.ratchet.address address.input))

/-- One forwarding step emits no raw address outside the two typed source domains. -/
theorem jointKdfViewForwardImpl_no_untyped_query_step
    (query : JointKdfViewAdversarySpec.Domain) :
    (jointKdfViewForwardImpl query).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  rcases query with randomQuery | viewQuery
  · simp only [jointKdfViewForwardImpl_uniform]
    change (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512UntypedStreamQuery]
  · simp only [jointKdfViewForwardImpl_projection, bind_pure_comp]
    change (viewQuery.project <$> (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range
            (.inr viewQuery.address)))).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0
    rw [OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff
      (p := IsFixedHkdfSha512UntypedStreamQuery)
      (.inr viewQuery.address) 0).2 (by
        intro outside
        exfalso
        rcases viewQuery with ⟨input, domain, projection⟩
        cases domain with
        | pqxdh => exact outside.1 (by
            simp [JointKdfViewQuery.address, FixedHkdfDomain.address])
        | ratchet => exact outside.2 (by
            simp [JointKdfViewQuery.address, FixedHkdfDomain.address]))

/-- Every complete-stream query emitted while forwarding an arbitrary public computation is typed. -/
theorem jointKdfViewForwardImpl_no_untyped_queries {alpha : Type}
    (computation : OracleComp JointKdfViewAdversarySpec alpha) :
    (simulateQ jointKdfViewForwardImpl computation).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  have hfalse : computation.IsQueryBoundP (fun _ => False) 0 :=
    OracleComp.isQueryBoundP_false computation 0
  refine hfalse.simulateQ_of_step ?_ ?_
  · intro query hquery
    exact hquery.elim
  · intro query hquery
    exact jointKdfViewForwardImpl_no_untyped_query_step query

/-- A bounded adaptive Boolean distinguisher for the exact public projection surface. -/
structure JointKdfViewAdversary (qU qKdf : ℕ) where
  main : OracleComp JointKdfViewAdversarySpec Bool
  uniformQueryBound : main.IsQueryBoundP IsJointKdfViewUniformQuery qU
  projectionQueryBound : main.IsQueryBoundP IsJointKdfViewProjectionQuery qKdf

/-- A bounded Boolean distinguisher for the complete-stream primitive challenge. -/
structure FixedHkdfSha512JointStreamAdversary (qU qKdf : ℕ) where
  main : OracleComp FixedHkdfSha512JointStreamSpec Bool
  uniformQueryBound : main.IsQueryBoundP IsFixedHkdfSha512UniformQuery qU
  streamQueryBound : main.IsQueryBoundP IsFixedHkdfSha512StreamQuery qKdf

/-- Separate public-view bounds give the explicit `qU + qKdf` total-query cap. -/
theorem isTotalQueryBound_of_jointKdfView_bounds {alpha : Type}
    {computation : OracleComp JointKdfViewAdversarySpec alpha} {qU qKdf : ℕ}
    (huniform : computation.IsQueryBoundP IsJointKdfViewUniformQuery qU)
    (hprojection : computation.IsQueryBoundP IsJointKdfViewProjectionQuery qKdf) :
    computation.IsTotalQueryBound (qU + qKdf) := by
  induction computation using OracleComp.inductionOn generalizing qU qKdf with
  | pure output => trivial
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at huniform hprojection
      rw [OracleComp.isTotalQueryBound_query_bind_iff]
      rcases query with randomQuery | viewQuery
      · simp [IsJointKdfViewUniformQuery,
          IsJointKdfViewProjectionQuery] at huniform hprojection
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (huniform.2 response) (hprojection response)).mono
          (by omega)
      · simp [IsJointKdfViewUniformQuery,
          IsJointKdfViewProjectionQuery] at huniform hprojection
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (huniform response) (hprojection.2 response)).mono
          (by omega)

/-- Separate primitive bounds give the explicit `qU + qKdf` total-query cap. -/
theorem isTotalQueryBound_of_fixedHkdfSha512JointStream_bounds {alpha : Type}
    {computation : OracleComp FixedHkdfSha512JointStreamSpec alpha}
    {qU qKdf : ℕ}
    (huniform : computation.IsQueryBoundP IsFixedHkdfSha512UniformQuery qU)
    (hstream : computation.IsQueryBoundP IsFixedHkdfSha512StreamQuery qKdf) :
    computation.IsTotalQueryBound (qU + qKdf) := by
  induction computation using OracleComp.inductionOn generalizing qU qKdf with
  | pure output => trivial
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at huniform hstream
      rw [OracleComp.isTotalQueryBound_query_bind_iff]
      rcases query with randomQuery | streamQuery
      · simp [IsFixedHkdfSha512UniformQuery,
          IsFixedHkdfSha512StreamQuery] at huniform hstream
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (huniform.2 response) (hstream response)).mono
          (by omega)
      · simp [IsFixedHkdfSha512UniformQuery,
          IsFixedHkdfSha512StreamQuery] at huniform hstream
        refine ⟨by omega, fun response => ?_⟩
        exact (ih response (huniform response) (hstream.2 response)).mono
          (by omega)

theorem JointKdfViewAdversary.totalQueryBound {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    adversary.main.IsTotalQueryBound (qU + qKdf) :=
  isTotalQueryBound_of_jointKdfView_bounds adversary.uniformQueryBound
    adversary.projectionQueryBound

theorem FixedHkdfSha512JointStreamAdversary.totalQueryBound {qU qKdf : ℕ}
    (adversary : FixedHkdfSha512JointStreamAdversary qU qKdf) :
    adversary.main.IsTotalQueryBound (qU + qKdf) :=
  isTotalQueryBound_of_fixedHkdfSha512JointStream_bounds
    adversary.uniformQueryBound adversary.streamQueryBound

/-- One forwarding step preserves the uniform-query indicator exactly. -/
theorem jointKdfViewForwardImpl_uniform_query_bound_step
    (query : JointKdfViewAdversarySpec.Domain) :
    (jointKdfViewForwardImpl query).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery
      (if IsJointKdfViewUniformQuery query then 1 else 0) := by
  rcases query with randomQuery | viewQuery
  · simp only [jointKdfViewForwardImpl_uniform,
      IsJointKdfViewUniformQuery, if_true]
    change (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery 1
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512UniformQuery]
  · simp only [jointKdfViewForwardImpl_projection,
      IsJointKdfViewUniformQuery, if_false, bind_pure_comp]
    change (viewQuery.project <$> (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range
            (.inr viewQuery.address)))).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery 0
    rw [OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff
      (p := IsFixedHkdfSha512UniformQuery) (.inr viewQuery.address) 0).2
        (by simp [IsFixedHkdfSha512UniformQuery])

/-- One forwarding step preserves the KDF-query indicator exactly. -/
theorem jointKdfViewForwardImpl_stream_query_bound_step
    (query : JointKdfViewAdversarySpec.Domain) :
    (jointKdfViewForwardImpl query).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery
      (if IsJointKdfViewProjectionQuery query then 1 else 0) := by
  rcases query with randomQuery | viewQuery
  · simp only [jointKdfViewForwardImpl_uniform,
      IsJointKdfViewProjectionQuery, if_false]
    change (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSha512StreamQuery]
  · simp only [jointKdfViewForwardImpl_projection,
      IsJointKdfViewProjectionQuery, if_true, bind_pure_comp]
    change (viewQuery.project <$> (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range
            (.inr viewQuery.address)))).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery 1
    rw [OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff
      (p := IsFixedHkdfSha512StreamQuery) (.inr viewQuery.address) 1).2
        (by simp [IsFixedHkdfSha512StreamQuery])

/-- Forwarding preserves the adversary's uniform-query cap without loss. -/
theorem jointKdfViewForwardImpl_uniform_query_bound {alpha : Type}
    {computation : OracleComp JointKdfViewAdversarySpec alpha} {qU : ℕ}
    (hbound : computation.IsQueryBoundP IsJointKdfViewUniformQuery qU) :
    (simulateQ jointKdfViewForwardImpl computation).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery qU := by
  refine hbound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using
      jointKdfViewForwardImpl_uniform_query_bound_step query
  · intro query hquery
    simpa [hquery] using
      jointKdfViewForwardImpl_uniform_query_bound_step query

/-- Forwarding preserves the public KDF-query cap without loss. -/
theorem jointKdfViewForwardImpl_stream_query_bound {alpha : Type}
    {computation : OracleComp JointKdfViewAdversarySpec alpha} {qKdf : ℕ}
    (hbound : computation.IsQueryBoundP IsJointKdfViewProjectionQuery qKdf) :
    (simulateQ jointKdfViewForwardImpl computation).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery qKdf := by
  refine hbound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using
      jointKdfViewForwardImpl_stream_query_bound_step query
  · intro query hquery
    simpa [hquery] using
      jointKdfViewForwardImpl_stream_query_bound_step query

/-- Forward a bounded public-view distinguisher to the complete-stream challenge. -/
def jointKdfViewReduction {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    FixedHkdfSha512JointStreamAdversary qU qKdf where
  main := simulateQ jointKdfViewForwardImpl adversary.main
  uniformQueryBound :=
    jointKdfViewForwardImpl_uniform_query_bound adversary.uniformQueryBound
  streamQueryBound :=
    jointKdfViewForwardImpl_stream_query_bound adversary.projectionQueryBound

/-- The forwarding reduction makes at most the original `qU` uniform queries. -/
theorem jointKdfViewReduction_uniform_query_bound {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    (jointKdfViewReduction adversary).main.IsQueryBoundP
      IsFixedHkdfSha512UniformQuery qU :=
  (jointKdfViewReduction adversary).uniformQueryBound

/-- The forwarding reduction makes exactly one stream query per public projection call, with cap `qKdf`. -/
theorem jointKdfViewReduction_stream_query_bound {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    (jointKdfViewReduction adversary).main.IsQueryBoundP
      IsFixedHkdfSha512StreamQuery qKdf :=
  (jointKdfViewReduction adversary).streamQueryBound

/-- The constructed primitive distinguisher uses only `INFO_PQ` and `INFO_R` stream addresses. -/
theorem jointKdfViewReduction_no_untyped_stream_queries {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    (jointKdfViewReduction adversary).main.IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  exact jointKdfViewForwardImpl_no_untyped_queries adversary.main

/-- The forwarding reduction retains the explicit factor-one total cap `qU + qKdf`. -/
theorem jointKdfViewReduction_totalQueryBound {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    (jointKdfViewReduction adversary).main.IsTotalQueryBound (qU + qKdf) :=
  (jointKdfViewReduction adversary).totalQueryBound

/-- Real fixed-HKDF-SHA-512/no-salt complete-stream experiment. -/
def fixedHkdfSha512JointStreamRealExp
    (source : FixedHkdfSha512NoSaltSource) {qU qKdf : ℕ}
    (adversary : FixedHkdfSha512JointStreamAdversary qU qKdf) :
    ProbComp Bool :=
  simulateQ (fixedHkdfSha512JointStreamRealImpl source) adversary.main

/-- Prefix-consistent lazy-random complete-stream experiment. -/
noncomputable def fixedHkdfSha512JointStreamRandomExp
    {qU qKdf : ℕ}
    (adversary : FixedHkdfSha512JointStreamAdversary qU qKdf) :
    ProbComp Bool :=
  (simulateQ fixedHkdfSha512JointStreamRandomImpl adversary.main).run' ∅

/-- Fixed-HKDF-SHA-512 joint-stream real-or-random advantage.

This deliberately named primitive advantage is the reduction endpoint; it is not a claim that the public-input source is a fixed-secret-key PRF.
-/
noncomputable def fixedHkdfSha512JointStreamAdvantage
    (source : FixedHkdfSha512NoSaltSource) {qU qKdf : ℕ}
    (adversary : FixedHkdfSha512JointStreamAdversary qU qKdf) : ℝ :=
  (fixedHkdfSha512JointStreamRealExp source adversary).boolDistAdvantage
    (fixedHkdfSha512JointStreamRandomExp adversary)

/-- Real experiment exposed through the exact public projection component. -/
def jointKdfViewRealExp (source : FixedHkdfSha512NoSaltSource)
    {qU qKdf : ℕ} (adversary : JointKdfViewAdversary qU qKdf) :
    ProbComp Bool :=
  simulateQ (jointKdfViewRealImpl source) adversary.main

/-- Lazy-random experiment exposed through the exact public projection component. -/
noncomputable def jointKdfViewRandomExp {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) : ProbComp Bool :=
  (simulateQ jointKdfViewRandomImpl adversary.main).run' ∅

/-- Distinguishing advantage on the exact public projection view. -/
noncomputable def jointKdfViewAdvantage
    (source : FixedHkdfSha512NoSaltSource) {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) : ℝ :=
  (jointKdfViewRealExp source adversary).boolDistAdvantage
    (jointKdfViewRandomExp adversary)

/-- Forwarding reproduces the public real world exactly. -/
theorem jointKdfViewRealExp_eq_fixedHkdfSha512JointStreamRealExp
    (source : FixedHkdfSha512NoSaltSource) {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    jointKdfViewRealExp source adversary =
      fixedHkdfSha512JointStreamRealExp source
        (jointKdfViewReduction adversary) := by
  simp [jointKdfViewRealExp, fixedHkdfSha512JointStreamRealExp,
    jointKdfViewRealImpl, jointKdfViewReduction]

/-- Forwarding reproduces the public lazy-random world exactly. -/
theorem jointKdfViewRandomExp_eq_fixedHkdfSha512JointStreamRandomExp
    {qU qKdf : ℕ} (adversary : JointKdfViewAdversary qU qKdf) :
    jointKdfViewRandomExp adversary =
      fixedHkdfSha512JointStreamRandomExp
        (jointKdfViewReduction adversary) := by
  simp [jointKdfViewRandomExp, fixedHkdfSha512JointStreamRandomExp,
    jointKdfViewRandomImpl, jointKdfViewReduction]

/-- The public component advantage is exactly the named complete-stream advantage of its factor-one forwarding reduction. -/
theorem jointKdfViewAdvantage_eq_fixedHkdfSha512JointStreamAdvantage
    (source : FixedHkdfSha512NoSaltSource) {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    jointKdfViewAdvantage source adversary =
      fixedHkdfSha512JointStreamAdvantage source
        (jointKdfViewReduction adversary) := by
  rw [jointKdfViewAdvantage, fixedHkdfSha512JointStreamAdvantage,
    jointKdfViewRealExp_eq_fixedHkdfSha512JointStreamRealExp,
    jointKdfViewRandomExp_eq_fixedHkdfSha512JointStreamRandomExp]

/-- Factor-one reduction bound with no multiplicative or query loss. -/
theorem jointKdfViewAdvantage_le_fixedHkdfSha512JointStreamAdvantage
    (source : FixedHkdfSha512NoSaltSource) {qU qKdf : ℕ}
    (adversary : JointKdfViewAdversary qU qKdf) :
    jointKdfViewAdvantage source adversary ≤
      fixedHkdfSha512JointStreamAdvantage source
        (jointKdfViewReduction adversary) := by
  exact le_of_eq
    (jointKdfViewAdvantage_eq_fixedHkdfSha512JointStreamAdvantage
      source adversary)

end BeaconcryptCore.Computational.PqxdhJointKdfGame
