import BeaconcryptCore.Computational.PqxdhInitializerSecrecy
import BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

/-!
# One-session PQXDH initialized-chain secrecy

HB-69 materially specializes the HB-66 initializer game to the two directional model chains used by the initial ratchet.
The wrapper privately receives the independently protected root, requests the existing typed first32 and second32 projections in source order at one canonical ratchet address, converts them to model bytes, and exposes only the Server-to-Beacon and Beacon-to-Server pair to a downstream observer.
The four DH-derived root coordinates are conservatively caller/adversary-visible known coordinates in this game; this wording does not claim that the underlying production values are public wire data.
Two logical projection requests remain two challenger-facing source calls, while the lazy-random interpretation samples one 76-byte value on the first empty-cache request and reuses it for the second same-address request and later observer requests.
The coefficient-one capstone reuses exactly the existing ML-KEM-768 IND-CCA and fixed HKDF-SHA-512/no-salt joint-stream endpoints plus the HB-66 root-guess term.
The extracted-kernel corollary is deterministic and conditional on separate endpoint-local root representations and pending-indexed response adapter premises; no concrete array or kernel appears inside a probabilistic game.
This module proves no primitive internals, root provenance or agreement, authenticated-target discharge, projection-collision conditioning, operation-level crypto adapter, source/compiler refinement, multi-session lifting, or PPT, QPT, or QROM claim.
-/

open OracleSpec OracleComp ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhInitializedChainsSecrecy

open PqxdhKemIndCca PqxdhHiddenRoot PqxdhJointKdf PqxdhJointKdfGame
open PqxdhInitializerSecrecy PqxdhInitialRatchetComplementarity

variable {iota : Type} {baseSpec : OracleSpec iota} {SK : Type}

/-- Directional model chains exposed after initialization. -/
structure InitializedDirectionalChains where
  serverToBeacon : Pqxdh.Bytes
  beaconToServer : Pqxdh.Bytes

/-- A downstream observer sees the public initializer transcript, the four conservatively known root coordinates and public context, and only the two directional chains. -/
structure InitializedChainsObserver
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)) where
  State : Type
  Context : Type
  preChallenge : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec State
  knownCoordinates : State → MlKem768PublicKey → MlKem768Ciphertext →
    KnownPqxdhRootCoordinates
  publicContext : State → MlKem768PublicKey → MlKem768Ciphertext → Context
  main : InitializerPublicTranscript Context → KnownPqxdhRootCoordinates →
    InitializedDirectionalChains → OracleComp (InitializerPostSpec baseSpec) Bool

/-- The first typed symmetric projection at the canonical root-derived ratchet address. -/
def initializedFirstQuery (root : HiddenRootCoordinate) : JointKdfViewQuery :=
  ⟨root.toList, .ratchet, .first32⟩

/-- The second typed symmetric projection at the same canonical root-derived ratchet address. -/
def initializedSecondQuery (root : HiddenRootCoordinate) : JointKdfViewQuery :=
  ⟨root.toList, .ratchet, .second32⟩

@[simp] theorem initializedFirstQuery_address (root : HiddenRootCoordinate) :
    (initializedFirstQuery root).address = ratchetAddress root.toList := by
  rfl

@[simp] theorem initializedSecondQuery_address (root : HiddenRootCoordinate) :
    (initializedSecondQuery root).address = ratchetAddress root.toList := by
  rfl

theorem initializedQueries_same_address (root : HiddenRootCoordinate) :
    (initializedFirstQuery root).address = (initializedSecondQuery root).address := by
  rfl

@[simp] theorem initializedFirstQuery_width (root : HiddenRootCoordinate) :
    (initializedFirstQuery root).projection.width = 32 := by
  rfl

@[simp] theorem initializedSecondQuery_width (root : HiddenRootCoordinate) :
    (initializedSecondQuery root).projection.width = 32 := by
  rfl

/-- Issue the two source projections in order, then erase the root before invoking the observer. -/
def initializedChainsWrapperMain
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate) :
    OracleComp (InitializerPostSpec baseSpec) Bool := do
  let serverToBeacon ← liftM ((InitializerPostSpec baseSpec).query
    (.inr (initializedFirstQuery root)))
  let beaconToServer ← liftM ((InitializerPostSpec baseSpec).query
    (.inr (initializedSecondQuery root)))
  observer.main transcript known
    ⟨serverToBeacon.toList, beaconToServer.toList⟩

/-- Exact source-order normal form: first32, then second32, then the observer with the root erased. -/
theorem initializedChainsWrapperMain_query_normal_form
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate) :
    initializedChainsWrapperMain kem observer transcript known root = (do
      let serverToBeacon ← liftM ((InitializerPostSpec baseSpec).query
        (.inr (initializedFirstQuery root)))
      let beaconToServer ← liftM ((InitializerPostSpec baseSpec).query
        (.inr (initializedSecondQuery root)))
      observer.main transcript known
        ⟨serverToBeacon.toList, beaconToServer.toList⟩) := by
  rfl

/-- Specialize the HB-66 initializer adversary by privately projecting its root to two directional chains. -/
def toInitializerAdversary
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) : InitializerAdversary kem where
  State := observer.State
  Context := observer.Context
  preChallenge := observer.preChallenge
  knownCoordinates := observer.knownCoordinates
  publicContext := observer.publicContext
  main := initializedChainsWrapperMain kem observer

/-- Production interpretation of the two wrapper queries is exactly the existing root-chain function. -/
theorem simulateQ_initializedChainsWrapperMain_real
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate) :
    simulateQ (initializerPostRealImpl source kem)
        (initializedChainsWrapperMain kem observer transcript known root) =
      simulateQ (initializerPostRealImpl source kem)
        (observer.main transcript known
          ⟨(Pqxdh.rootChains source.crypto root.toList).1,
            (Pqxdh.rootChains source.crypto root.toList).2⟩) := by
  rw [PqxdhJointKdf.rootChains_eq_initialProjection source.crypto
    source.prefixConsistent root.toList]
  simp [initializedChainsWrapperMain, initializerPostRealImpl,
    initializedFirstQuery, initializedSecondQuery,
    JointKdfViewQuery.project, JointKdfProjection.project,
    JointKdfViewQuery.address, FixedHkdfDomain.address,
    PqxdhJointKdf.ratchetAddress, PqxdhJointKdf.initialProjection]

/-! ## Exact logical query accounting -/

/-- Logical query caps for the observer before the wrapper adds its two typed chain projections. -/
def InitializedChainsObserver.MakesAtMostQueries
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (observer : InitializedChainsObserver kem)
    (qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym : ℕ) : Prop :=
  (∀ pk,
    (observer.preChallenge pk).IsQueryBoundP IsMlKemUniformQuery qUPre ∧
    (observer.preChallenge pk).IsQueryBoundP IsMlKemBaseQuery qBPre ∧
    (observer.preChallenge pk).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDPre) ∧
  (∀ transcript known chains,
    (observer.main transcript known chains).IsQueryBoundP
        IsInitializerUniformQuery qUPost ∧
    (observer.main transcript known chains).IsQueryBoundP
        IsInitializerBaseQuery qBPost ∧
    (observer.main transcript known chains).IsQueryBoundP
        IsInitializerLogicalDecapsulationQuery qDPost ∧
    (observer.main transcript known chains).IsQueryBoundP
        IsInitializerRootQuery qRoot ∧
    (observer.main transcript known chains).IsQueryBoundP
        IsInitializerSymmetricQuery qSym)

/-- The wrapper's two typed projections add no uniform calls. -/
theorem initializedChainsWrapperMain_uniform_query_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate)
    {q : ℕ}
    (hbound : ∀ chains, (observer.main transcript known chains).IsQueryBoundP
      IsInitializerUniformQuery q) :
    (initializedChainsWrapperMain kem observer transcript known root).IsQueryBoundP
      IsInitializerUniformQuery q := by
  simp only [initializedChainsWrapperMain,
    OracleComp.isQueryBoundP_query_bind_iff]
  simp [IsInitializerUniformQuery]
  intro first second
  exact hbound ⟨first.toList, second.toList⟩

/-- The wrapper's two typed projections add no base calls. -/
theorem initializedChainsWrapperMain_base_query_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate)
    {q : ℕ}
    (hbound : ∀ chains, (observer.main transcript known chains).IsQueryBoundP
      IsInitializerBaseQuery q) :
    (initializedChainsWrapperMain kem observer transcript known root).IsQueryBoundP
      IsInitializerBaseQuery q := by
  simp only [initializedChainsWrapperMain,
    OracleComp.isQueryBoundP_query_bind_iff]
  simp [IsInitializerBaseQuery]
  intro first second
  exact hbound ⟨first.toList, second.toList⟩

/-- The wrapper's two typed projections add no logical decapsulation calls. -/
theorem initializedChainsWrapperMain_decapsulation_query_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate)
    {q : ℕ}
    (hbound : ∀ chains, (observer.main transcript known chains).IsQueryBoundP
      IsInitializerLogicalDecapsulationQuery q) :
    (initializedChainsWrapperMain kem observer transcript known root).IsQueryBoundP
      IsInitializerLogicalDecapsulationQuery q := by
  simp only [initializedChainsWrapperMain,
    OracleComp.isQueryBoundP_query_bind_iff]
  simp [IsInitializerLogicalDecapsulationQuery]
  intro first second
  exact hbound ⟨first.toList, second.toList⟩

/-- The wrapper's two typed projections add no root-domain calls. -/
theorem initializedChainsWrapperMain_root_query_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate)
    {q : ℕ}
    (hbound : ∀ chains, (observer.main transcript known chains).IsQueryBoundP
      IsInitializerRootQuery q) :
    (initializedChainsWrapperMain kem observer transcript known root).IsQueryBoundP
      IsInitializerRootQuery q := by
  simp only [initializedChainsWrapperMain,
    OracleComp.isQueryBoundP_query_bind_iff]
  simp [IsInitializerRootQuery, IsHiddenRootDomainQuery,
    initializedFirstQuery, initializedSecondQuery]
  intro first second
  exact hbound ⟨first.toList, second.toList⟩

/-- The wrapper adds exactly the two first/second symmetric projection sites to an observer upper bound. -/
theorem initializedChainsWrapperMain_symmetric_query_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate)
    {q : ℕ}
    (hbound : ∀ chains, (observer.main transcript known chains).IsQueryBoundP
      IsInitializerSymmetricQuery q) :
    (initializedChainsWrapperMain kem observer transcript known root).IsQueryBoundP
      IsInitializerSymmetricQuery (q + 2) := by
  simp only [initializedChainsWrapperMain,
    OracleComp.isQueryBoundP_query_bind_iff]
  simp [IsInitializerSymmetricQuery, IsHiddenRootSymmetricQuery,
    initializedFirstQuery, initializedSecondQuery]
  intro first second
  exact (hbound ⟨first.toList, second.toList⟩).mono (by omega)

/-- The specialized HB-66 adversary preserves all observer caps and adds two symmetric calls. -/
theorem toInitializerAdversary_makesAtMostQueries
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    {qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym : ℕ}
    (hbound : observer.MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym) :
    (toInitializerAdversary kem observer).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost qRoot (qSym + 2) := by
  constructor
  · exact hbound.1
  · intro transcript known root
    have hmain := hbound.2 transcript known
    exact ⟨
      initializedChainsWrapperMain_uniform_query_bound kem observer
        transcript known root (fun chains => (hmain chains).1),
      initializedChainsWrapperMain_base_query_bound kem observer
        transcript known root (fun chains => (hmain chains).2.1),
      initializedChainsWrapperMain_decapsulation_query_bound kem observer
        transcript known root (fun chains => (hmain chains).2.2.1),
      initializedChainsWrapperMain_root_query_bound kem observer
        transcript known root (fun chains => (hmain chains).2.2.2.1),
      initializedChainsWrapperMain_symmetric_query_bound kem observer
        transcript known root (fun chains => (hmain chains).2.2.2.2)⟩

/-! ## One-address lazy-stream normal form -/

/-- After the KEM/base post handler is lifted away, the wrapper remains the same two view queries followed by the transformed observer. -/
theorem simulateQ_initializedChainsWrapperMain_toJointKdfView
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (sk : SK) (cStar : MlKem768Ciphertext)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate) :
    simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
        (initializedChainsWrapperMain kem observer transcript known root) =
      (do
        let serverToBeacon ←
          liftM (JointKdfViewAdversarySpec.query
            (.inr (initializedFirstQuery root)))
        let beaconToServer ←
          liftM (JointKdfViewAdversarySpec.query
            (.inr (initializedSecondQuery root)))
        simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
          (observer.main transcript known
            ⟨serverToBeacon.toList, beaconToServer.toList⟩)) := by
  simp [initializedChainsWrapperMain, initializerPostToJointKdfViewImpl]

/-- Sum-range-normalized miss form for a typed view query. -/
theorem jointKdfViewRandomImpl_inr_run_miss
    (query : JointKdfViewQuery) (cache : JointKdfRO.QueryCache)
    (hcache : cache query.address = none) :
    (jointKdfViewRandomImpl (.inr query)).run cache =
      (fun stream : JointKdfStream =>
        (show JointKdfViewAdversarySpec.Range (.inr query) ×
            JointKdfRO.QueryCache from
          (query.project stream, cache.cacheQuery query.address stream))) <$>
        ($ᵗ JointKdfStream) := by
  exact jointKdfViewRandomImpl_projection_run_miss query cache hcache

/-- Sum-range-normalized hit form for a typed view query. -/
theorem jointKdfViewRandomImpl_inr_run_hit
    (query : JointKdfViewQuery) (cache : JointKdfRO.QueryCache)
    (stream : JointKdfStream) (hcache : cache query.address = some stream) :
    (jointKdfViewRandomImpl (.inr query)).run cache =
      pure (show JointKdfViewAdversarySpec.Range (.inr query) ×
          JointKdfRO.QueryCache from (query.project stream, cache)) := by
  exact jointKdfViewRandomImpl_projection_run_hit query cache stream hcache

/-- From an empty cache, the two logical projection calls sample one complete stream, install it once, and reuse it on the second same-address call. -/
theorem run_initializedChainsWrapperMain_random_empty
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (sk : SK) (cStar : MlKem768Ciphertext)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate) :
    (simulateQ jointKdfViewRandomImpl
      (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
        (initializedChainsWrapperMain kem observer transcript known root))).run
        (∅ : JointKdfRO.QueryCache) =
      (do
        let stream ← $ᵗ JointKdfStream
        (simulateQ jointKdfViewRandomImpl
          (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
            (observer.main transcript known
              ⟨PqxdhJointKdf.first32 stream,
                PqxdhJointKdf.second32 stream⟩))).run
          ((∅ : JointKdfRO.QueryCache).cacheQuery
            (ratchetAddress root.toList) stream)) := by
  rw [simulateQ_initializedChainsWrapperMain_toJointKdfView]
  simp only [simulateQ_query_bind, OracleQuery.input_query,
    monadLift_self, StateT.run_bind]
  rw [jointKdfViewRandomImpl_inr_run_miss _ _
    (QueryCache.empty_apply _)]
  rw [bind_map_left]
  apply bind_congr
  intro stream
  rw [jointKdfViewRandomImpl_inr_run_hit _ _ stream]
  · simp [initializedFirstQuery, initializedSecondQuery,
      JointKdfViewQuery.project, JointKdfProjection.project]
    rfl
  · exact QueryCache.cacheQuery_self _ _ _

/-- Output-only form of the one-miss/one-hit law; the observer still starts from the populated shared cache. -/
theorem run'_initializedChainsWrapperMain_random_empty
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (sk : SK) (cStar : MlKem768Ciphertext)
    (transcript : InitializerPublicTranscript observer.Context)
    (known : KnownPqxdhRootCoordinates) (root : HiddenRootCoordinate) :
    (simulateQ jointKdfViewRandomImpl
      (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
        (initializedChainsWrapperMain kem observer transcript known root))).run'
        (∅ : JointKdfRO.QueryCache) =
      (do
        let stream ← $ᵗ JointKdfStream
        (simulateQ jointKdfViewRandomImpl
          (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem sk cStar)
            (observer.main transcript known
              ⟨PqxdhJointKdf.first32 stream,
                PqxdhJointKdf.second32 stream⟩))).run'
          ((∅ : JointKdfRO.QueryCache).cacheQuery
            (ratchetAddress root.toList) stream)) := by
  simp only [StateT.run'_eq]
  rw [run_initializedChainsWrapperMain_random_empty]
  rw [map_bind]

/-! ## Readable production and independent-root games -/

/-- One-key production client that exposes only the two existing directional model chains to the observer. -/
def toProductionInitializedChainsOneKeyAdversary
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) : OneKeyAdversary kem where
  Context := observer.State
  preChallenge := observer.preChallenge
  postChallenge transcript kStar :=
    let known := observer.knownCoordinates transcript.context
      transcript.publicKey transcript.ciphertext
    let publicContext := observer.publicContext transcript.context
      transcript.publicKey transcript.ciphertext
    let root := productionHiddenRoot source known kStar
    simulateQ (initializerPostRealImpl source kem)
      (observer.main
        ⟨transcript.publicKey, transcript.ciphertext, publicContext⟩ known
        ⟨(Pqxdh.rootChains source.crypto root.toList).1,
          (Pqxdh.rootChains source.crypto root.toList).2⟩)

/-- The specialized HB-66 post client is exactly the readable production-chain client. -/
theorem toKemOneKeyAdversary_initializedChains_postChallenge
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (transcript : MlKemChallengeTranscript observer.State)
    (kStar : MlKemSharedSecret) :
    (toKemOneKeyAdversary source kem
      (toInitializerAdversary kem observer)).postChallenge transcript kStar =
    (toProductionInitializedChainsOneKeyAdversary source kem observer).postChallenge
      transcript kStar := by
  exact simulateQ_initializedChainsWrapperMain_real source kem observer
    ⟨transcript.publicKey, transcript.ciphertext,
      observer.publicContext transcript.context transcript.publicKey
        transcript.ciphertext⟩
    (observer.knownCoordinates transcript.context transcript.publicKey
      transcript.ciphertext)
    (productionHiddenRoot source
      (observer.knownCoordinates transcript.context transcript.publicKey
        transcript.ciphertext) kStar)

/-- Readable production initialized-chain game, retaining the exact one-key KEM prefix and post-challenge surface. -/
noncomputable def productionInitializedChainsGame
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl)
    (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
      (toProductionInitializedChainsOneKeyAdversary source kem observer) true)

/-- HB-66's real game specialized by the wrapper is definitionally the same prefix and, by prefix consistency, the readable production-chain post phase. -/
theorem initializerRealGame_initializedChains_eq_production
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) :
    initializerRealGame source baseImpl kem
        (toInitializerAdversary kem observer) =
      productionInitializedChainsGame source baseImpl kem observer := by
  unfold initializerRealGame productionInitializedChainsGame oneKeyBranchMain
  apply congrArg (simulateQ (kemAmbientImpl baseImpl))
  apply bind_congr
  intro preState
  unfold oneKeyFinish
  apply bind_congr
  intro encapsulation
  apply bind_congr
  intro kRand
  rw [toKemOneKeyAdversary_initializedChains_postChallenge]
  rfl

/-- Readable terminal game: after the independent root is sampled, one lazy 76-byte stream at its canonical ratchet address supplies both directional chains and remains cached for the observer. -/
noncomputable def independentRootInitializedChainsGame
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) : ProbComp Bool := do
  let sampled ← initializerKdfPrefixProb baseImpl kem
    (toInitializerAdversary kem observer)
  let known := observer.knownCoordinates sampled.state
    sampled.publicKey sampled.ciphertext
  let publicContext := observer.publicContext sampled.state
    sampled.publicKey sampled.ciphertext
  let _hidden ← $ᵗ HiddenRootCoordinate
  let root ← $ᵗ HiddenRootCoordinate
  let stream ← $ᵗ JointKdfStream
  (simulateQ jointKdfViewRandomImpl
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (observer.main
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known
        ⟨PqxdhJointKdf.first32 stream,
          PqxdhJointKdf.second32 stream⟩))).run'
    ((∅ : JointKdfRO.QueryCache).cacheQuery
      (ratchetAddress root.toList) stream)

/-- HB-66's terminal independent-root game specializes exactly to one shared-address cached stream supplying the two directional chains. -/
theorem initializerIndependentRootGame_initializedChains_eq
    {qPrefix qPost qRoot qSym : ℕ}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializerKdfReductionBounds baseImpl kem
      (toInitializerAdversary kem observer)
      qPrefix qPost qRoot (qSym + 2)) :
    initializerIndependentRootGame baseImpl kem
        (toInitializerAdversary kem observer) bounds =
      independentRootInitializedChainsGame baseImpl kem observer := by
  unfold initializerIndependentRootGame independentRootInitializedChainsGame
  apply bind_congr
  intro sampled
  simp only [sampledHiddenRootAdversary, toHiddenRootAdversary,
    hiddenRootIndependentGame, toInitializerAdversary]
  apply bind_congr
  intro hidden
  apply bind_congr
  intro root
  exact run'_initializedChainsWrapperMain_random_empty baseImpl kem observer
    sampled.secretKey sampled.ciphertext
    ⟨sampled.publicKey, sampled.ciphertext,
      observer.publicContext sampled.state sampled.publicKey sampled.ciphertext⟩
    (observer.knownCoordinates sampled.state sampled.publicKey
      sampled.ciphertext) root

/-! ## Reduction packaging and primitive-facing accounting -/

/-- Source caps plus the same caller-supplied ambient-uniform slack obligations used by HB-66, specialized to the chain wrapper. -/
structure InitializedChainsExplicitReductionBounds
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ) where
  observerQueries : observer.MakesAtMostQueries
    qUPre qBPre qDPre qUPost qBPost qDPost qRoot qSym
  ambientTotal : qKemPrefix + qKemPost ≤ qKemAmbient
  prefixUniform :
    (OracleComp.liftComp
      (initializerKdfPrefixProb baseImpl kem
        (toInitializerAdversary kem observer))
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512UniformQuery (qKemPrefix + qUPre)
  postUniform : ∀
      (sampled : InitializerKdfPrefix kem
        (toInitializerAdversary kem observer))
      (known : KnownPqxdhRootCoordinates)
      (publicContext : observer.Context) (root : HiddenRootCoordinate),
    (simulateQ (initializerPostToJointKdfViewImpl baseImpl kem
        sampled.secretKey sampled.ciphertext)
      (initializedChainsWrapperMain kem observer
        ⟨sampled.publicKey, sampled.ciphertext, publicContext⟩ known root)).IsQueryBoundP
      IsJointKdfViewUniformQuery (qKemPost + qUPost)

/-- Package the observer's unchanged caps and its two added symmetric queries for direct use by HB-66. -/
def InitializedChainsExplicitReductionBounds.toInitializerBounds
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    {source : FixedHkdfSha512NoSaltSource}
    {baseImpl : QueryImpl baseSpec ProbComp}
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    {observer : InitializedChainsObserver kem}
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    InitializerExplicitReductionBounds source baseImpl kem
      (toInitializerAdversary kem observer)
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot (qSym + 2) where
  sourceQueries := toInitializerAdversary_makesAtMostQueries kem observer
    bounds.observerQueries
  ambientTotal := bounds.ambientTotal
  prefixUniform := bounds.prefixUniform
  postUniform := bounds.postUniform

/-- The one-key ML-KEM reduction used by the initialized-chain capstone. -/
def initializedChainsKemReduction
    (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) : OneKeyAdversary kem :=
  toKemOneKeyAdversary source kem (toInitializerAdversary kem observer)

/-- The single fixed-HKDF joint-stream reduction used by the initialized-chain capstone. -/
noncomputable def initializedChainsKdfReduction
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    FixedHkdfSha512JointStreamAdversary
      (qKemAmbient + qUPre + qUPost + 32)
      (qRoot + (qSym + 2) + 1) :=
  initializerKdfReduction source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- The KDF reduction's uniform cap is unchanged by the two chain projections. -/
theorem initializedChainsKdfReduction_uniform_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKdfReduction source baseImpl kem observer bounds).main.IsQueryBoundP
      IsFixedHkdfSha512UniformQuery
        (qKemAmbient + qUPre + qUPost + 32) :=
  initializerKdfReduction_uniform_query_bound source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- The two added symmetric projections change the complete-stream upper bound from `qRoot + qSym + 1` to `qRoot + (qSym + 2) + 1`. -/
theorem initializedChainsKdfReduction_stream_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKdfReduction source baseImpl kem observer bounds).main.IsQueryBoundP
      IsFixedHkdfSha512StreamQuery (qRoot + (qSym + 2) + 1) :=
  initializerKdfReduction_stream_query_bound source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- Root-domain accounting remains the HB-66 `qRoot + 1` bound. -/
theorem initializedChainsKdfReduction_root_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKdfReduction source baseImpl kem observer bounds).main.IsQueryBoundP
      IsFixedHkdfRootStreamQuery (qRoot + 1) :=
  initializerKdfReduction_root_query_bound source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- Symmetric-domain accounting is exactly the observer bound plus the two wrapper calls. -/
theorem initializedChainsKdfReduction_symmetric_query_bound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKdfReduction source baseImpl kem observer bounds).main.IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery (qSym + 2) :=
  initializerKdfReduction_symmetric_query_bound source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- The specialized KDF reduction emits no untyped stream address. -/
theorem initializedChainsKdfReduction_no_untyped_stream_queries
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKdfReduction source baseImpl kem observer bounds).main.IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 :=
  initializerKdfReduction_no_untyped_stream_queries source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- Total primitive-interface accounting is the sum of the uniform and complete-stream bounds. -/
theorem initializedChainsKdfReduction_totalQueryBound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKdfReduction source baseImpl kem observer bounds).main.IsTotalQueryBound
      ((qKemAmbient + qUPre + qUPost + 32) +
        (qRoot + (qSym + 2) + 1)) :=
  initializerKdfReduction_totalQueryBound source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- The ML-KEM reduction preserves the observer's six pre/post uniform, base, and logical-decapsulation upper bounds; the chain wrapper adds none of these calls. -/
theorem initializedChainsKemReduction_makesAtMostQueries
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    (initializedChainsKemReduction source kem observer).MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost :=
  initializerKemReduction_makesAtMostQueries source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-- Exact post-challenge ciphertext attempts remain logical but blocked; only unequal ciphertexts are primitive-forwardable. -/
theorem initializedChainsKemReduction_post_unblockedDecapsulationQueryBound
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym)
    (transcript : MlKemChallengeTranscript
      (initializedChainsKemReduction source kem observer).Context)
    (kStar : MlKemSharedSecret) :
    ((initializedChainsKemReduction source kem observer).postChallenge
      transcript kStar).IsQueryBoundP
        (IsMlKemUnblockedDecapsulationQuery transcript.ciphertext) qDPost :=
  initializerKemReduction_post_unblockedDecapsulationQueryBound source
    baseImpl kem (toInitializerAdversary kem observer)
    bounds.toInitializerBounds transcript kStar

/-! ## Coefficient-one initialized-chain secrecy theorem -/

/-- Distinguishing advantage between the source-shaped production chains and the independent-root/shared-lazy-stream chain game. -/
noncomputable def initializedChainsSecrecyAdvantage
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem) : ℝ :=
  (productionInitializedChainsGame source baseImpl kem observer).boolDistAdvantage
    (independentRootInitializedChainsGame baseImpl kem observer)

/-- One-session initialized directional-chain secrecy reduces with coefficient one to the existing ML-KEM IND-CCA and fixed-HKDF joint-stream endpoints plus the one root-guess term. -/
theorem initializedChainsSecrecyAdvantage_le
    {qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym : ℕ}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (observer : InitializedChainsObserver kem)
    (bounds : InitializedChainsExplicitReductionBounds source baseImpl kem observer
      qKemAmbient qKemPrefix qKemPost qUPre qBPre qDPre
      qUPost qBPost qDPost qRoot qSym) :
    initializedChainsSecrecyAdvantage source baseImpl kem observer ≤
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
          (initializedChainsKemReduction source kem observer).toINDCCA +
        fixedHkdfSha512JointStreamAdvantage source
          (initializedChainsKdfReduction source baseImpl kem observer bounds) +
        ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  unfold initializedChainsSecrecyAdvantage
  rw [← initializerRealGame_initializedChains_eq_production source baseImpl
    kem observer]
  rw [← initializerIndependentRootGame_initializedChains_eq baseImpl kem
    observer bounds.toInitializerBounds.toKdfBounds]
  exact initializerSecrecyAdvantage_le source baseImpl kem
    (toInitializerAdversary kem observer) bounds.toInitializerBounds

/-! ## Conditional extracted-kernel endpoint -/

/-- The deterministic production orientation named by the game: Server-to-Beacon is the first projection and Beacon-to-Server is the second. -/
def productionDirectionalChains
    (source : FixedHkdfSha512NoSaltSource) (root : Pqxdh.Bytes) :
    InitializedDirectionalChains :=
  ⟨(Pqxdh.rootChains source.crypto root).1,
    (Pqxdh.rootChains source.crypto root).2⟩

@[simp] theorem productionDirectionalChains_serverToBeacon
    (source : FixedHkdfSha512NoSaltSource) (root : Pqxdh.Bytes) :
    (productionDirectionalChains source root).serverToBeacon =
      (Pqxdh.rootChains source.crypto root).1 := by
  rfl

@[simp] theorem productionDirectionalChains_beaconToServer
    (source : FixedHkdfSha512NoSaltSource) (root : Pqxdh.Bytes) :
    (productionDirectionalChains source root).beaconToServer =
      (Pqxdh.rootChains source.crypto root).2 := by
  rfl

/-- Conditional HB-67 endpoint: if each extracted endpoint's concrete root and its own pending-indexed adapter response represent the same model root, the resulting zero-state kernels refine the game chains and are complementary. -/
theorem productionInitializedChains_to_concreteKernels {AD PT CT : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (cr : Ratchet.Crypto beaconcrypt_core.ratchet.RatchetChain
      beaconcrypt_core.ratchet.RatchetMaterial AD PT CT)
    (serverRoot beaconRoot : Std.Array Std.U8 32#usize)
    (root : Pqxdh.Bytes)
    (serverResponse beaconResponse :
      beaconcrypt_core.pqxdh.concrete.InitialRatchetKdfResponse)
    (hserverRoot : RootArrayRefines serverRoot root)
    (hbeaconRoot : RootArrayRefines beaconRoot root)
    (hserverResponse : InitialResponseRefines source.crypto
      (serverPending serverRoot) serverResponse)
    (hbeaconResponse : InitialResponseRefines source.crypto
      (beaconPending beaconRoot) beaconResponse) :
    let chains := productionDirectionalChains source root
    ∃ serverPendingResult beaconPendingResult :
        beaconcrypt_core.pqxdh.concrete.InitialRatchetKdfPending,
      ∃ serverKernel beaconKernel :
          beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel,
        InitialKernelResult cr
          beaconcrypt_core.pqxdh.concrete.start_server_ratchet_kdf serverRoot
          serverResponse root chains.serverToBeacon chains.beaconToServer
          serverPendingResult serverKernel ∧
        InitialKernelResult cr
          beaconcrypt_core.pqxdh.concrete.start_beacon_ratchet_kdf beaconRoot
          beaconResponse root chains.beaconToServer chains.serverToBeacon
          beaconPendingResult beaconKernel ∧
        serverKernel.refined.send_chain = beaconKernel.refined.receive_chain ∧
        serverKernel.refined.receive_chain = beaconKernel.refined.send_chain := by
  simpa [productionDirectionalChains] using
    initialRatchetComplementarity source.crypto cr serverRoot beaconRoot root
      serverResponse beaconResponse hserverRoot hbeaconRoot
      hserverResponse hbeaconResponse

/--
info: 'BeaconcryptCore.Computational.PqxdhInitializedChainsSecrecy.run_initializedChainsWrapperMain_random_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms run_initializedChainsWrapperMain_random_empty

/--
info: 'BeaconcryptCore.Computational.PqxdhInitializedChainsSecrecy.initializedChainsSecrecyAdvantage_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms initializedChainsSecrecyAdvantage_le

/--
info: 'BeaconcryptCore.Computational.PqxdhInitializedChainsSecrecy.productionInitializedChains_to_concreteKernels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms productionInitializedChains_to_concreteKernels

end BeaconcryptCore.Computational.PqxdhInitializedChainsSecrecy
