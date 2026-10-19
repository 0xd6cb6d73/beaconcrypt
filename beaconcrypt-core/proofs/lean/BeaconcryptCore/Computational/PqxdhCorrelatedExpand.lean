import BeaconcryptCore.Computational.PqxdhCorrelatedExtractQueryBounds

/-!
Exact root-valued observation of the consistent random-PRK family. The compiler preserves the complete private protocol continuation before interpretation; its table projection removes only private PRKs after deriving their roots. It does not assume PRK/root injectivity, distinct source coordinates, or a native global protocol instantiation.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhCorrelatedExpand
open PqxdhSecretInputKdf PqxdhHiddenRoot PqxdhJointKdfGame
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhCorrelatedExtractFamily
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev RootOracle := Message →ₒ RootOutput
abbrev RootSpec := unifSpec + RootOracle

def rootCoins {Result : Type} (client : ProbComp Result) : OracleComp RootSpec Result :=
  OracleComp.liftComp client RootSpec

/-- This compiler reveals only projected roots to its client, never the sampled PRK. -/
def compile (hmac : HmacSha512) : QueryImpl RootSpec (OracleComp FamilySpec) :=
  let primitive : QueryImpl RootOracle (OracleComp FamilySpec) := fun message => do
    let prk ← FamilySpec.query (.inr message)
    pure (expandRoot hmac prk)
  QueryImpl.ofLift unifSpec (OracleComp FamilySpec) + primitive

theorem compile_coins {Result : Type} (hmac : HmacSha512) (client : ProbComp Result) :
    simulateQ (compile hmac) (rootCoins client) = coins client := by
  simp only [compile, rootCoins, coins, QueryImpl.simulateQ_add_liftComp_left]
  rfl

noncomputable def rootPost
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secretKey : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (LocalPostSpec baseSpec) (OracleComp RootSpec)
  | .inl request => rootCoins (simulateQ (kemAmbientImpl baseImpl) (publicImpl kem secretKey challenge request))
  | .inr request =>
      if request.ciphertext = challenge then some <$> RootSpec.query (.inr (coordinates request.coordinates))
      else do
        let recovered ← rootCoins (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secretKey request.ciphertext))
        pure (recovered.map (productionHiddenRoot source request.coordinates))

noncomputable def rootResume
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (prepared : Prepared protocol KemSK) : OracleComp RootSpec Bool := do
  let initial ← match protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
    | none => pure none
    | some known => some <$> RootSpec.query (.inr (coordinates known))
  simulateQ (rootPost source baseImpl kem prepared.secretKey prepared.ciphertext)
    (protocol.resume prepared.publicKey prepared.ciphertext prepared.state initial)

noncomputable def rootReduction
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    OracleComp RootSpec Bool := do
  let prepared ← rootCoins (prepare baseImpl kem protocol)
  rootResume source baseImpl kem protocol prepared

/-- Full optional post replies are reconstructed using only root-valued family answers. -/
theorem compile_post
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secretKey : KemSK) (challenge : MlKem768Ciphertext) :
    compile hmac ∘ₛ rootPost source baseImpl kem secretKey challenge =
      post source hmac baseImpl kem secretKey challenge := by
  funext request
  cases request with
  | inl request => exact compile_coins hmac _
  | inr request =>
      by_cases same : request.ciphertext = challenge
      · simp only [QueryImpl.compose, rootPost, post, same, ite_true, simulateQ_map]
        rfl
      · simp only [QueryImpl.compose, rootPost, post, same, ite_false, simulateQ_bind, compile_coins, simulateQ_pure]

/-- The root-valued source keeps every original continuation before either cryptographic interpreter is applied. -/
theorem compile_resume
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (prepared : Prepared protocol KemSK) :
    simulateQ (compile hmac) (rootResume source baseImpl kem protocol prepared) =
      resume source hmac baseImpl kem protocol prepared := by
  unfold rootResume resume
  cases initial : protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
  | none =>
      simp only [pure_bind, ← QueryImpl.simulateQ_compose, compile_post]
      rfl
  | some known =>
      simp only [simulateQ_bind,
        ← QueryImpl.simulateQ_compose, compile_post]
      rfl

theorem compile_reduction
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    simulateQ (compile hmac) (rootReduction source baseImpl kem protocol) =
      PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol := by
  simp only [rootReduction, PqxdhCorrelatedExtractFamily.reduction, simulateQ_bind,
    compile_coins, compile_resume]

/-- The table projection preserves every address and discards only each private PRK beyond its derived root. -/
def projectCache (hmac : HmacSha512) (cache : ExtractOracle.QueryCache) : RootOracle.QueryCache :=
  fun message => (cache message).map (expandRoot hmac)

theorem projectCache_empty (hmac : HmacSha512) : projectCache hmac ∅ = ∅ := by
  funext message
  rfl

noncomputable def rootSampler (hmac : HmacSha512) : ProbComp RootOutput :=
  expandRoot hmac <$> ($ᵗ HmacBlock)

/-- Direct root service: fresh hidden PRK sampling, real Expand, and consistent root caching. -/
noncomputable def rootImpl (hmac : HmacSha512) : QueryImpl RootSpec (StateT RootOracle.QueryCache ProbComp) :=
  let primitive : QueryImpl RootOracle ProbComp := fun _ => rootSampler hmac
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT RootOracle.QueryCache ProbComp) +
    primitive.withCaching

theorem projectCache_update (hmac : HmacSha512) (cache : ExtractOracle.QueryCache)
    (message : Message) (prk : HmacBlock) :
    projectCache hmac (cache.cacheQuery message prk) =
      (projectCache hmac cache).cacheQuery message (expandRoot hmac prk) := by
  funext other
  by_cases same : other = message
  · subst other
    simp [projectCache]
  · simp [projectCache, QueryCache.cacheQuery_of_ne, same]

set_option backward.isDefEq.respectTransparency false in
/-- Each direct query retains the same root and complete projected cache, including repeated addresses. -/
theorem rootImpl_step (hmac : HmacSha512) (request : RootSpec.Domain)
    (cache : ExtractOracle.QueryCache) :
    Prod.map id (projectCache hmac) <$>
      ((simulateQ PqxdhCorrelatedExtractFamily.randomImpl (compile hmac request)).run cache) =
      (rootImpl hmac request).run (projectCache hmac cache) := by
  cases request with
  | inl coin =>
      simp only [compile, QueryImpl.add_apply_inl, rootImpl]
      rfl
  | inr message =>
      change Prod.map id (projectCache hmac) <$>
        ((simulateQ PqxdhCorrelatedExtractFamily.randomImpl
          ((FamilySpec.query (.inr message) : OracleComp FamilySpec HmacBlock) >>= fun prk =>
            pure (expandRoot hmac prk))).run cache) = _
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        simulateQ_pure, StateT.run_pure]
      cases hit : cache message with
      | none =>
          rw [random_miss message cache hit]
          have absent : projectCache hmac cache message = none := by simp [projectCache, hit]
          simp only [rootImpl, QueryImpl.add_apply_inr, QueryImpl.withCaching_run_none _ absent,
            rootSampler, bind_pure_comp, Functor.map_map]
          simp only [Prod.map, projectCache_update, id_eq]
      | some prk =>
          rw [random_hit message cache prk hit]
          have present : projectCache hmac cache message = some (expandRoot hmac prk) := by simp [projectCache, hit]
          simp only [rootImpl, QueryImpl.add_apply_inr, QueryImpl.withCaching_run_some _ present]
          rfl

/-- Full adaptive execution keeps all roots and protocol output while projecting only the hidden PRK cache. -/
theorem rootImpl_complete {Result : Type} (hmac : HmacSha512)
    (client : OracleComp RootSpec Result) (cache : ExtractOracle.QueryCache) :
    Prod.map id (projectCache hmac) <$>
      ((simulateQ PqxdhCorrelatedExtractFamily.randomImpl (simulateQ (compile hmac) client)).run cache) =
      (simulateQ (rootImpl hmac) client).run (projectCache hmac cache) := by
  rw [← QueryImpl.simulateQ_compose]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ _ (rootImpl_step hmac) client cache

noncomputable def expandedGame (hmac : HmacSha512) (client : OracleComp RootSpec Bool) : ProbComp Bool :=
  (simulateQ (rootImpl hmac) client).run' ∅

/-- The ordinary family comparison is exactly the direct cached-root source, after erasing private PRKs. -/
theorem expandedGame_eq (hmac : HmacSha512) (client : OracleComp RootSpec Bool) :
    PqxdhCorrelatedExtractFamily.randomGame (simulateQ (compile hmac) client) = expandedGame hmac client := by
  have complete := congrArg (Prod.fst <$> ·) (rootImpl_complete hmac client ∅)
  simpa only [PqxdhCorrelatedExtractFamily.randomGame, expandedGame, StateT.run'_eq,
    Functor.map_map, Prod.map_fst, id_eq, projectCache_empty] using complete

theorem reduction_expanded_eq
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    PqxdhCorrelatedExtractFamily.randomGame
      (PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol) =
      expandedGame hmac (rootReduction source baseImpl kem protocol) := by
  rw [← compile_reduction]
  exact expandedGame_eq hmac _

end BeaconcryptCore.Computational.PqxdhCorrelatedExpand

/-! Persistent kernel-dependency audit for every statement in this module. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_post' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_post

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_resume

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_reduction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.compile_reduction

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.projectCache_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.projectCache_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.projectCache_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.projectCache_update

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.rootImpl_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.rootImpl_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.rootImpl_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.rootImpl_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.expandedGame_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.expandedGame_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpand.reduction_expanded_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpand.reduction_expanded_eq
