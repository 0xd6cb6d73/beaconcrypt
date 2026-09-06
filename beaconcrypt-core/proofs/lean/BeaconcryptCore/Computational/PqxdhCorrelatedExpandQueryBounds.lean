import BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid

/-!
Complete query ledgers for the same root-valued source and indexed ordinary HMAC reductions. Original source coins are counted once across each stopped prefix and continued suffix; real challengers pay a 64-byte key and random challengers pay a fresh 64-byte answer. Logical root bounds count repeated and rejected source attempts, and do not make deterministic cryptographic or state-processing work free.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds
open PqxdhSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
open PqxdhSecretInputInitializer

def IsCoin : RootSpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance : DecidablePred IsCoin
  | .inl _ => inferInstanceAs (Decidable True)
  | .inr _ => inferInstanceAs (Decidable False)

noncomputable def cachedImpl (sample : ProbComp RootOutput) :
    QueryImpl RootSpec (StateT RootOracle.QueryCache ProbComp) :=
  let primitive : QueryImpl RootOracle ProbComp := fun _ => sample
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT RootOracle.QueryCache ProbComp) + primitive.withCaching

set_option backward.isDefEq.respectTransparency false in
/-- Cache hits draw nothing, fresh roots pay the actual sample program, and explicit coins retain their source order. -/
theorem cached_step (sample : ProbComp RootOutput) (cost : Nat) (bounded : sample.IsTotalQueryBound cost)
    (request : RootSpec.Domain) (cache : RootOracle.QueryCache) :
    ((cachedImpl sample request).run cache).IsTotalQueryBound
      ((if IsCoin request then 1 else 0) + (if IsRoot request then cost else 0)) := by
  cases request with
  | inl coin =>
      change (((unifSpec.query coin : ProbComp (unifSpec.Range coin)) >>= fun answer =>
        pure (answer, cache))).IsTotalQueryBound 1
      exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr message =>
      simp only [IsCoin, IsRoot, if_true, if_false, Nat.zero_add]
      cases hit : cache message with
      | none =>
          simp only [cachedImpl, QueryImpl.add_apply_inr, QueryImpl.withCaching_run_none _ hit,
            IsTotalQueryBound, isQueryBound_map_iff]
          exact bounded
      | some root =>
          simp only [cachedImpl, QueryImpl.add_apply_inr, QueryImpl.withCaching_run_some _ hit]
          trivial

/-- Both actual cached-root kernels retain the entire table through every possible client continuation. -/
theorem cached_run {Result : Type} (sample : ProbComp RootOutput) (cost : Nat)
    (sampleBound : sample.IsTotalQueryBound cost) (client : OracleComp RootSpec Result)
    (qCoins qRoots : Nat) (coins : client.IsQueryBoundP IsCoin qCoins)
    (roots : client.IsQueryBoundP IsRoot qRoots) (cache : RootOracle.QueryCache) :
    ((simulateQ (cachedImpl sample) client).run cache).IsTotalQueryBound (qCoins + cost * qRoots) := by
  induction client using OracleComp.inductionOn generalizing qCoins qRoots cache with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at coins roots
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isTotalQueryBound_bind (cached_step sample cost sampleBound request cache)
        (fun answer => ih answer.1 _ _ (coins.2 answer.1) (roots.2 answer.1) answer.2)).mono
      have hc := coins.1
      have hr := roots.1
      have rootStep : ∀ n, 0 < n → cost * (n - 1) + cost = cost * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := rootStep qRoots (by omega)
      all_goals omega

theorem root_run_uniform {Result : Type} (hmac : HmacSha512) (client : OracleComp RootSpec Result)
    (qCoins qRoots : Nat) (coins : client.IsQueryBoundP IsCoin qCoins)
    (roots : client.IsQueryBoundP IsRoot qRoots) (cache : RootOracle.QueryCache) :
    ((simulateQ (rootImpl hmac) client).run cache).IsTotalQueryBound (qCoins + 64 * qRoots) := by
  apply cached_run _ 64 _ client qCoins qRoots coins roots cache
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)

theorem uniform_run_uniform {Result : Type} (client : OracleComp RootSpec Result)
    (qCoins qRoots : Nat) (coins : client.IsQueryBoundP IsCoin qCoins)
    (roots : client.IsQueryBoundP IsRoot qRoots) (cache : RootOracle.QueryCache) :
    ((simulateQ uniformImpl client).run cache).IsTotalQueryBound (qCoins + 32 * qRoots) :=
  cached_run ($ᵗ RootOutput) 32 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    client qCoins qRoots coins roots cache

open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhHiddenRoot
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}
theorem rootCoins_uniform {Result : Type} (client : ProbComp Result) (q : Nat)
    (bounded : client.IsTotalQueryBound q) :
    (rootCoins client).IsQueryBoundP IsCoin q := by
  exact IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (fun _ => Iff.rfl) bounded.isQueryBoundP

theorem rootCoins_roots {Result : Type} (client : ProbComp Result) :
    (rootCoins client).IsQueryBoundP IsRoot 0 := by
  exact IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false client 0)

set_option backward.isDefEq.respectTransparency false in
theorem query_bounds (message : Message) :
    (RootSpec.query (.inr message) : OracleComp RootSpec RootOutput).IsQueryBoundP IsCoin 0 ∧
    (RootSpec.query (.inr message) : OracleComp RootSpec RootOutput).IsQueryBoundP IsRoot 1 := by
  simp [isQueryBoundP_query_iff, IsCoin, IsRoot]

theorem post_uniform_step
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (request : (LocalPostSpec baseSpec).Domain) :
    (rootPost source baseImpl kem secret challenge request).IsQueryBoundP IsCoin
      ((if PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery request then 1 else 0) +
       (if PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery request then qBase else 0) +
       (if RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery request then qDecap else 0)) := by
  rcases request with ((coin | query) | ciphertext) | privateRequest
  all_goals simp only [PublicClass, RoutedClass, IsMlKemUniformQuery, IsMlKemBaseQuery,
    IsMlKemLogicalDecapsulationQuery, if_true, if_false, Nat.zero_add, Nat.add_zero]
  · apply rootCoins_uniform
    change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inl coin))).IsTotalQueryBound 1
    rw [simulateQ_spec_query]
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · apply rootCoins_uniform
    change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inr query))).IsTotalQueryBound qBase
    rw [simulateQ_spec_query]
    exact baseBound query
  · apply rootCoins_uniform
    change (simulateQ (kemAmbientImpl baseImpl)
      (if ciphertext = challenge then pure none else kem.decaps secret ciphertext)).IsTotalQueryBound qDecap
    split
    · simp only [simulateQ_pure]
      trivial
    · exact decapBound ciphertext
  · simp only [rootPost]
    split
    · exact ((isQueryBoundP_map_iff _ some 0).mpr (query_bounds (coordinates privateRequest.coordinates)).1).mono (Nat.zero_le _)
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        rootCoins_uniform _ qDecap (decapBound privateRequest.ciphertext)

theorem post_uniform_run {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (LocalPostSpec baseSpec) Result)
    (qUniform qBaseCalls qDecapCalls : Nat)
    (uniforms : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) qUniform)
    (bases : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : client.IsQueryBoundP (RoutedClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls) :
    (simulateQ (rootPost source baseImpl kem secret challenge) client).IsQueryBoundP IsCoin
      (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  induction client using OracleComp.inductionOn generalizing qUniform qBaseCalls qDecapCalls with
  | pure value => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at uniforms bases decaps
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply (isQueryBoundP_bind
        (post_uniform_step source baseImpl kem secret challenge qBase qDecap baseBound decapBound request)
        (fun answer _ => ih answer _ _ _ (uniforms.2 answer) (bases.2 answer) (decaps.2 answer))).mono
      have hu := uniforms.1
      have hb := bases.1
      have hd := decaps.1
      have baseStep : ∀ n, 0 < n → qBase * (n - 1) + qBase = qBase * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      have decapStep : ∀ n, 0 < n → qDecap * (n - 1) + qDecap = qDecap * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := baseStep qBaseCalls (by omega)
      all_goals try have := decapStep qDecapCalls (by omega)
      all_goals omega

/-- Actual processing counts both public and private decapsulation work, preserving every failed private result. -/
theorem post_uniform_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (u b d r : Nat)
    (bounded : PostBounds client u b d r) :
    (simulateQ (rootPost source baseImpl kem secret challenge) client).IsQueryBoundP IsCoin
      (u + qBase * b + qDecap * (d + r)) := by
  apply post_uniform_run source baseImpl kem secret challenge qBase qDecap baseBound decapBound
    client u b (d + r) bounded.uniforms bounded.bases
  apply IsQueryBoundP.of_imp _ (PqxdhProjectionCollisions.isQueryBoundP_or bounded.decaps bounded.privateRoots)
  intro request selected
  cases request with
  | inl request => exact Or.inl selected
  | inr request => exact Or.inr trivial

/-- Only matching private requests make a family query; every private attempt is charged in the cap. -/
theorem post_root_step
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (request : (LocalPostSpec baseSpec).Domain) :
    (rootPost source baseImpl kem secret challenge request).IsQueryBoundP IsRoot
      (if IsPrivateRoot (baseSpec := baseSpec) request then 1 else 0) := by
  cases request with
  | inl request => exact rootCoins_roots _
  | inr request =>
      simp only [rootPost, IsPrivateRoot, if_true]
      split
      · exact (isQueryBoundP_map_iff _ some 1).mpr (query_bounds (coordinates request.coordinates)).2
      · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using (rootCoins_roots
          (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret request.ciphertext))).mono (by omega)

theorem post_root_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (q : Nat)
    (bounded : client.IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) q) :
    (simulateQ (rootPost source baseImpl kem secret challenge) client).IsQueryBoundP IsRoot q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind]
      have combined := isQueryBoundP_bind (post_root_step source baseImpl kem secret challenge request)
        (fun answer _ => ih answer _ (bounded.2 answer))
      apply combined.mono
      by_cases selected : IsPrivateRoot (baseSpec := baseSpec) request
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, if_true]
        omega
      · simp only [selected, if_false, Nat.zero_add, le_refl]

theorem resume_bounds
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (prepared : Prepared protocol KemSK) (qBase qDecap u b d r : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps prepared.secretKey ciphertext)).IsTotalQueryBound qDecap)
    (bounded : ∀ initial, PostBounds
      (protocol.resume prepared.publicKey prepared.ciphertext prepared.state initial) u b d r) :
    (rootResume source baseImpl kem protocol prepared).IsQueryBoundP IsCoin
      (u + qBase * b + qDecap * (d + r)) ∧
    (rootResume source baseImpl kem protocol prepared).IsQueryBoundP IsRoot (1 + r) := by
  unfold rootResume
  cases initial : protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
  | none =>
      simp only [pure_bind]
      exact ⟨post_uniform_bound source baseImpl kem _ _ _ _ baseBound decapBound _ _ _ _ _ (bounded none),
        (post_root_bound source baseImpl kem _ _ _ _ (bounded none).privateRoots).mono (by omega)⟩
  | some known =>
      constructor
      · have rootBound := (isQueryBoundP_map_iff _ some 0).mpr (query_bounds (coordinates known)).1
        simpa only [Nat.zero_add] using isQueryBoundP_bind rootBound (fun answer _ =>
          post_uniform_bound source baseImpl kem _ _ _ _ baseBound decapBound _ _ _ _ _ (bounded answer))
      · have rootBound := (isQueryBoundP_map_iff _ some 1).mpr (query_bounds (coordinates known)).2
        exact isQueryBoundP_bind rootBound (fun answer _ =>
          post_root_bound source baseImpl kem _ _ _ _ (bounded answer).privateRoots)

/-- Logical family calls and all locally interpreted coin calls are bounded on the actual reduction program. -/
theorem reduction_bounds
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    (rootReduction source baseImpl kem protocol).IsQueryBoundP IsCoin
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) +
        (uPost + qBase * bPost + qDecap * (dPost + privatePost))) ∧
    (rootReduction source baseImpl kem protocol).IsQueryBoundP IsRoot
      (1 + privatePost) := by
  unfold rootReduction
  constructor
  · apply isQueryBoundP_bind (rootCoins_uniform _ _ (PqxdhCorrelatedExtractQueryBounds.prepare_uniform_bound baseImpl kem protocol
      _ _ _ _ _ _ _ _ _ _ _ bounded))
    intro prepared _
    exact (resume_bounds source baseImpl kem protocol prepared _ _ _ _ _ _ bounded.base
      (bounded.decaps prepared.secretKey) (bounded.resume _ _ _)).1
  · simpa only [Nat.zero_add] using isQueryBoundP_bind (rootCoins_roots (prepare baseImpl kem protocol))
      (fun prepared _ => (resume_bounds source baseImpl kem protocol prepared _ _ _ _ _ _ bounded.base
        (bounded.decaps prepared.secretKey) (bounded.resume _ _ _)).2)

/-- Explicit local work is lifted into the ordinary HMAC game with no hidden base capability. -/
def hmacCoins {Result : Type} (client : ProbComp Result) : OracleComp HmacAdversarySpec Result :=
  OracleComp.liftComp client HmacAdversarySpec

theorem hmacCoins_bind {A B : Type} (client : ProbComp A) (next : A → ProbComp B) :
    hmacCoins (client >>= next) = (hmacCoins client >>= fun answer => hmacCoins (next answer)) := by
  simp only [hmacCoins, liftComp_bind]

noncomputable def challengeFrame (hmac : HmacSha512) (frame : Prefix Bool) : OracleComp HmacAdversarySpec Bool := do
  let block ← HmacAdversarySpec.query (.inr rootExpandInput)
  hmacCoins (Prod.fst <$> finishWithRoot hmac frame (first32 block))

noncomputable def selectedRun (hmac : HmacSha512) (client : OracleComp RootSpec Bool)
    (index : Nat) (cache : RootOracle.QueryCache) : OracleComp HmacAdversarySpec Bool := do
  let frame ← hmacCoins (scan client index cache)
  challengeFrame hmac frame

theorem selectedRun_indexed (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat) :
    selectedRun hmac client index ∅ = indexedReduction hmac client index := by
  simp [selectedRun, indexedReduction, expandReduction, scanSampler, scanObserver,
    hmacCoins, challengeFrame]

set_option backward.isDefEq.respectTransparency false in
theorem challengeFrame_complete (hmac : HmacSha512) (result : Bool) (cache : RootOracle.QueryCache) :
    (challengeFrame hmac (.complete result, cache)).IsQueryBoundP IsHmacUniformQuery 0 := by
  simp only [challengeFrame, isQueryBoundP_query_bind_iff, IsHmacUniformQuery,
    not_false_eq_true, true_or, if_false, true_and]
  intro block
  simp [finishWithRoot, hmacCoins]

set_option backward.isDefEq.respectTransparency false in
/-- The selected HMAC query contributes no local uniform request; every actual suffix operation remains charged. -/
theorem challengeFrame_pending (hmac : HmacSha512) (message : Message)
    (next : RootOutput → OracleComp RootSpec Bool) (cache : RootOracle.QueryCache)
    (qCoins qRoots : Nat) (coins : ∀ answer, (next answer).IsQueryBoundP IsCoin qCoins)
    (roots : ∀ answer, (next answer).IsQueryBoundP IsRoot qRoots) :
    (challengeFrame hmac (.pending message next, cache)).IsQueryBoundP IsHmacUniformQuery
      (qCoins + 64 * qRoots) := by
  simp only [challengeFrame, isQueryBoundP_query_bind_iff, IsHmacUniformQuery,
    not_false_eq_true, true_or, if_false, true_and]
  intro block
  apply local_hmac_uniform_query_bound
  cases hit : cache message with
  | none =>
      simpa only [finishWithRoot, hit, IsTotalQueryBound, isQueryBound_map_iff] using
        root_run_uniform hmac (next (first32 block)) qCoins qRoots (coins _) (roots _)
          (cache.cacheQuery message (first32 block))
  | some answer =>
      simpa only [finishWithRoot, hit, IsTotalQueryBound, isQueryBound_map_iff] using
        root_run_uniform hmac (next answer) qCoins qRoots (coins _) (roots _) cache

theorem selectedRun_pure (hmac : HmacSha512) (result : Bool) (index : Nat) (cache : RootOracle.QueryCache) :
    selectedRun hmac (pure result) index cache = challengeFrame hmac (.complete result, cache) := by
  simp [selectedRun, hmacCoins]

theorem selectedRun_coin (hmac : HmacSha512) (coin : unifSpec.Domain)
    (next : unifSpec.Range coin → OracleComp RootSpec Bool) (index : Nat) (cache : RootOracle.QueryCache) :
    selectedRun hmac (RootSpec.query (.inl coin) >>= next) index cache = (do
      let answer ← hmacCoins (unifSpec.query coin)
      selectedRun hmac (next answer) index cache) := by
  simp only [selectedRun, scan_coin, hmacCoins_bind, bind_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem selectedRun_root_zero (hmac : HmacSha512) (message : Message)
    (next : RootOutput → OracleComp RootSpec Bool) (cache : RootOracle.QueryCache) :
    selectedRun hmac (RootSpec.query (.inr message) >>= next) 0 cache =
      challengeFrame hmac (.pending message next, cache) := by
  unfold selectedRun
  rw [scan_root_zero]
  simp [hmacCoins]

theorem selectedRun_root_succ (hmac : HmacSha512) (message : Message)
    (next : RootOutput → OracleComp RootSpec Bool) (index : Nat) (cache : RootOracle.QueryCache) :
    selectedRun hmac (RootSpec.query (.inr message) >>= next) (index + 1) cache = (do
      let (answer, updated) ← hmacCoins ((uniformImpl (.inr message)).run cache)
      selectedRun hmac (next answer) index updated) := by
  simp only [selectedRun, scan_root_succ, hmacCoins_bind, bind_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The indexed client charges the actual source coins once across its prefix and suffix, plus at most 64 draws per original root request. -/
theorem selectedRun_uniform (hmac : HmacSha512) (client : OracleComp RootSpec Bool)
    (index : Nat) (cache : RootOracle.QueryCache) (qCoins qRoots : Nat)
    (coins : client.IsQueryBoundP IsCoin qCoins) (roots : client.IsQueryBoundP IsRoot qRoots) :
    (selectedRun hmac client index cache).IsQueryBoundP IsHmacUniformQuery (qCoins + 64 * qRoots) := by
  induction client using OracleComp.inductionOn generalizing index cache qCoins qRoots with
  | pure result =>
      rw [selectedRun_pure]
      exact (challengeFrame_complete hmac result cache).mono (Nat.zero_le _)
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at coins roots
      cases request with
      | inl coin =>
          have positive : 0 < qCoins := by simpa [IsCoin] using coins.1
          have tailsCoin : ∀ answer, (next answer).IsQueryBoundP IsCoin (qCoins - 1) := by
            intro answer
            simpa [IsCoin] using coins.2 answer
          have tailsRoot : ∀ answer, (next answer).IsQueryBoundP IsRoot qRoots := by
            intro answer
            simpa [IsRoot] using roots.2 answer
          rw [selectedRun_coin]
          apply (isQueryBoundP_bind
            (local_hmac_uniform_query_bound _ (show (unifSpec.query coin : ProbComp _).IsTotalQueryBound 1 from
              ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩))
            (fun answer _ => ih answer index cache _ _ (tailsCoin answer) (tailsRoot answer))).mono
          omega
      | inr message =>
          have positive : 0 < qRoots := by simpa [IsRoot] using roots.1
          have tailsCoin : ∀ answer, (next answer).IsQueryBoundP IsCoin qCoins := by
            intro answer
            simpa [IsCoin] using coins.2 answer
          have tailsRoot : ∀ answer, (next answer).IsQueryBoundP IsRoot (qRoots - 1) := by
            intro answer
            simpa [IsRoot] using roots.2 answer
          cases index with
          | zero =>
              rw [selectedRun_root_zero]
              exact (challengeFrame_pending hmac message next cache _ _ tailsCoin tailsRoot).mono (by omega)
          | succ index =>
              rw [selectedRun_root_succ]
              have step : ((uniformImpl (.inr message)).run cache).IsTotalQueryBound 32 := by
                change ((cachedImpl ($ᵗ RootOutput) (.inr message)).run cache).IsTotalQueryBound 32
                simpa only [IsCoin, IsRoot, if_false, if_true, Nat.zero_add] using
                  cached_step ($ᵗ RootOutput) 32 (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
                    (.inr message) cache
              apply (isQueryBoundP_bind (local_hmac_uniform_query_bound _ step)
                (fun answer _ => ih answer.1 index answer.2 _ _ (tailsCoin answer.1) (tailsRoot answer.1))).mono
              omega

theorem hmac_real_step (hmac : HmacSha512) (secret : HmacBlock) (request : HmacAdversarySpec.Domain) :
    (hmacRealImpl hmac secret request).IsTotalQueryBound (if IsHmacUniformQuery request then 1 else 0) := by
  cases request with
  | inl request => exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr request => trivial

theorem hmac_real_run {Result : Type} (hmac : HmacSha512) (secret : HmacBlock)
    (client : OracleComp HmacAdversarySpec Result) (q : Nat) (bounded : client.IsQueryBoundP IsHmacUniformQuery q) :
    (simulateQ (hmacRealImpl hmac secret) client).IsTotalQueryBound q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_query_bind]
      apply (isTotalQueryBound_bind (hmac_real_step hmac secret request)
        (fun answer => ih answer _ (bounded.2 answer))).mono
      by_cases selected : IsHmacUniformQuery request
      · have positive := bounded.1.resolve_left (not_not.mpr selected)
        simp only [selected, if_true]
        omega
      · simp only [selected, if_false, Nat.zero_add, le_refl]

/-- The real HMAC challenger pays its single hidden 64-byte key sample in addition to the client's coins. -/
theorem hmac_real_game (hmac : HmacSha512) (client : OracleComp HmacAdversarySpec Bool)
    (q : Nat) (bounded : client.IsQueryBoundP IsHmacUniformQuery q) :
    (hmacPrfRealGame hmac client).IsTotalQueryBound (64 + q) := by
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
    (fun secret => hmac_real_run hmac secret client q bounded)

set_option backward.isDefEq.respectTransparency false in
theorem hmac_random_step (request : HmacAdversarySpec.Domain) (cache : HmacOracle.QueryCache) :
    ((hmacRandomImpl request).run cache).IsTotalQueryBound
      ((if IsHmacUniformQuery request then 1 else 0) + (if IsHmacChallengeQuery request then 64 else 0)) := by
  cases request with
  | inl coin =>
      change (((unifSpec.query coin : ProbComp (unifSpec.Range coin)) >>= fun answer =>
        pure (answer, cache))).IsTotalQueryBound 1
      exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr message =>
      simp only [IsHmacUniformQuery, IsHmacChallengeQuery, if_false, if_true, Nat.zero_add,
        hmacRandomImpl, QueryImpl.add_apply_inr, OracleSpec.randomOracle]
      cases hit : cache message with
      | none =>
          rw [QueryImpl.withCaching_run_none _ hit]
          simpa only [uniformSampleImpl, IsTotalQueryBound, isQueryBound_map_iff] using
            CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64
      | some block =>
          rw [QueryImpl.withCaching_run_some _ hit]
          trivial

theorem hmac_random_run {Result : Type} (client : OracleComp HmacAdversarySpec Result)
    (qCoins qFamily : Nat) (coinBound : client.IsQueryBoundP IsHmacUniformQuery qCoins)
    (familyBound : client.IsQueryBoundP IsHmacChallengeQuery qFamily) (cache : HmacOracle.QueryCache) :
    ((simulateQ hmacRandomImpl client).run cache).IsTotalQueryBound (qCoins + 64 * qFamily) := by
  induction client using OracleComp.inductionOn generalizing qCoins qFamily cache with
  | pure result => trivial
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at coinBound familyBound
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isTotalQueryBound_bind (hmac_random_step request cache)
        (fun answer => ih answer.1 _ _ (coinBound.2 answer.1) (familyBound.2 answer.1) answer.2)).mono
      have hc := coinBound.1
      have hf := familyBound.1
      have familyStep : ∀ n, 0 < n → 64 * (n - 1) + 64 = 64 * n := by
        intro n hn
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := familyStep qFamily (by omega)
      all_goals omega

/-- The random challenger has no sampled HMAC key; only new table entries add randomness. -/
theorem hmac_random_game (client : OracleComp HmacAdversarySpec Bool) (qCoins qFamily : Nat)
    (coinBound : client.IsQueryBoundP IsHmacUniformQuery qCoins) (familyBound : client.IsQueryBoundP IsHmacChallengeQuery qFamily) :
    (hmacPrfRandomGame client).IsTotalQueryBound (qCoins + 64 * qFamily) := by
  simpa only [hmacPrfRandomGame, StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff] using
    hmac_random_run client qCoins qFamily coinBound familyBound ∅

/-- Each exact ordinary reduction has one challenge call and the complete source-local uniform budget. -/
theorem indexed_bounds (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat)
    (qCoins qRoots : Nat) (coins : client.IsQueryBoundP IsCoin qCoins)
    (roots : client.IsQueryBoundP IsRoot qRoots) :
    (indexedReduction hmac client index).IsQueryBoundP IsHmacUniformQuery (qCoins + 64 * qRoots) ∧
    (indexedReduction hmac client index).IsQueryBoundP IsHmacChallengeQuery 1 := by
  constructor
  · rw [← selectedRun_indexed]
    exact selectedRun_uniform hmac client index ∅ qCoins qRoots coins roots
  · exact expandReduction_hmac_query_bound _ _

/-- Complete real and random HMAC challengers both include a checked cap of 64 additional draws, respectively for the key and the one fresh answer. -/
theorem indexed_uniform_ledger (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat)
    (qCoins qRoots : Nat) (coins : client.IsQueryBoundP IsCoin qCoins)
    (roots : client.IsQueryBoundP IsRoot qRoots) :
    (hmacPrfRealGame hmac (indexedReduction hmac client index)).IsTotalQueryBound
      (64 + qCoins + 64 * qRoots) ∧
    (hmacPrfRandomGame (indexedReduction hmac client index)).IsTotalQueryBound
      (64 + qCoins + 64 * qRoots) := by
  have caps := indexed_bounds hmac client index qCoins qRoots coins roots
  exact ⟨(hmac_real_game hmac _ _ caps.1).mono (by omega),
    (hmac_random_game _ _ _ caps.1 caps.2).mono (by omega)⟩

/-- The concrete private protocol inherits its actual local-work budget and at most one initial plus every post root request. -/
theorem source_uniform_ledger
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : SamplerBounds baseImpl kem protocol qKeygen qEncap qBase qDecap
      uPre bPre dPre uPost bPost dPost privatePost) :
    let client := rootReduction source baseImpl kem protocol
    let Q := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) +
      (uPost + qBase * bPost + qDecap * (dPost + privatePost))
    client.IsQueryBoundP IsRoot (1 + privatePost) ∧
    (expandedGame hmac client).IsTotalQueryBound (Q + 64 * (1 + privatePost)) ∧
    (uniformGame client).IsTotalQueryBound (Q + 32 * (1 + privatePost)) ∧
    ∀ index,
      (hmacPrfRealGame hmac (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + Q + 64 * (1 + privatePost)) ∧
      (hmacPrfRandomGame (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + Q + 64 * (1 + privatePost)) := by
  dsimp only
  have caps := reduction_bounds source baseImpl kem protocol _ _ _ _ _ _ _ _ _ _ _ bounded
  refine ⟨caps.2, ?_, ?_, fun index => indexed_uniform_ledger hmac _ index _ _ caps.1 caps.2⟩
  · simpa only [expandedGame, StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff] using
      root_run_uniform hmac _ _ _ caps.1 caps.2 ∅
  · simpa only [uniformGame, StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff] using
      uniform_run_uniform _ _ _ caps.1 caps.2 ∅

end BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds

/-! Persistent kernel-dependency audit for every statement in this module. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.cached_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.cached_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.cached_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.cached_run

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.root_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.root_run_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.uniform_run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.uniform_run_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.rootCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.rootCoins_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.rootCoins_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.rootCoins_roots

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.query_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_uniform_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_uniform_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_uniform_run

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_uniform_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_root_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_root_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.post_root_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.resume_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.resume_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmacCoins_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmacCoins_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_indexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_indexed

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.challengeFrame_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.challengeFrame_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.challengeFrame_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.challengeFrame_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_root_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_root_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_root_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_root_succ

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.selectedRun_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_real_step' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_real_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_real_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_real_run

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_real_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_real_game

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_random_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_random_step

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_random_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_random_run

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_random_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.hmac_random_game

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.indexed_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.indexed_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.indexed_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.indexed_uniform_ledger

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.source_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds.source_uniform_ledger
