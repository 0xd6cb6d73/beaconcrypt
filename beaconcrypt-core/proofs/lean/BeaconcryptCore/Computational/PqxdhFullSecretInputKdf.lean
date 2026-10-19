import BeaconcryptCore.Computational.PqxdhSecretInputKdf
import BeaconcryptCore.Computational.CtxComputationalSecurity
import BeaconcryptCore.Computational.PqxdhProjectionCollisions

/-!
# The complete source HKDF expansion at one secret input

The first block is shared by the 32-byte, 64-byte and 76-byte observations.
The second HMAC message contains the complete first block. Public local
evaluations remain real. This module concerns the output interface and its
primitive reductions, not the implementation or internal security of HMAC.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhFullSecretInputKdf

open PqxdhSecretInputKdf PqxdhJointKdfGame

abbrev FullOutput := List.Vector UInt8 76
abbrev NonceOutput := List.Vector UInt8 12

def firstExpandInput (domain : FixedHkdfDomain) : Pqxdh.Bytes := domain.info ++ [1]

def secondExpandInput (domain : FixedHkdfDomain) (first : HmacBlock) : Pqxdh.Bytes :=
  first.toList ++ domain.info ++ [2]

def noncePart (block : HmacBlock) : NonceOutput := List.Vector.take 12 block

def joinBlocks (first second : HmacBlock) : FullOutput :=
  first ++ noncePart second

def expandFull (hmac : HmacSha512) (domain : FixedHkdfDomain)
    (prk : HmacBlock) : FullOutput :=
  let first := hmac.eval prk (firstExpandInput domain)
  joinBlocks first (hmac.eval prk (secondExpandInput domain first))

abbrev FullObserver (Context : Type) := Context → FullOutput → ProbComp Bool

def fullExpandReduction {Context : Type} (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context) :
    OracleComp HmacAdversarySpec Bool := do
  let (context, _) ← liftM (m := ProbComp) sample
  let first ← liftM (HmacAdversarySpec.query (.inr (firstExpandInput domain)))
  let second ← liftM (HmacAdversarySpec.query (.inr (secondExpandInput domain first)))
  liftM (observer context (joinBlocks first second))

/-- The second query is fresh even though it depends on the first answer. -/
theorem secondExpandInput_ne_first (domain : FixedHkdfDomain) (first : HmacBlock) :
    secondExpandInput domain first ≠ firstExpandInput domain := by
  intro equality
  have lengths := congrArg List.length equality
  simp [secondExpandInput, firstExpandInput] at lengths

/-- The entire adaptive two-query HMAC simulation equals two fresh blocks. -/
theorem fullExpandReduction_random {Context : Type} (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context) :
    hmacPrfRandomGame (fullExpandReduction domain sample observer) =
      (do let (context, _) ← sample
          let first ← $ᵗ HmacBlock
          let second ← $ᵗ HmacBlock
          observer context (joinBlocks first second)) := by
  simp [hmacPrfRandomGame, fullExpandReduction, hmacRandomImpl,
    QueryImpl.simulateQ_add_liftM_left, OracleSpec.randomOracle,
    uniformSampleImpl, StateT.run'_eq, QueryCache.cacheQuery_of_ne,
    secondExpandInput_ne_first]

/-- Splitting a fixed-width byte vector retains both parts without loss. -/
def vectorSplitEquiv (left right : Nat) :
    List.Vector UInt8 (left + right) ≃
      (List.Vector UInt8 left × List.Vector UInt8 right) where
  toFun bytes :=
    (⟨bytes.toList.take left, by simp⟩, ⟨bytes.toList.drop left, by simp⟩)
  invFun parts := parts.1 ++ parts.2
  left_inv bytes := List.Vector.toList_injective (List.take_append_drop left bytes.toList)
  right_inv parts := Prod.ext
    (List.Vector.toList_injective (by simp))
    (List.Vector.toList_injective (by simp))

/-- Projecting a uniform byte vector gives a uniform prefix. -/
theorem take_uniform (left right : Nat) :
    𝒮[(fun bytes => (vectorSplitEquiv left right bytes).1) <$>
      ($ᵗ List.Vector UInt8 (left + right))] =
      𝒮[$ᵗ List.Vector UInt8 left] := by
  have split := evalSPMF_map_bijective_uniform_cross
    (List.Vector UInt8 (left + right)) (vectorSplitEquiv left right)
    (vectorSplitEquiv left right).bijective
  have projected := congrArg (fun distribution => Prod.fst <$> distribution) split
  simpa only [← evalSPMF_map, Functor.map_map] using
    projected.trans (show Prod.fst <$>
      𝒮[$ᵗ (List.Vector UInt8 left × List.Vector UInt8 right)] =
        𝒮[$ᵗ List.Vector UInt8 left] from by
      rw [← evalSPMF_map]
      exact evalSPMF_map_fst_uniformSample_prod)

/-- Two independent byte vectors concatenate to a uniform full vector. -/
theorem append_uniform (left right : Nat) :
    𝒮[(fun parts : List.Vector UInt8 left × List.Vector UInt8 right =>
        parts.1 ++ parts.2) <$> ($ᵗ (List.Vector UInt8 left × List.Vector UInt8 right))] =
      𝒮[$ᵗ List.Vector UInt8 (left + right)] := by
  exact evalSPMF_map_bijective_uniform_cross
    (List.Vector UInt8 left × List.Vector UInt8 right)
    (vectorSplitEquiv left right).symm (vectorSplitEquiv left right).symm.bijective

theorem pairSample {A B : Type} [SampleableType A] [SampleableType B] :
    (do let a ← $ᵗ A
        let b ← $ᵗ B
        pure (a, b)) = ($ᵗ (A × B)) := by
  change _ = (Prod.mk <$> ($ᵗ A) <*> ($ᵗ B))
  simp [monad_norm]

/-- The production 76-byte observation is uniform jointly, including its shared prefix. -/
theorem joinBlocks_uniform :
    𝒮[(do let first ← $ᵗ HmacBlock
          let second ← $ᵗ HmacBlock
          pure (joinBlocks first second))] = 𝒮[$ᵗ FullOutput] := by
  have nonceUniform : 𝒮[noncePart <$> ($ᵗ HmacBlock)] =
      𝒮[$ᵗ NonceOutput] := take_uniform 12 52
  have projected : 𝒮[(do let first ← $ᵗ HmacBlock
                         let second ← $ᵗ HmacBlock
                         pure (joinBlocks first second))] =
      𝒮[(do let first ← $ᵗ HmacBlock
            let nonce ← $ᵗ NonceOutput
            pure (first ++ nonce))] := by
    refine evalSPMF_bind_congr' (m := ProbComp) ($ᵗ HmacBlock) fun first => ?_
    change 𝒮[($ᵗ HmacBlock) >>= fun second =>
      (fun nonce : NonceOutput => (pure (first ++ nonce) : ProbComp FullOutput))
        (noncePart second)] = _
    rw [← bind_map_left noncePart ($ᵗ HmacBlock)
      (fun nonce : NonceOutput => (pure (first ++ nonce) : ProbComp FullOutput)),
      evalSPMF_bind, nonceUniform, ← evalSPMF_bind]
  rw [projected]
  have factored : (do let first ← $ᵗ HmacBlock
                      let nonce ← $ᵗ NonceOutput
                      pure (first ++ nonce)) =
      (fun parts : HmacBlock × NonceOutput => parts.1 ++ parts.2) <$>
        (do let first ← $ᵗ HmacBlock
            let nonce ← $ᵗ NonceOutput
            pure (first, nonce)) := by
    simp [monad_norm]
  rw [factored, pairSample]
  exact append_uniform 64 12

/-- Functional correspondence for the two actual labels; no security premise is included. -/
def SourceFullCorrect (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) : Prop :=
  ∀ domain input, PqxdhJointKdf.productionStream source.crypto (domain.address input) =
    expandFull hmac domain (extract hmac input)

def sourceFullGame {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (domain : FixedHkdfDomain) (sample : SecretInputSampler Context)
    (observer : FullObserver Context) : ProbComp Bool := do
  let (context, input) ← sample
  observer context (PqxdhJointKdf.productionStream source.crypto (domain.address input))

noncomputable def independentFullGame {Context : Type}
    (sample : SecretInputSampler Context) (observer : FullObserver Context) : ProbComp Bool := do
  let (context, _) ← sample
  let output ← $ᵗ FullOutput
  observer context output

def fullExtractReduction {Context : Type} (hmac : HmacSha512) (domain : FixedHkdfDomain)
    (observer : FullObserver Context) : Context → HmacBlock → ProbComp Bool :=
  fun context prk => observer context (expandFull hmac domain prk)

/-- Real HMAC simulation retains the full output and every observer continuation. -/
theorem fullExpandReduction_real {Context : Type} (hmac : HmacSha512)
    (domain : FixedHkdfDomain) (key : HmacBlock) (sample : SecretInputSampler Context)
    (observer : FullObserver Context) :
    simulateQ (hmacRealImpl hmac key) (fullExpandReduction domain sample observer) =
      (do let (context, _) ← sample
          observer context (expandFull hmac domain key)) := by
  simp [fullExpandReduction, hmacRealImpl, QueryImpl.simulateQ_add_liftM_left, expandFull]

theorem sourceFullGame_eq_extract {Context : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context) :
    sourceFullGame source domain sample observer =
      extractRealGame hmac sample (fullExtractReduction hmac domain observer) := by
  unfold SourceFullCorrect at correct
  simp only [sourceFullGame, extractRealGame, fullExtractReduction, correct]

/-- The PRK sample commutes with the complete independent sampler and output continuation. -/
theorem fullExtractUniform_eq_hmacReal {Context : Type} (hmac : HmacSha512)
    (domain : FixedHkdfDomain) (sample : SecretInputSampler Context)
    (observer : FullObserver Context) :
    𝒮[extractUniformGame sample (fullExtractReduction hmac domain observer)] =
      𝒮[hmacPrfRealGame hmac (fullExpandReduction domain sample observer)] := by
  simpa [hmacPrfRealGame, fullExpandReduction_real, extractUniformGame,
    fullExtractReduction] using
      evalSPMF_sample_comm (sample : ProbComp (Context × Pqxdh.Bytes)) ($ᵗ HmacBlock)
        (fun pair key => observer pair.1 (expandFull hmac domain key))

/-- Any continuation observes exactly a uniform full output in the HMAC random world. -/
theorem fullHmacRandom_eq_independent {Context : Type} (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context) :
    𝒮[hmacPrfRandomGame (fullExpandReduction domain sample observer)] =
      𝒮[independentFullGame sample observer] := by
  rw [fullExpandReduction_random]
  refine evalSPMF_bind_congr' (m := ProbComp) (sample : ProbComp (Context × Pqxdh.Bytes))
    fun pair => ?_
  rcases pair with ⟨context, input⟩
  have observed := congrArg (fun distribution => distribution >>=
    fun output => 𝒮[observer context output]) joinBlocks_uniform
  simpa only [← evalSPMF_bind, bind_assoc, pure_bind] using observed

/-- A loss-one full-output reduction at the actual joint input/context sampler. -/
theorem sourceFullAdvantage_le_extract_add_hmac {Context : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context) :
    (sourceFullGame source domain sample observer).boolDistAdvantage
        (independentFullGame sample observer) ≤
      (extractRealGame hmac sample (fullExtractReduction hmac domain observer)).boolDistAdvantage
        (extractUniformGame sample (fullExtractReduction hmac domain observer)) +
      (hmacPrfRealGame hmac (fullExpandReduction domain sample observer)).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction domain sample observer)) := by
  have real := evalDist_eq_of_evalSPMF_eq _ _
    (fullExtractUniform_eq_hmacReal hmac domain sample observer)
  have random := evalDist_eq_of_evalSPMF_eq _ _
    (fullHmacRandom_eq_independent domain sample observer)
  simpa only [sourceFullGame_eq_extract source hmac correct, ProbComp.boolDistAdvantage,
    real, random] using
      ProbComp.boolDistAdvantage_triangle (sourceFullGame source domain sample observer)
        (extractUniformGame sample (fullExtractReduction hmac domain observer))
        (independentFullGame sample observer)

/-- Exactly two challenge HMAC queries suffice; local public evaluations stay local. -/
theorem fullExpandReduction_hmac_query_bound {Context : Type}
    (domain : FixedHkdfDomain) (sample : SecretInputSampler Context)
    (observer : FullObserver Context) :
    (fullExpandReduction domain sample observer).IsQueryBoundP IsHmacChallengeQuery 2 := by
  unfold fullExpandReduction
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 2) (local_no_hmac_query sample) ?_
  rintro ⟨context, input⟩ _
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by decide), fun first => ?_⟩
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr (by simp [IsHmacChallengeQuery]), fun second =>
    local_no_hmac_query (observer context (joinBlocks first second))⟩

def IsHmacUniformQuery : HmacAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsHmacUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Local probabilistic work is charged, even though it has no challenge-key access. -/
theorem local_uniform_query_bound {A : Type} {computation : ProbComp A} {q : Nat}
    (bound : computation.IsTotalQueryBound q) :
    (OracleComp.liftComp computation HmacAdversarySpec).IsQueryBoundP IsHmacUniformQuery q := by
  apply OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := HmacAdversarySpec) (p := fun _ => True)
    (hpq := fun query => by simp [IsHmacUniformQuery, SubSpec.onQuery])
  simpa only [OracleComp.IsQueryBoundP, OracleComp.IsTotalQueryBound,
    not_true_eq_false, false_or, ite_true] using bound

/-- The sampler and observer budgets are retained separately from challenge queries. -/
theorem fullExpandReduction_uniform_query_bound {Context : Type}
    (domain : FixedHkdfDomain) (sample : SecretInputSampler Context)
    (observer : FullObserver Context) {qSample qObserver : Nat}
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserver) :
    (fullExpandReduction domain sample observer).IsQueryBoundP IsHmacUniformQuery
      (qSample + qObserver) := by
  unfold fullExpandReduction
  refine OracleComp.isQueryBoundP_bind (local_uniform_query_bound sampleBound) ?_
  rintro ⟨context, input⟩ _
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [IsHmacUniformQuery]), fun first => ?_⟩
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp [IsHmacUniformQuery]), fun second =>
    local_uniform_query_bound (observerBound context (joinBlocks first second))⟩

def initialPrefix (output : FullOutput) : HmacBlock := List.Vector.take 64 output

/-- Initial derivation and record derivation expose exactly the same first HMAC block. -/
theorem initialPrefix_joinBlocks (first second : HmacBlock) :
    initialPrefix (joinBlocks first second) = first := by
  apply List.Vector.toList_injective
  change (first.toList ++ (noncePart second).toList).take 64 = first.toList
  simp

theorem initialPrefix_expandFull (hmac : HmacSha512) (domain : FixedHkdfDomain)
    (prk : HmacBlock) :
    initialPrefix (expandFull hmac domain prk) = hmac.eval prk (firstExpandInput domain) := by
  exact initialPrefix_joinBlocks _ _

theorem initialPrefix_uniform :
    𝒮[initialPrefix <$> ($ᵗ FullOutput)] = 𝒮[$ᵗ HmacBlock] := by
  exact take_uniform 64 12

/-- The root projection never uses the second expansion block. -/
theorem rootProjection_joinBlocks (first second : HmacBlock) :
    PqxdhJointKdf.rootProjection (joinBlocks first second) =
      (PqxdhSecretInputKdf.first32 first).toList := by
  change (first.toList ++ (noncePart second).toList).take 32 = first.toList.take 32
  exact List.take_append_of_le_length (by simp)

/-- The full functional contract entails the existing exact 32-byte root contract. -/
theorem SourceFullCorrect.root {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) : SourceRootCorrect source hmac := by
  intro input
  exact (PqxdhJointKdf.rootSecret_eq_rootProjection source.crypto source.prefixConsistent input).trans
    ((congrArg PqxdhJointKdf.rootProjection (correct .pqxdh input)).trans
      (rootProjection_joinBlocks _ _))

/-- Both source initial chains are projections of the same complete expansion. -/
theorem SourceFullCorrect.initialChains {source : FixedHkdfSha512NoSaltSource}
    {hmac : HmacSha512} (correct : SourceFullCorrect source hmac) (input : Pqxdh.Bytes) :
    Pqxdh.rootChains source.crypto input = PqxdhJointKdf.initialProjection
      (expandFull hmac .ratchet (extract hmac input)) := by
  exact (PqxdhJointKdf.rootChains_eq_initialProjection source.crypto
    source.prefixConsistent input).trans
      (congrArg PqxdhJointKdf.initialProjection (correct .ratchet input))

/-- The source's entire 76-byte step is the two-block output in the reduction. -/
theorem SourceFullCorrect.ratchetStep {source : FixedHkdfSha512NoSaltSource}
    {hmac : HmacSha512} (correct : SourceFullCorrect source hmac) (input : Pqxdh.Bytes) :
    Pqxdh.ratchetOut source.crypto input =
      (expandFull hmac .ratchet (extract hmac input)).toList := by
  exact congrArg List.Vector.toList (correct .ratchet input)

/-- Distinct canonical slots are independent in this justified ideal output; repeated projections still alias. -/
theorem projectedOutput_uniform :
    𝒮[(fun output : FullOutput =>
      (JointKdfProjection.first32.project output, JointKdfProjection.second32.project output,
        JointKdfProjection.final12.project output)) <$> ($ᵗ FullOutput)] =
      𝒮[$ᵗ (RootOutput × RootOutput × NonceOutput)] := by
  exact PqxdhProjectionCollisions.evalSPMF_split_uniformJointKdfStream

/-- The source game charges every sampler and observer random query. -/
theorem sourceFullGame_uniform_query_bound {Context : Type}
    (source : FixedHkdfSha512NoSaltSource) (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context)
    {qSample qObserver : Nat} (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserver) :
    (sourceFullGame source domain sample observer).IsTotalQueryBound (qSample + qObserver) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun pair => observerBound _ _)

/-- Uniform Extract adds the complete 64-byte challenger key sample. -/
theorem fullExtractUniform_uniform_query_bound {Context : Type}
    (hmac : HmacSha512) (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context)
    {qSample qObserver : Nat} (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserver) :
    (extractUniformGame sample (fullExtractReduction hmac domain observer)).IsTotalQueryBound
      (qSample + (64 + qObserver)) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun pair =>
    OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      (fun key => observerBound _ _))

/-- The real PRF challenger samples its hidden key before the complete reduction. -/
theorem fullHmacReal_uniform_query_bound {Context : Type}
    (hmac : HmacSha512) (domain : FixedHkdfDomain)
    (sample : SecretInputSampler Context) (observer : FullObserver Context)
    {qSample qObserver : Nat} (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserver) :
    (hmacPrfRealGame hmac (fullExpandReduction domain sample observer)).IsTotalQueryBound
      (64 + (qSample + qObserver)) := by
  unfold hmacPrfRealGame
  refine OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) fun key => ?_
  rw [fullExpandReduction_real]
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun pair => observerBound _ _)

/-- The random PRF challenger charges both complete blocks, including unused suffix bytes. -/
theorem fullHmacRandom_uniform_query_bound {Context : Type}
    (domain : FixedHkdfDomain) (sample : SecretInputSampler Context)
    (observer : FullObserver Context) {qSample qObserver : Nat}
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserver) :
    (hmacPrfRandomGame (fullExpandReduction domain sample observer)).IsTotalQueryBound
      (qSample + (64 + (64 + qObserver))) := by
  rw [fullExpandReduction_random]
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun pair =>
    OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) (fun first =>
        OracleComp.isTotalQueryBound_bind
          (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
          (fun second => observerBound _ _)))

/-- Sampling a full ideal output charges its 76 bytes explicitly. -/
theorem independentFullGame_uniform_query_bound {Context : Type}
    (sample : SecretInputSampler Context) (observer : FullObserver Context)
    {qSample qObserver : Nat} (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserver) :
    (independentFullGame sample observer).IsTotalQueryBound
      (qSample + (76 + qObserver)) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun pair =>
    OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
      (fun output => observerBound _ _))

end BeaconcryptCore.Computational.PqxdhFullSecretInputKdf

/--
info: 'BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.sourceFullAdvantage_le_extract_add_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.sourceFullAdvantage_le_extract_add_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullExpandReduction_uniform_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullExpandReduction_uniform_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullHmacRandom_uniform_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.fullHmacRandom_uniform_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.SourceFullCorrect.initialChains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.SourceFullCorrect.initialChains

/--
info: 'BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.projectedOutput_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.projectedOutput_uniform
