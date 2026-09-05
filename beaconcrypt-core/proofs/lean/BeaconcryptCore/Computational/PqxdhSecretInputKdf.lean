import BeaconcryptCore.Computational.PqxdhJointKdfGame
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# A secret-input PQXDH root game and an Extract/HMAC decomposition

Only the honest root is replaced. The adversary is ordinary probabilistic code with the public source implementation available for local evaluation in BOTH worlds. It receives public side information from a joint sampler, never the sampled IKM or PRK. This rules out the public-oracle replacement defect without banning guesses or local HKDF evaluation.

The two endpoints are (1) pseudorandomness of the fixed-zero-salt HMAC-Extract PRK for the specified joint input/side-information distribution, against a distinguisher receiving the entire PRK, and (2) the ordinary HMAC PRF game with an independent uniform secret 64-byte key and a public-message oracle. Neither endpoint assumes protocol secrecy. No small bound for concrete SHA-512 Extract is proved: a secret or high-entropy IKM alone does not establish this endpoint, and ordinary secret-key HMAC PRF security does not apply to the public fixed Extract key.

This result covers the 32-byte root (one Expand block), with a functional source equation. It does not replace all public HKDF queries by a random oracle, establish 76-byte joint-stream security, or compose evolving session keys.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhSecretInputKdf

open PqxdhJointKdfGame

abbrev HmacBlock := List.Vector UInt8 64
abbrev RootOutput := List.Vector UInt8 32
abbrev HmacOracle := Pqxdh.Bytes →ₒ HmacBlock
abbrev HmacAdversarySpec := unifSpec + HmacOracle

/-- Concrete HMAC evaluation, with its key argument explicit. This field has no security law. -/
structure HmacSha512 where
  eval : HmacBlock → Pqxdh.Bytes → HmacBlock

/-- RFC 5869's absent salt is a HashLen-byte zero string. -/
def zeroSalt : HmacBlock := List.Vector.replicate 64 0

/-- The production root uses the first Expand block at the exact root label. -/
def rootExpandInput : Pqxdh.Bytes := Pqxdh.INFO_PQ ++ [1]

def first32 (block : HmacBlock) : RootOutput := List.Vector.take 32 block

def extract (hmac : HmacSha512) (input : Pqxdh.Bytes) : HmacBlock :=
  hmac.eval zeroSalt input

def expandRoot (hmac : HmacSha512) (prk : HmacBlock) : RootOutput :=
  first32 (hmac.eval prk rootExpandInput)

/-- An algorithmic equation, separate from both cryptographic security endpoints. -/
def SourceRootCorrect (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) : Prop :=
  ∀ input, Pqxdh.rootSecret source.crypto input =
    (expandRoot hmac (extract hmac input)).toList

/-- The public transcript and secret input may be correlated; the distribution must be justified separately. -/
abbrev SecretInputSampler (Context : Type) := ProbComp (Context × Pqxdh.Bytes)

/-- Local public computations, including HKDF on every guess, are permitted in either branch. -/
abbrev RootObserver (Context : Type) := Context → RootOutput → ProbComp Bool

/-- Real output of the actual 32-byte source wrapper, without replacing public evaluations. -/
def sourceRootGame {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : SecretInputSampler Context) (observer : RootObserver Context) : ProbComp Bool := do
  let (context, input) ← sample
  observer context ⟨Pqxdh.rootSecret source.crypto input,
    Pqxdh.rootSecret_length source.crypto input⟩

/-- Only the honest root is independent uniform; the same observer code retains all public operations. -/
noncomputable def independentRootGame {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context) : ProbComp Bool := do
  let (context, _) ← sample
  let root ← $ᵗ RootOutput
  observer context root

/-- A primitive Extract experiment exposes the whole PRK, a stronger observation than the final root. -/
def extractRealGame {Context : Type} (hmac : HmacSha512)
    (sample : SecretInputSampler Context) (test : Context → HmacBlock → ProbComp Bool) : ProbComp Bool := do
  let (context, input) ← sample
  test context (extract hmac input)

noncomputable def extractUniformGame {Context : Type}
    (sample : SecretInputSampler Context) (test : Context → HmacBlock → ProbComp Bool) : ProbComp Bool := do
  let (context, _) ← sample
  let prk ← $ᵗ HmacBlock
  test context prk

/-- The concrete Extract reduction evaluates only the first HMAC-Expand block before running the observer. -/
def extractReduction {Context : Type} (hmac : HmacSha512)
    (observer : RootObserver Context) : Context → HmacBlock → ProbComp Bool :=
  fun context prk => observer context (expandRoot hmac prk)

/-- One standard secret-key HMAC challenge query; all other observer computations stay local. -/
def expandReduction {Context : Type} (sample : SecretInputSampler Context)
    (observer : RootObserver Context) : OracleComp HmacAdversarySpec Bool := do
  let (context, _) ← liftM (m := ProbComp) sample
  let block ← liftM (HmacAdversarySpec.query (.inr rootExpandInput))
  liftM (observer context (first32 block))

/-- Ordinary PRF real handler: adversary coins and HMAC under one hidden uniform key. -/
def hmacRealImpl (hmac : HmacSha512) (key : HmacBlock) :
    QueryImpl HmacAdversarySpec ProbComp :=
  let primitive : QueryImpl HmacOracle ProbComp := fun input => pure (hmac.eval key input)
  QueryImpl.ofLift unifSpec ProbComp + primitive

/-- Ordinary PRF ideal handler, consistent on repeated public-message queries. -/
noncomputable def hmacRandomImpl :
    QueryImpl HmacAdversarySpec (StateT HmacOracle.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT HmacOracle.QueryCache ProbComp) +
    HmacOracle.randomOracle

noncomputable def hmacPrfRealGame (hmac : HmacSha512)
    (adversary : OracleComp HmacAdversarySpec Bool) : ProbComp Bool := do
  let key ← $ᵗ HmacBlock
  simulateQ (hmacRealImpl hmac key) adversary

noncomputable def hmacPrfRandomGame
    (adversary : OracleComp HmacAdversarySpec Bool) : ProbComp Bool :=
  (simulateQ hmacRandomImpl adversary).run' ∅

/-- The functional source law also fixes the complete typed root. -/
theorem sourceRootOutput_eq (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceRootCorrect source hmac) (input : Pqxdh.Bytes) :
    (⟨Pqxdh.rootSecret source.crypto input, Pqxdh.rootSecret_length source.crypto input⟩ : RootOutput) =
      expandRoot hmac (extract hmac input) := by
  exact List.Vector.toList_injective (correct input)

/-- The source relation connects the actual wrapper to Extract followed by Expand. -/
theorem sourceRootGame_eq_extract {Context : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (sample : SecretInputSampler Context)
    (observer : RootObserver Context) :
    sourceRootGame source sample observer =
      extractRealGame hmac sample (extractReduction hmac observer) := by
  simp only [sourceRootGame, extractRealGame, extractReduction, sourceRootOutput_eq source hmac correct]

/-- The real PRF reduction performs the same local sampler and observer around one Expand call. -/
theorem expandReduction_real {Context : Type} (hmac : HmacSha512)
    (key : HmacBlock) (sample : SecretInputSampler Context) (observer : RootObserver Context) :
    simulateQ (hmacRealImpl hmac key) (expandReduction sample observer) =
      (do let (context, _) ← sample
          observer context (expandRoot hmac key)) := by
  simp [expandReduction, hmacRealImpl, QueryImpl.simulateQ_add_liftM_left,
    expandRoot]

/-- The independent PRF key and public sampler may be reordered in distribution. -/
theorem evalDist_sample_comm {A B C : Type} (left : ProbComp A) (right : ProbComp B)
    (next : A → B → ProbComp C) :
    𝒟[left >>= fun a => right >>= next a] =
      𝒟[right >>= fun b => left >>= fun a => next a b] := by
  apply evalDist_ext
  intro output
  simp_rw [probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  simp only [mul_left_comm]

/-- Uniform Extract output is exactly the ordinary secret-key HMAC real world. -/
theorem extractUniform_eq_hmacReal {Context : Type} (hmac : HmacSha512)
    (sample : SecretInputSampler Context) (observer : RootObserver Context) :
    𝒟[extractUniformGame sample (extractReduction hmac observer)] =
      𝒟[hmacPrfRealGame hmac (expandReduction sample observer)] := by
  simpa [hmacPrfRealGame, expandReduction_real, extractUniformGame, extractReduction] using
    evalDist_sample_comm (sample : ProbComp (Context × Pqxdh.Bytes)) ($ᵗ HmacBlock)
      (fun pair key => observer pair.1 (expandRoot hmac key))

/-- The ideal HMAC reduction receives one fresh block, while local computations leave the table alone. -/
theorem expandReduction_random {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context) :
    hmacPrfRandomGame (expandReduction sample observer) =
      (do let (context, _) ← sample
          let block ← $ᵗ HmacBlock
          observer context (first32 block)) := by
  simp [hmacPrfRandomGame, expandReduction, hmacRandomImpl,
    QueryImpl.simulateQ_add_liftM_left, OracleSpec.randomOracle,
    uniformSampleImpl, StateT.run'_eq]

/-- Splitting a SHA-512 block preserves every byte and is bijective. -/
def blockSplitEquiv : HmacBlock ≃ (RootOutput × RootOutput) where
  toFun block := (List.Vector.take 32 block, List.Vector.drop 32 block)
  invFun parts := parts.1 ++ parts.2
  left_inv block := List.Vector.toList_injective (List.take_append_drop 32 block.toList)
  right_inv parts := Prod.ext
    (List.Vector.toList_injective (show
      List.take 32 (parts.1.toList ++ parts.2.toList) = parts.1.toList from by
        simp))
    (List.Vector.toList_injective (show
      List.drop 32 (parts.1.toList ++ parts.2.toList) = parts.2.toList from by
        simp))

/-- The ideal first-block projection is exactly a uniform 32-byte root. -/
theorem first32_uniform :
    𝒟[first32 <$> ($ᵗ HmacBlock)] = 𝒟[$ᵗ RootOutput] := by
  have split : 𝒟[blockSplitEquiv <$> ($ᵗ HmacBlock)] =
      𝒟[$ᵗ (RootOutput × RootOutput)] :=
    evalDist_map_bijective_uniform_cross HmacBlock blockSplitEquiv blockSplitEquiv.bijective
  calc
    _ = 𝒟[Prod.fst <$> (blockSplitEquiv <$> ($ᵗ HmacBlock))] := by
      simp only [Functor.map_map]
      rfl
    _ = 𝒟[Prod.fst <$> ($ᵗ (RootOutput × RootOutput))] := by
      rw [evalDist_map, split, ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- The HMAC random world replaces exactly the honest root and preserves the observer's local public evaluations. -/
theorem hmacRandom_eq_independentRoot {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context) :
    𝒟[hmacPrfRandomGame (expandReduction sample observer)] =
      𝒟[independentRootGame sample observer] := by
  rw [expandReduction_random]
  refine evalDist_bind_congr' (m := ProbComp) (sample : ProbComp (Context × Pqxdh.Bytes)) fun pair => ?_
  change 𝒟[($ᵗ HmacBlock) >>= fun block => observer pair.1 (first32 block)] =
    𝒟[($ᵗ RootOutput) >>= observer pair.1]
  rw [← bind_map_left, evalDist_bind, first32_uniform, ← evalDist_bind]

/-- A loss-one root reduction to fixed-salt Extract pseudorandomness and ordinary secret-key HMAC PRF advantage.

The Extract term depends on the full joint input/side-information sampler. Its smallness is an additional primitive/distribution obligation, not a theorem of HMAC PRF security. This bound has no public-HKDF-versus-random-table term and makes no multi-session or compromise claim.
-/
theorem sourceRootAdvantage_le_extract_add_hmac {Context : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (sample : SecretInputSampler Context)
    (observer : RootObserver Context) :
    (sourceRootGame source sample observer).boolDistAdvantage
        (independentRootGame sample observer) ≤
      (extractRealGame hmac sample (extractReduction hmac observer)).boolDistAdvantage
        (extractUniformGame sample (extractReduction hmac observer)) +
      (hmacPrfRealGame hmac (expandReduction sample observer)).boolDistAdvantage
        (hmacPrfRandomGame (expandReduction sample observer)) := by
  have real := OracleComp.probOutput_congr (x := true) rfl
    (extractUniform_eq_hmacReal hmac sample observer)
  have random := OracleComp.probOutput_congr (x := true) rfl
    (hmacRandom_eq_independentRoot sample observer)
  simpa only [sourceRootGame_eq_extract source hmac correct, ProbComp.boolDistAdvantage,
    real, random] using
    ProbComp.boolDistAdvantage_triangle (sourceRootGame source sample observer)
      (extractUniformGame sample (extractReduction hmac observer))
      (independentRootGame sample observer)

/-- Charge only secret-key HMAC queries; public local evaluation is not such a query. -/
def IsHmacChallengeQuery : HmacAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsHmacChallengeQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

/-- The sampler and observer can do arbitrary local probabilistic computation without secret-key oracle access. -/
theorem local_no_hmac_query {A : Type} (computation : ProbComp A) :
    (OracleComp.liftComp computation HmacAdversarySpec).IsQueryBoundP
      IsHmacChallengeQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := HmacAdversarySpec)
    (p := fun _ => False) (q := IsHmacChallengeQuery)
    (hpq := fun query => by simp [IsHmacChallengeQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false computation 0)

/-- The root reduction costs at most one ordinary secret-key HMAC query. -/
theorem expandReduction_hmac_query_bound {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context) :
    (expandReduction sample observer).IsQueryBoundP IsHmacChallengeQuery 1 := by
  unfold expandReduction
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 1) (local_no_hmac_query sample) ?_
  rintro ⟨context, input⟩ _
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr (by decide), fun block => local_no_hmac_query (observer context (first32 block))⟩

/-- A countermodel transformer: sabotage only the public Extract key, leaving all other keyed evaluations unchanged. -/
def zeroSaltPatched (hmac : HmacSha512) : HmacSha512 where
  eval key input := if key = zeroSalt then zeroSalt else hmac.eval key input

/-- Entropy of the input cannot rescue Extract for this exceptional-key countermodel. -/
theorem extract_zeroSaltPatched (hmac : HmacSha512) (input : Pqxdh.Bytes) :
    extract (zeroSaltPatched hmac) input = zeroSalt := by
  simp [extract, zeroSaltPatched]

/-- Every complete keyed-oracle execution away from the exceptional key is unchanged. -/
theorem hmacRealImpl_zeroSaltPatched (hmac : HmacSha512) (key : HmacBlock)
    (notZero : key ≠ zeroSalt) :
    hmacRealImpl (zeroSaltPatched hmac) key = hmacRealImpl hmac key := by
  simp [hmacRealImpl, zeroSaltPatched, notZero]

/-- A uniform-key PRF game encounters that exceptional key with probability only `2^-512`.

Together with the preceding handler equality this identifies the rare-key event a PRF hybrid must charge. It is not an implementation of SHA-512 and asserts no concrete HMAC attack.
-/
theorem zeroSalt_key_probability :
    Pr[fun key : HmacBlock => key = zeroSalt | $ᵗ HmacBlock] =
      (Fintype.card HmacBlock : ℝ≥0∞)⁻¹ := by
  simp [probOutput_uniformSample]

end BeaconcryptCore.Computational.PqxdhSecretInputKdf

/--
info: 'BeaconcryptCore.Computational.PqxdhSecretInputKdf.sourceRootAdvantage_le_extract_add_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSecretInputKdf.sourceRootAdvantage_le_extract_add_hmac
