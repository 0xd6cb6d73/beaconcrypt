import BeaconcryptCore.Computational.PqxdhFullSecretInputKdf
import BeaconcryptCore.Computational.RawCtxSelectedInitialSecond

/-!
# Generic key-schedule bound for Server authentication

This module is stage B8a of the Milestone B (Server authentication) design. It concerns only the key schedule that turns one 64-byte PRK into the 108 bytes the protocol later uses, and it contains no protocol code.

The key schedule is the one the Server and the Beacon run after the root derivation: the real HMAC-SHA-512 Expand gives the 32-byte root from the PRK, the production 64-byte ratchet HKDF of the root gives the initializer, the production 76-byte ratchet HKDF of the initializer's first half gives the first record's key, nonce and next chain, and the initializer's second half is kept. The output is the pair of that 76-byte step and the 32-byte second half.

Under route R1 the zero-salt 192-byte Extract is a random oracle, so the PRK of the table entry is a uniform 64-byte block. The real game therefore samples the PRK uniformly. Every other HMAC use stays real: the root Expand, the two 32-byte Extract calls and the two ratchet Expand calls are covered by the existing HMAC PRF game and the existing Extract game on a uniform 32-byte input.

The main theorem `keySchedule_bound` says that, for any distinguisher of the 108-byte output, the advantage between the real key schedule and 108 uniform bytes is at most the sum of five advantages. Each advantage belongs to a reduction built here from the distinguisher, and every secret is sampled inside the games. There is no premise quantified over all adversaries.

The five hops are: the root Expand (HMAC PRF, one query); the Extract of the uniform root (Extract game on a uniform 32-byte input); the first ratchet Expand block (HMAC PRF, one query); the Extract of the first initializer half (Extract game on a uniform 32-byte input); and the two-block 76-byte ratchet Expand (HMAC PRF, two queries). Between the third and fourth hops, `RawCtxSelectedInitialSecond.second_observed` splits the uniform 64-byte initializer into two independent uniform halves at no cost.

Each Extract and Expand pair has the shape of `PqxdhSecretInputKdf.sourceRootAdvantage_le_extract_add_hmac`: the functional contract `SourceFullCorrect` rewrites the production HKDF as Extract followed by Expand, the uniform Extract world is the real HMAC PRF world once the unused hidden input is dropped, and the random HMAC world is exactly the next uniform hybrid. The root hop has only the Expand half, because under R1 the PRK is already uniform. `SourceFullCorrect` is used for both the 64-byte and the 76-byte production HKDF; the 64-byte call is related to the 76-byte stream by the source's prefix contract.

The Extract games use the design's sampler `uniform32` (a uniform 32-byte input and no side information), so the two step-hop reductions draw the independent second half of the initializer themselves. Reductions 1, 4 and 5 are the existing `expandReduction`, `fullExtractReduction` and `fullExpandReduction`; the Expand reductions receive the trivial sampler `unitSample`, whose input they ignore.

The hybrid steps are equalities of output distributions, so each hop's advantage is exactly the advantage of its reduction. The only inequalities are triangle inequalities.

Two fidelity lemmas tie the output to the model: `fromRoot_model` shows that the 108 bytes are `Pqxdh.ratchetOut` on the left initial chain of `Pqxdh.rootChains`, followed by the right chain, and `keySchedule_extract` shows that with the real Extract in place of the random table the key schedule starts from the model's root `Pqxdh.rootSecret`. `keySchedule_bound_context` restates the bound when side information is sampled before the PRK, and the three HMAC PRF reductions make at most one, one and two secret-key HMAC queries.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule

open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- The 108-byte key-schedule output: the 76-byte ratchet step on the initializer's first half, then the initializer's 32-byte second half. -/
abbrev Output := FullOutput × RootOutput

/-- A distinguisher receives the whole 108-byte output and may run any local probabilistic computation, including public HMAC and HKDF evaluations. -/
abbrev Distinguisher := Output → ProbComp Bool

/-- The production 64-byte initial ratchet HKDF of a 32-byte root, `HKDF(root, INFO_R, 64)`. -/
def initializer (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) : HmacBlock :=
  ⟨source.crypto.hkdf root.toList Pqxdh.INFO_R 64, source.crypto.hkdf_length _ _ _⟩

/-- The production 76-byte ratchet step of a 32-byte chain, `HKDF(chain, INFO_R, 76)`. -/
def step (source : FixedHkdfSha512NoSaltSource) (chain : RootOutput) : FullOutput :=
  PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address chain.toList)

/-- Split a 64-byte initializer: step its first half (the first chain) and keep its second half. -/
def fromInitializer (source : FixedHkdfSha512NoSaltSource) (init : HmacBlock) : Output :=
  (step source (PqxdhSecretInputKdf.first32 init), RawCtxSelectedInitialSecond.secondChain init)

/-- The key schedule from the 32-byte root onwards. -/
def fromRoot (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) : Output :=
  fromInitializer source (initializer source root)

/-- The complete key schedule `f PRK`: the real root Expand, then the production initial and step HKDF. -/
def keySchedule (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (prk : HmacBlock) :
    Output :=
  fromRoot source (expandRoot hmac prk)

/-- The real game: a uniform 64-byte PRK (the table entry under route R1) and the real key schedule. -/
noncomputable def realGame (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) : ProbComp Bool := do
  let prk ← $ᵗ HmacBlock
  distinguisher (keySchedule source hmac prk)

/-- The ideal game: 108 uniform bytes. -/
noncomputable def uniformGame (distinguisher : Distinguisher) : ProbComp Bool := do
  let output ← $ᵗ Output
  distinguisher output

/-- The Extract sampler: an independent uniform 32-byte hidden input and no side information. -/
noncomputable def uniform32 : SecretInputSampler Unit :=
  (do let input ← $ᵗ RootOutput
      pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes))

/-- A sampler with no side information and no input, used where an existing Expand reduction is reused; those reductions ignore the input. -/
def unitSample : SecretInputSampler Unit :=
  (pure ((), []) : ProbComp (Unit × Pqxdh.Bytes))

/-! ### The five reductions -/

/-- The continuation of the root hop: finish the key schedule on the received root. -/
def rootObserver (source : FixedHkdfSha512NoSaltSource) (distinguisher : Distinguisher) :
    RootObserver Unit :=
  fun _ root => distinguisher (fromRoot source root)

/-- Reduction 1 (HMAC PRF): the existing root Expand reduction, one challenge query at `rootExpandInput`. -/
def rootExpandReduction (source : FixedHkdfSha512NoSaltSource) (distinguisher : Distinguisher) :
    OracleComp HmacAdversarySpec Bool :=
  expandReduction unitSample (rootObserver source distinguisher)

/-- Reduction 2 (Extract of the root): given the PRK of the root, compute the first ratchet Expand block locally and finish. -/
def initExtractReduction (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) : Unit → HmacBlock → ProbComp Bool :=
  fun _ prk => distinguisher (fromInitializer source (hmac.eval prk (firstExpandInput .ratchet)))

/-- Reduction 3 (HMAC PRF): one challenge query at the first ratchet Expand message gives the 64-byte initializer. -/
def initExpandReduction (source : FixedHkdfSha512NoSaltSource) (distinguisher : Distinguisher) :
    OracleComp HmacAdversarySpec Bool := do
  let init ← liftM (HmacAdversarySpec.query (.inr (firstExpandInput .ratchet)))
  liftM (distinguisher (fromInitializer source init))

/-- The continuation of the step hops: it draws the independent second half itself and passes both parts on. -/
noncomputable def stepObserver (distinguisher : Distinguisher) : FullObserver Unit :=
  fun _ output => do
    let other ← $ᵗ RootOutput
    distinguisher (output, other)

/-- Reduction 4 (Extract of the first chain): the existing full-expansion Extract reduction at the ratchet label. -/
noncomputable def stepExtractReduction (hmac : HmacSha512) (distinguisher : Distinguisher) :
    Unit → HmacBlock → ProbComp Bool :=
  fullExtractReduction hmac .ratchet (stepObserver distinguisher)

/-- Reduction 5 (HMAC PRF): the existing two-query full-expansion reduction at the ratchet label. -/
noncomputable def stepExpandReduction (distinguisher : Distinguisher) :
    OracleComp HmacAdversarySpec Bool :=
  fullExpandReduction .ratchet unitSample (stepObserver distinguisher)

/-! ### Hybrids -/

/-- Hybrid 1: a uniform root. -/
noncomputable def rootHybrid (source : FixedHkdfSha512NoSaltSource)
    (distinguisher : Distinguisher) : ProbComp Bool := do
  let root ← $ᵗ RootOutput
  distinguisher (fromRoot source root)

/-- Hybrid 2: a uniform PRK for the initializer Expand. -/
noncomputable def initKeyHybrid (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) : ProbComp Bool := do
  let prk ← $ᵗ HmacBlock
  distinguisher (fromInitializer source (hmac.eval prk (firstExpandInput .ratchet)))

/-- Hybrid 3: a uniform 64-byte initializer. -/
noncomputable def initHybrid (source : FixedHkdfSha512NoSaltSource)
    (distinguisher : Distinguisher) : ProbComp Bool := do
  let init ← $ᵗ HmacBlock
  distinguisher (fromInitializer source init)

/-- Hybrid 4: two independent uniform halves; the first is stepped by the production HKDF. -/
noncomputable def splitHybrid (source : FixedHkdfSha512NoSaltSource)
    (distinguisher : Distinguisher) : ProbComp Bool := do
  let chain ← $ᵗ RootOutput
  let other ← $ᵗ RootOutput
  distinguisher (step source chain, other)

/-- Hybrid 5: a uniform PRK for the two-block ratchet Expand. -/
noncomputable def stepKeyHybrid (hmac : HmacSha512) (distinguisher : Distinguisher) :
    ProbComp Bool := do
  let prk ← $ᵗ HmacBlock
  let other ← $ᵗ RootOutput
  distinguisher (expandFull hmac .ratchet prk, other)

/-! ### Functional equations -/

/-- The production 64-byte initializer is the first ratchet Expand block under the Extract of the root. -/
theorem initializer_eq {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (root : RootOutput) :
    initializer source root = hmac.eval (extract hmac root.toList) (firstExpandInput .ratchet) := by
  apply List.Vector.toList_injective
  have prefixEq := source.prefixConsistent.ratchetPrefix root.toList
  have stream := congrArg (fun output : FullOutput => (initialPrefix output).toList)
    (correct .ratchet root.toList)
  simp only [initialPrefix_expandFull] at stream
  rw [← stream]
  change source.crypto.hkdf root.toList Pqxdh.INFO_R 64 = _
  rw [prefixEq]
  rfl

/-- The production 76-byte step is the full ratchet Expand under the Extract of the chain. -/
theorem step_eq {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (chain : RootOutput) :
    step source chain = expandFull hmac .ratchet (extract hmac chain.toList) :=
  correct .ratchet chain.toList

/-- The key schedule written with HMAC only: root Expand, Extract, one Expand block, split, Extract and the two-block Expand. -/
theorem keySchedule_hmac {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (prk : HmacBlock) :
    keySchedule source hmac prk =
      (expandFull hmac .ratchet (extract hmac (PqxdhSecretInputKdf.first32
          (hmac.eval (extract hmac (expandRoot hmac prk).toList) (firstExpandInput .ratchet))).toList),
        RawCtxSelectedInitialSecond.secondChain
          (hmac.eval (extract hmac (expandRoot hmac prk).toList) (firstExpandInput .ratchet))) := by
  simp only [keySchedule, fromRoot, fromInitializer, initializer_eq correct, step_eq correct]

/-- The 108 bytes from a root are the model's record expansion `Pqxdh.ratchetOut` on the initial left chain, then the initial right chain, both from `Pqxdh.rootChains`. -/
theorem fromRoot_model (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    ((fromRoot source root).1.toList, (fromRoot source root).2.toList) =
      (Pqxdh.ratchetOut source.crypto (Pqxdh.rootChains source.crypto root.toList).1,
        (Pqxdh.rootChains source.crypto root.toList).2) :=
  rfl

/-- With the real Extract in place of the random table, the key schedule is the one of the model's PQXDH root `Pqxdh.rootSecret`. -/
theorem keySchedule_extract {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (input : Pqxdh.Bytes) :
    keySchedule source hmac (extract hmac input) =
      fromRoot source ⟨Pqxdh.rootSecret source.crypto input,
        Pqxdh.rootSecret_length source.crypto input⟩ := by
  rw [keySchedule, sourceRootOutput_eq source hmac correct.root input]

/-! ### Hop equalities -/

/-- Equal output distributions give equal distinguishing advantages. -/
theorem advantage_congr {p p' q q' : ProbComp Bool} (hp : 𝒟[p] = 𝒟[p']) (hq : 𝒟[q] = 𝒟[q']) :
    p.boolDistAdvantage q = p'.boolDistAdvantage q' := by
  simp only [ProbComp.boolDistAdvantage, hp, hq]

/-- The real PRF world of reduction 1 is the real game. -/
theorem rootExpand_real (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) :
    hmacPrfRealGame hmac (rootExpandReduction source distinguisher) =
      realGame source hmac distinguisher := by
  simp [hmacPrfRealGame, rootExpandReduction, expandReduction_real, unitSample, rootObserver,
    realGame, keySchedule]

/-- The random PRF world of reduction 1 has the output distribution of hybrid 1. -/
theorem rootExpand_random (source : FixedHkdfSha512NoSaltSource) (distinguisher : Distinguisher) :
    𝒟[hmacPrfRandomGame (rootExpandReduction source distinguisher)] =
      𝒟[rootHybrid source distinguisher] := by
  apply evalDist_eq_of_evalSPMF_eq
  rw [rootExpandReduction, hmacRandom_eq_independentRoot_vcvioLegacy]
  simp [independentRootGame, unitSample, rootObserver, rootHybrid]

/-- The real Extract world of reduction 2 is hybrid 1, by `SourceFullCorrect` for the 64-byte HKDF. -/
theorem initExtract_real {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher) =
      rootHybrid source distinguisher := by
  simp [extractRealGame, uniform32, initExtractReduction, rootHybrid, fromRoot,
    initializer_eq correct]

/-- The uniform Extract world of reduction 2 has the output distribution of hybrid 2: the unused hidden input is dropped. -/
theorem initExtract_uniform (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) :
    𝒟[extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)] =
      𝒟[initKeyHybrid source hmac distinguisher] := by
  apply evalDist_eq_of_evalSPMF_eq
  simp only [extractUniformGame, uniform32, bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ RootOutput) (by simp) _

/-- The real PRF world of reduction 3 is hybrid 2. -/
theorem initExpand_real (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) :
    hmacPrfRealGame hmac (initExpandReduction source distinguisher) =
      initKeyHybrid source hmac distinguisher := by
  simp [hmacPrfRealGame, initExpandReduction, hmacRealImpl, QueryImpl.simulateQ_add_liftM_left,
    initKeyHybrid]

/-- The random PRF world of reduction 3 is hybrid 3: its single query is fresh. -/
theorem initExpand_random (source : FixedHkdfSha512NoSaltSource) (distinguisher : Distinguisher) :
    hmacPrfRandomGame (initExpandReduction source distinguisher) =
      initHybrid source distinguisher := by
  simp [hmacPrfRandomGame, initExpandReduction, hmacRandomImpl,
    QueryImpl.simulateQ_add_liftM_left, OracleSpec.randomOracle, uniformSampleImpl,
    StateT.run'_eq, initHybrid]

/-- Hybrids 3 and 4 have the same output distribution: a uniform initializer is two independent uniform halves (`second_observed`). -/
theorem init_split (source : FixedHkdfSha512NoSaltSource) (distinguisher : Distinguisher) :
    𝒟[initHybrid source distinguisher] = 𝒟[splitHybrid source distinguisher] :=
  evalDist_eq_of_evalSPMF_eq _ _ (RawCtxSelectedInitialSecond.second_observed_vcvioLegacy
    (fun chain other => distinguisher (step source chain, other)))

/-- The real Extract world of reduction 4 is hybrid 4, by `SourceFullCorrect` for the 76-byte HKDF. -/
theorem stepExtract_real {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher) =
      splitHybrid source distinguisher := by
  simp [extractRealGame, uniform32, stepExtractReduction, fullExtractReduction, stepObserver,
    splitHybrid, step_eq correct]

/-- The uniform Extract world of reduction 4 has the output distribution of hybrid 5: the unused hidden input is dropped. -/
theorem stepExtract_uniform (hmac : HmacSha512) (distinguisher : Distinguisher) :
    𝒟[extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)] =
      𝒟[stepKeyHybrid hmac distinguisher] := by
  apply evalDist_eq_of_evalSPMF_eq
  simp only [extractUniformGame, uniform32, bind_assoc, pure_bind]
  exact OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ RootOutput) (by simp) _

/-- The real PRF world of reduction 5 is hybrid 5. -/
theorem stepExpand_real (hmac : HmacSha512) (distinguisher : Distinguisher) :
    hmacPrfRealGame hmac (stepExpandReduction distinguisher) = stepKeyHybrid hmac distinguisher := by
  simp [hmacPrfRealGame, stepExpandReduction, fullExpandReduction_real, unitSample, stepObserver,
    stepKeyHybrid]

/-- The random PRF world of reduction 5 has the output distribution of the ideal game: the two fresh blocks give a uniform 76-byte output. -/
theorem stepExpand_random (distinguisher : Distinguisher) :
    𝒟[hmacPrfRandomGame (stepExpandReduction distinguisher)] = 𝒟[uniformGame distinguisher] := by
  apply evalDist_eq_of_evalSPMF_eq
  rw [stepExpandReduction, fullHmacRandom_eq_independent_vcvioLegacy]
  have joint : (do
      let output ← $ᵗ FullOutput
      let other ← $ᵗ RootOutput
      distinguisher (output, other)) =
      (do let pair ← (do let output ← $ᵗ FullOutput
                          let other ← $ᵗ RootOutput
                          pure (output, other))
          distinguisher pair) := by
    simp
  simp only [independentFullGame, unitSample, stepObserver, pure_bind, uniformGame, joint,
    pairSample]

/-! ### The five hops and the bound -/

/-- Hop 1 (root Expand): the real game against hybrid 1 is exactly the HMAC PRF advantage of reduction 1. -/
theorem rootExpand_hop (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) :
    (realGame source hmac distinguisher).boolDistAdvantage (rootHybrid source distinguisher) =
      (hmacPrfRealGame hmac (rootExpandReduction source distinguisher)).boolDistAdvantage
        (hmacPrfRandomGame (rootExpandReduction source distinguisher)) :=
  advantage_congr (by rw [rootExpand_real]) (rootExpand_random source distinguisher).symm

/-- Hop 2 (Extract of the root): hybrid 1 against hybrid 2 is exactly the Extract advantage of reduction 2. -/
theorem initExtract_hop {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    (rootHybrid source distinguisher).boolDistAdvantage (initKeyHybrid source hmac distinguisher) =
      (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistAdvantage
        (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) :=
  advantage_congr (by rw [initExtract_real correct])
    (initExtract_uniform source hmac distinguisher).symm

/-- Hop 3 (initializer Expand): hybrid 2 against hybrid 3 is exactly the HMAC PRF advantage of reduction 3. -/
theorem initExpand_hop (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (distinguisher : Distinguisher) :
    (initKeyHybrid source hmac distinguisher).boolDistAdvantage (initHybrid source distinguisher) =
      (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistAdvantage
        (hmacPrfRandomGame (initExpandReduction source distinguisher)) :=
  advantage_congr (by rw [initExpand_real]) (by rw [initExpand_random])

/-- Hop 4 (Extract of the first chain): hybrid 4 against hybrid 5 is exactly the Extract advantage of reduction 4. -/
theorem stepExtract_hop {source : FixedHkdfSha512NoSaltSource} {hmac : HmacSha512}
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    (splitHybrid source distinguisher).boolDistAdvantage (stepKeyHybrid hmac distinguisher) =
      (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistAdvantage
        (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) :=
  advantage_congr (by rw [stepExtract_real correct]) (stepExtract_uniform hmac distinguisher).symm

/-- Hop 5 (step Expand): hybrid 5 against the ideal game is exactly the HMAC PRF advantage of reduction 5. -/
theorem stepExpand_hop (hmac : HmacSha512) (distinguisher : Distinguisher) :
    (stepKeyHybrid hmac distinguisher).boolDistAdvantage (uniformGame distinguisher) =
      (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistAdvantage
        (hmacPrfRandomGame (stepExpandReduction distinguisher)) :=
  advantage_congr (by rw [stepExpand_real]) (stepExpand_random distinguisher).symm

/-- The key-schedule bound: for any distinguisher of the 108-byte output, the real-versus-uniform advantage is at most the sum of the five advantages of the reductions built from it (root Expand PRF, root Extract, initializer Expand PRF, first-chain Extract, step Expand PRF)., under the functional contract `SourceFullCorrect`. -/
theorem keySchedule_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (distinguisher : Distinguisher) :
    (realGame source hmac distinguisher).boolDistAdvantage (uniformGame distinguisher) ≤
      (hmacPrfRealGame hmac (rootExpandReduction source distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (rootExpandReduction source distinguisher)) +
        (extractRealGame hmac uniform32 (initExtractReduction source hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (initExtractReduction source hmac distinguisher)) +
        (hmacPrfRealGame hmac (initExpandReduction source distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction source distinguisher)) +
        (extractRealGame hmac uniform32 (stepExtractReduction hmac distinguisher)).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction hmac distinguisher)) +
        (hmacPrfRealGame hmac (stepExpandReduction distinguisher)).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction distinguisher)) := by
  rw [← rootExpand_hop, ← initExtract_hop correct, ← initExpand_hop, ← stepExtract_hop correct,
    ← stepExpand_hop]
  have split : (initHybrid source distinguisher).boolDistAdvantage (uniformGame distinguisher) =
      (splitHybrid source distinguisher).boolDistAdvantage (uniformGame distinguisher) :=
    advantage_congr (init_split source distinguisher) rfl
  have first := ProbComp.boolDistAdvantage_triangle (realGame source hmac distinguisher)
    (rootHybrid source distinguisher) (uniformGame distinguisher)
  have second := ProbComp.boolDistAdvantage_triangle (rootHybrid source distinguisher)
    (initKeyHybrid source hmac distinguisher) (uniformGame distinguisher)
  have third := ProbComp.boolDistAdvantage_triangle (initKeyHybrid source hmac distinguisher)
    (initHybrid source distinguisher) (uniformGame distinguisher)
  have fourth := ProbComp.boolDistAdvantage_triangle (splitHybrid source distinguisher)
    (stepKeyHybrid hmac distinguisher) (uniformGame distinguisher)
  linarith

/-- Fold side information sampled before the PRK into the distinguisher. -/
def withContext {Context : Type} (sample : ProbComp Context)
    (distinguisher : Context → Distinguisher) : Distinguisher :=
  fun output => do
    let context ← sample
    distinguisher context output

/-- The key-schedule bound when side information is sampled before the PRK: the five reductions are built from the folded distinguisher `withContext sample distinguisher`. -/
theorem keySchedule_bound_context {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (sample : ProbComp Context)
    (distinguisher : Context → Distinguisher) :
    (do let context ← sample
        let prk ← $ᵗ HmacBlock
        distinguisher context (keySchedule source hmac prk)).boolDistAdvantage
      (do let context ← sample
          let output ← $ᵗ Output
          distinguisher context output) ≤
      (hmacPrfRealGame hmac (rootExpandReduction source (withContext sample distinguisher))).boolDistAdvantage
          (hmacPrfRandomGame (rootExpandReduction source (withContext sample distinguisher))) +
        (extractRealGame hmac uniform32
            (initExtractReduction source hmac (withContext sample distinguisher))).boolDistAdvantage
          (extractUniformGame uniform32
            (initExtractReduction source hmac (withContext sample distinguisher))) +
        (hmacPrfRealGame hmac (initExpandReduction source (withContext sample distinguisher))).boolDistAdvantage
          (hmacPrfRandomGame (initExpandReduction source (withContext sample distinguisher))) +
        (extractRealGame hmac uniform32
            (stepExtractReduction hmac (withContext sample distinguisher))).boolDistAdvantage
          (extractUniformGame uniform32 (stepExtractReduction hmac (withContext sample distinguisher))) +
        (hmacPrfRealGame hmac (stepExpandReduction (withContext sample distinguisher))).boolDistAdvantage
          (hmacPrfRandomGame (stepExpandReduction (withContext sample distinguisher))) := by
  have real := evalDist_eq_of_evalSPMF_eq _ _ (PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy sample
    ($ᵗ HmacBlock) (fun context prk => distinguisher context (keySchedule source hmac prk)))
  have ideal := evalDist_eq_of_evalSPMF_eq _ _ (PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy sample
    ($ᵗ Output) (fun context output => distinguisher context output))
  rw [advantage_congr real ideal]
  exact keySchedule_bound source hmac correct (withContext sample distinguisher)

/-! ### Challenge-query counts of the PRF reductions -/

/-- Reduction 1 makes at most one secret-key HMAC query. -/
theorem rootExpandReduction_query_bound (source : FixedHkdfSha512NoSaltSource)
    (distinguisher : Distinguisher) :
    (rootExpandReduction source distinguisher).IsQueryBoundP IsHmacChallengeQuery 1 :=
  expandReduction_hmac_query_bound unitSample (rootObserver source distinguisher)

/-- Reduction 3 makes at most one secret-key HMAC query. -/
theorem initExpandReduction_query_bound (source : FixedHkdfSha512NoSaltSource)
    (distinguisher : Distinguisher) :
    (initExpandReduction source distinguisher).IsQueryBoundP IsHmacChallengeQuery 1 := by
  unfold initExpandReduction
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr (by decide), fun init => local_no_hmac_query
    (distinguisher (fromInitializer source init))⟩

/-- Reduction 5 makes at most two secret-key HMAC queries. -/
theorem stepExpandReduction_query_bound (distinguisher : Distinguisher) :
    (stepExpandReduction distinguisher).IsQueryBoundP IsHmacChallengeQuery 2 :=
  fullExpandReduction_hmac_query_bound .ratchet unitSample (stepObserver distinguisher)

end BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initializer_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initializer_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.step_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.step_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.fromRoot_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.fromRoot_model

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_extract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_extract

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.advantage_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.advantage_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpand_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpand_real

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpand_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpand_random

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExtract_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExtract_real

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExtract_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExtract_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpand_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpand_real

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpand_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpand_random

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.init_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.init_split

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExtract_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExtract_real

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExtract_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExtract_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpand_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpand_real

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpand_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpand_random

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpand_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpand_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExtract_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExtract_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpand_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpand_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExtract_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExtract_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpand_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpand_hop

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_bound_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.keySchedule_bound_context

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpandReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.rootExpandReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpandReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.initExpandReduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpandReduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule.stepExpandReduction_query_bound
