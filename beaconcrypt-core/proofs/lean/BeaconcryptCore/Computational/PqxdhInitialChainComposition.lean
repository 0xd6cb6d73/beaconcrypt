import BeaconcryptCore.Computational.PqxdhOrderedChainHybrids

/-!
# Source initialization and both ordered finite chains

Starting from one independently uniform 32-byte root, the actual 64-byte source call feeds both complete directional histories. Its exact shared-prefix equality precedes one initialization hop and the checked ordered derivation hops. Complete sampler/observer and challenger query budgets include the unselected direction, unused root/chain samples and all random blocks. This is a finite-history component; authenticated-root integration, adaptive schedules/reveals, snapshots and global source composition remain separate.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhInitialChainComposition

open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

/-- Discard only the unused initial nonce slot, keeping the entire continuation on both chains. -/
theorem initial_chains_observed {A : Type} (continuation : RootOutput → RootOutput → ProbComp A) :
    EvalDistEq
      (do let output ← $ᵗ FullOutput
          continuation (JointKdfProjection.first32.project output)
            (JointKdfProjection.second32.project output))
      (do let left ← $ᵗ RootOutput
          let right ← $ᵗ RootOutput
          continuation left right) := by
  have full := fullOutput_observed (fun record chain => continuation record.1 chain)
  simp only [material, nextChain] at full
  refine full.trans ?_
  simp only [Material, ← pairSample, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right ($ᵗ RootOutput) (fun left => ?_)
  exact OracleComp.EvalDistEq.bind_const _ _

/-- Initial chain expansion observes one root input without exposing that root in its context. -/
noncomputable def rootSampler {Context : Type} (sample : ProbComp Context) :
    ProbComp (Context × Pqxdh.Bytes) := do
  let context ← sample
  let root ← $ᵗ RootOutput
  pure (context, root.toList)

/-- Both directions and all later source derivations are created from this same initial output. -/
def initialObserver {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (observer : BidirectionalObserver Context) (leftRounds rightRounds : Nat) :
    FullObserver Context := fun context output =>
  observer context
    (realEvolution source leftRounds (JointKdfProjection.first32.project output))
    (realEvolution source rightRounds (JointKdfProjection.second32.project output))

/-- The real initialization consumes the source's single shared-prefix expansion. -/
noncomputable def initializedGame {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) : ProbComp Bool :=
  sourceFullGame source .ratchet (rootSampler sample)
    (initialObserver source observer leftRounds rightRounds)

/-- The source's actual 64-byte initialization pair is the observed pair of this one expansion. -/
theorem initialized_pair_source (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    Pqxdh.rootChains source.crypto root.toList =
      PqxdhJointKdf.initialProjection (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address root.toList)) := by
  exact PqxdhJointKdf.rootChains_eq_initialProjection source.crypto source.prefixConsistent _

/-- Idealizing initialization produces exactly the existing two-direction experiment. -/
theorem independent_initial_eq_bidirectional {Context : Type}
    (source : FixedHkdfSha512NoSaltSource) (sample : ProbComp Context)
    (observer : BidirectionalObserver Context) (leftRounds rightRounds : Nat) :
    EvalDistEq (independentFullGame (rootSampler sample)
      (initialObserver source observer leftRounds rightRounds))
      (bidirectionalGame source sample observer leftRounds rightRounds 0 0) := by
  simp only [independentFullGame, rootSampler, initialObserver, bidirectionalGame,
    sampleEvolution, sampleMaterials, Nat.sub_zero, List.nil_append, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right sample (fun context => ?_)
  refine (OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) _).trans ?_
  exact initial_chains_observed (fun left right =>
    observer context (realEvolution source leftRounds left) (realEvolution source rightRounds right))

/-- Explicit initialization reductions see the exact root sampler and both complete source tails. -/
noncomputable def initialLoss {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) : ℝ :=
  let joint := rootSampler sample
  let observe := initialObserver source observer leftRounds rightRounds
  (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).boolDistance
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)) +
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).boolDistance
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe))

/-- The first hop replaces the shared initialization prefix, before any directional hop. -/
theorem initialized_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) :
    (initializedGame source sample observer leftRounds rightRounds).boolDistance
      (bidirectionalGame source sample observer leftRounds rightRounds 0 0) ≤
      initialLoss source hmac sample observer leftRounds rightRounds := by
  have random := (independent_initial_eq_bidirectional source sample observer leftRounds rightRounds).evalDist_eq
  simpa only [initializedGame, initialLoss, ProbComp.boolDistance, random] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet
      (rootSampler sample) (initialObserver source observer leftRounds rightRounds)

/-- The actual initialization and both complete directional derivations compose in order. -/
theorem initialized_evolving_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) :
    (initializedGame source sample observer leftRounds rightRounds).boolDistance
      (bidirectionalGame source sample observer leftRounds rightRounds leftRounds rightRounds) ≤
      initialLoss source hmac sample observer leftRounds rightRounds +
      ((∑ cut ∈ Finset.range leftRounds,
        hopLoss source hmac sample (leftObserver source observer rightRounds 0)
          cut (leftRounds - cut - 1)) +
      (∑ cut ∈ Finset.range rightRounds,
        hopLoss source hmac (rightContextSampler source sample leftRounds leftRounds)
          (rightObserver observer) cut (rightRounds - cut - 1))) := by
  exact (ProbComp.boolDistance_triangle _ _ _).trans
    (add_le_add (initialized_bound source hmac correct sample observer leftRounds rightRounds)
      (bidirectional_bound source hmac correct sample observer leftRounds rightRounds))

/-- Execute the actual 64-byte source call once, then split its two halves. -/
def sourceInitialChains (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    RootOutput × RootOutput :=
  let bytes := source.crypto.hkdf root.toList Pqxdh.INFO_R 64
  (⟨bytes.take 32, by simp [bytes, source.crypto.hkdf_length]⟩,
    ⟨bytes.drop 32, by simp [bytes, source.crypto.hkdf_length]⟩)

/-- Typed source output and the byte model have the same two initial chains. -/
theorem sourceInitialChains_bytes (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    ((sourceInitialChains source root).1.toList, (sourceInitialChains source root).2.toList) =
      Pqxdh.rootChains source.crypto root.toList := by rfl

/-- The source 64-byte call and the shared 76-byte projection feed identical typed continuations. -/
theorem sourceInitialChains_eq (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    sourceInitialChains source root =
      let output := PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address root.toList)
      (JointKdfProjection.first32.project output, JointKdfProjection.second32.project output) := by
  have bytes := (sourceInitialChains_bytes source root).trans (initialized_pair_source source root)
  apply Prod.ext
  · apply List.Vector.toList_injective
    exact congrArg Prod.fst bytes
  · apply List.Vector.toList_injective
    exact congrArg Prod.snd bytes

/-- Execute the actual 64-byte initialization exactly once, then derive both complete source histories from its two retained halves. -/
noncomputable def actualInitializedGame {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) : ProbComp Bool := do
  let context ← sample
  let root ← $ᵗ RootOutput
  let chains := sourceInitialChains source root
  observer context (realEvolution source leftRounds chains.1) (realEvolution source rightRounds chains.2)

/-- The source's actual 64-byte call and the proof's shared 76-byte projection retain the same complete continuation, not merely equal marginal chain distributions. -/
theorem actualInitializedGame_eq {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) :
    actualInitializedGame source sample observer leftRounds rightRounds =
      initializedGame source sample observer leftRounds rightRounds := by
  simp only [actualInitializedGame, initializedGame, sourceFullGame, rootSampler,
    initialObserver, sourceInitialChains_eq, bind_assoc, pure_bind]

/-- The actual source initialization and both complete directional histories satisfy the ordered bound with one initial and one per-derivation pair of concrete reductions. -/
theorem actualInitializedGame_evolving_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) :
    (actualInitializedGame source sample observer leftRounds rightRounds).boolDistance
      (bidirectionalGame source sample observer leftRounds rightRounds leftRounds rightRounds) ≤
      initialLoss source hmac sample observer leftRounds rightRounds +
      ((∑ cut ∈ Finset.range leftRounds,
        hopLoss source hmac sample (leftObserver source observer rightRounds 0)
          cut (leftRounds - cut - 1)) +
      (∑ cut ∈ Finset.range rightRounds,
        hopLoss source hmac (rightContextSampler source sample leftRounds leftRounds)
          (rightObserver observer) cut (rightRounds - cut - 1))) := by
  rw [actualInitializedGame_eq]
  exact initialized_evolving_bound source hmac correct sample observer leftRounds rightRounds

/-- The exact initial sampler includes its context and all 32 root bytes, even in a hybrid that later ignores that root. -/
theorem rootSampler_query_bound {Context : Type} (sample : ProbComp Context)
    (qSample : Nat) (sampleBound : sample.IsTotalQueryBound qSample) :
    (rootSampler sample).IsTotalQueryBound (qSample + 32) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun context =>
    OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun root => show (pure (context, root.toList) : ProbComp (Context × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial))

/-- The initial full-output reduction retains the entire observer of both source suffixes and makes two secret-key HMAC challenge queries. -/
theorem initialReduction_query_bounds {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver) :
    let reduction := fullExpandReduction .ratchet (rootSampler sample)
      (initialObserver source observer leftRounds rightRounds)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery ((qSample + 32) + qObserver) :=
  ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (rootSampler_query_bound sample qSample sampleBound)
      (fun _ _ => observerBound _ _ _)⟩

/-- Actual initialization samples one root and its complete observer; deterministic public KDF evaluations remain actual local work. -/
theorem actualInitializedGame_query_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver) :
    (actualInitializedGame source sample observer leftRounds rightRounds).IsTotalQueryBound
      ((qSample + 32) + qObserver) := by
  rw [actualInitializedGame_eq]
  exact sourceFullGame_uniform_query_bound source .ratchet _ _
    (rootSampler_query_bound sample qSample sampleBound) (fun _ _ => observerBound _ _ _)

/-- All initialization challenger worlds retain their actual sampled root, PRK/key, blocks and complete observer costs. -/
theorem initialChallenger_query_bounds {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver) :
    let joint := rootSampler sample
    let observe := initialObserver source observer leftRounds rightRounds
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      ((qSample + 32) + qObserver) ∧
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      ((qSample + 32) + (64 + qObserver)) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (64 + ((qSample + 32) + qObserver)) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      ((qSample + 32) + (64 + (64 + qObserver))) ∧
    (independentFullGame joint observe).IsTotalQueryBound
      ((qSample + 32) + (76 + qObserver)) := by
  have rootBound := rootSampler_query_bound sample qSample sampleBound
  have outputBound : ∀ context output,
      ((initialObserver source observer leftRounds rightRounds) context output).IsTotalQueryBound qObserver :=
    fun _ _ => observerBound _ _ _
  refine ⟨?_, fullExtractUniform_uniform_query_bound hmac .ratchet _ _ rootBound outputBound,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ rootBound outputBound,
    fullHmacRandom_uniform_query_bound .ratchet _ _ rootBound outputBound,
    independentFullGame_uniform_query_bound _ _ rootBound outputBound⟩
  exact OracleComp.isTotalQueryBound_bind rootBound (fun pair => outputBound _ _)

/-- A directional hybrid charges every earlier ideal key/nonce pair and its live chain, including a live sample unused after replacement. -/
theorem sampleEvolution_query_bound (source : FixedHkdfSha512NoSaltSource) (rounds cut : Nat) :
    (sampleEvolution source rounds cut).IsTotalQueryBound (44 * cut + 32) := by
  exact OracleComp.isTotalQueryBound_bind (sampleMaterials_query_bound cut) (fun prior =>
    OracleComp.isTotalQueryBound_bind
      (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun chain => show (pure ⟨prior ++ (realEvolution source (rounds - cut) chain).records,
          (realEvolution source (rounds - cut) chain).live⟩ : ProbComp Evolution).IsTotalQueryBound 0 from trivial))

/-- The unselected direction's complete evolution remains part of a selected left hop's observer budget. -/
theorem leftObserver_query_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (observer : BidirectionalObserver Context) (rightRounds rightCut qObserver : Nat)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver)
    (context : Context) (left : Evolution) :
    (leftObserver source observer rightRounds rightCut context left).IsTotalQueryBound
      ((44 * rightCut + 32) + qObserver) :=
  OracleComp.isTotalQueryBound_bind (sampleEvolution_query_bound source rightRounds rightCut)
    (fun right => observerBound context left right)

/-- A right hop's context retains and charges the complete previously sampled left direction. -/
theorem rightContextSampler_query_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (leftRounds leftCut qSample : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample) :
    (rightContextSampler source sample leftRounds leftCut).IsTotalQueryBound
      (qSample + (44 * leftCut + 32)) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun context =>
    OracleComp.isTotalQueryBound_bind (n₂ := 0) (sampleEvolution_query_bound source leftRounds leftCut)
      (fun left => show (pure (context, left) : ProbComp (Context × Evolution)).IsTotalQueryBound 0 from trivial))

/-- The entire directional comparison pays for both retained histories, live chains and every observer query. -/
theorem bidirectionalGame_query_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds leftCut rightCut qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver) :
    (bidirectionalGame source sample observer leftRounds rightRounds leftCut rightCut).IsTotalQueryBound
      (qSample + ((44 * leftCut + 32) + ((44 * rightCut + 32) + qObserver))) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun context =>
    OracleComp.isTotalQueryBound_bind (sampleEvolution_query_bound source leftRounds leftCut)
      (fun left => leftObserver_query_bound source observer rightRounds rightCut qObserver observerBound context left))

/-- Each left-direction reduction explicitly pays for the unselected real right chain inside its observer. -/
theorem leftHopReduction_query_bounds {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (rightRounds cut remaining qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver) :
    let reduction := fullExpandReduction .ratchet (hopSampler sample cut)
      (hopObserver source (leftObserver source observer rightRounds 0) remaining)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery
        ((qSample + (44 * cut + 32)) + (32 + qObserver)) := by
  apply hopReduction_query_bounds source sample (leftObserver source observer rightRounds 0)
    cut remaining sampleBound
  intro context left
  simpa only [Nat.mul_zero, Nat.zero_add] using
    leftObserver_query_bound source observer rightRounds 0 qObserver observerBound context left

/-- Each right-direction reduction explicitly pays for the complete previously idealized left history inside its sampler. -/
theorem rightHopReduction_query_bounds {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds cut remaining qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context left right, (observer context left right).IsTotalQueryBound qObserver) :
    let reduction := fullExpandReduction .ratchet
      (hopSampler (rightContextSampler source sample leftRounds leftRounds) cut)
      (hopObserver source (rightObserver observer) remaining)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery
        (((qSample + (44 * leftRounds + 32)) + (44 * cut + 32)) + qObserver) := by
  exact hopReduction_query_bounds source _ (rightObserver observer) cut remaining
    (rightContextSampler_query_bound source sample leftRounds leftRounds qSample sampleBound)
    (fun context right => observerBound context.1 context.2 right)

/-- Every directional hop has complete challenger sampling bounds, including unused sampled chains and both random HMAC blocks. Instantiating the checked opposite-direction budgets accounts for both histories. -/
theorem hopChallenger_query_bounds {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (sample : ProbComp Context) (observer : EvolutionObserver Context)
    (cut remaining qSample qObserver : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context evolution, (observer context evolution).IsTotalQueryBound qObserver) :
    let joint := hopSampler sample cut
    let observe := hopObserver source observer remaining
    let qJoint := qSample + (44 * cut + 32)
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      (qJoint + qObserver) ∧
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      (qJoint + (64 + qObserver)) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (64 + (qJoint + qObserver)) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (qJoint + (64 + (64 + qObserver))) ∧
    (independentFullGame joint observe).IsTotalQueryBound (qJoint + (76 + qObserver)) := by
  have sampleCap := hopSampler_query_bound sample cut sampleBound
  have outputCap : ∀ context output,
      (hopObserver source observer remaining context output).IsTotalQueryBound qObserver :=
    fun _ _ => observerBound _ _
  refine ⟨?_, fullExtractUniform_uniform_query_bound hmac .ratchet _ _ sampleCap outputCap,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ sampleCap outputCap,
    fullHmacRandom_uniform_query_bound .ratchet _ _ sampleCap outputCap,
    independentFullGame_uniform_query_bound _ _ sampleCap outputCap⟩
  exact OracleComp.isTotalQueryBound_bind sampleCap (fun pair => outputCap _ _)

end BeaconcryptCore.Computational.PqxdhInitialChainComposition

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.initial_chains_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.initial_chains_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialized_pair_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialized_pair_source

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.independent_initial_eq_bidirectional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.independent_initial_eq_bidirectional

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialized_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialized_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialized_evolving_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialized_evolving_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.sourceInitialChains_bytes' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.sourceInitialChains_bytes

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.sourceInitialChains_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.sourceInitialChains_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.actualInitializedGame_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.actualInitializedGame_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.actualInitializedGame_evolving_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.actualInitializedGame_evolving_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.rootSampler_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.rootSampler_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.actualInitializedGame_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.actualInitializedGame_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialChallenger_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.initialChallenger_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.sampleEvolution_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.sampleEvolution_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.leftObserver_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.leftObserver_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.rightContextSampler_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.rightContextSampler_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.bidirectionalGame_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.bidirectionalGame_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.leftHopReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.leftHopReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.rightHopReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.rightHopReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialChainComposition.hopChallenger_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialChainComposition.hopChallenger_query_bounds
