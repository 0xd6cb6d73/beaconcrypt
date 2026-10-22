import BeaconcryptCore.Computational.PqxdhFullSecretInputKdf
import BeaconcryptCore.Computational.PqxdhComposition
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-! Ordered replacement of evolving chain outputs. Each complete expansion supplies the message key, nonce and next chain together. The stopped sampler retains earlier record material, but the consumed chain appears only as its secret input. -/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhOrderedChainHybrids

open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Material := RootOutput × NonceOutput

def material (output : FullOutput) : Material :=
  (JointKdfProjection.first32.project output, JointKdfProjection.final12.project output)

def nextChain (output : FullOutput) : RootOutput :=
  JointKdfProjection.second32.project output

structure Evolution where
  records : List Material
  live : RootOutput

def prepend (head : Material) (tail : Evolution) : Evolution :=
  ⟨head :: tail.records, tail.live⟩

def realEvolution (source : FixedHkdfSha512NoSaltSource) : Nat → RootOutput → Evolution
  | 0, chain => ⟨[], chain⟩
  | rounds + 1, chain =>
      let output := PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address chain.toList)
      prepend (material output) (realEvolution source rounds (nextChain output))

noncomputable def sampleMaterials : Nat → ProbComp (List Material)
  | 0 => pure []
  | rounds + 1 => do
      let prior ← sampleMaterials rounds
      let last ← $ᵗ Material
      pure (prior ++ [last])

abbrev EvolutionObserver (Context : Type) := Context → Evolution → ProbComp Bool

noncomputable def hybrid {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (rounds cut : Nat) :
    ProbComp Bool := do
  let context ← sample
  let prior ← sampleMaterials cut
  let chain ← $ᵗ RootOutput
  let suffix := realEvolution source (rounds - cut) chain
  observer context ⟨prior ++ suffix.records, suffix.live⟩

/-- The exact pre-hop joint sampler: earlier material and an independent 32-byte live chain. -/
noncomputable def hopSampler {Context : Type} (sample : ProbComp Context) (cut : Nat) :
    ProbComp ((Context × List Material) × Pqxdh.Bytes) := do
  let context ← sample
  let prior ← sampleMaterials cut
  let chain ← $ᵗ RootOutput
  pure ((context, prior), chain.toList)

def hopObserver {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (observer : EvolutionObserver Context) (remaining : Nat) :
    FullObserver (Context × List Material) := fun (context, prior) output =>
  let suffix := realEvolution source remaining (nextChain output)
  observer context ⟨prior ++ material output :: suffix.records, suffix.live⟩

/-- Replacing the next step retains every later derivation and the final live chain. -/
theorem hybrid_eq_sourceHop {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (cut remaining : Nat) :
    hybrid source sample observer (cut + 1 + remaining) cut =
      sourceFullGame source .ratchet (hopSampler sample cut)
        (hopObserver source observer remaining) := by
  have count : cut + 1 + remaining - cut = remaining + 1 := by omega
  simp [hybrid, sourceFullGame, hopSampler, hopObserver, count, realEvolution, prepend,
    bind_assoc]

/-- Reorder the exact three source slots without discarding any bit. -/
def materialChainEquiv : FullOutput ≃ (Material × RootOutput) :=
  PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.trans {
    toFun := fun parts => ((parts.1, parts.2.2), parts.2.1)
    invFun := fun parts => (parts.1.1, parts.2, parts.1.2)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem materialChain_uniform :
    EvalDistEq ((fun output : FullOutput => (material output, nextChain output)) <$>
      ($ᵗ FullOutput)) ($ᵗ (Material × RootOutput)) := by
  exact SampleableType.map_uniformSample_evalDistEq_of_bijective materialChainEquiv.bijective

/-- Complete continuations see a material/next-chain pair with the exact uniform joint law. -/
theorem fullOutput_observed {A : Type} (continuation : Material → RootOutput → ProbComp A) :
    EvalDistEq
      (do
        let output ← $ᵗ FullOutput
        continuation (material output) (nextChain output))
      (do
        let record ← $ᵗ Material
        let chain ← $ᵗ RootOutput
        continuation record chain) := by
  have observed := materialChain_uniform.bind_left fun pair => continuation pair.1 pair.2
  simpa only [bind_map_left, ← pairSample, bind_assoc, pure_bind] using observed

/-- The independent full-output hop is precisely the next ordered hybrid. -/
theorem independentHop_eq_hybrid {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (cut remaining : Nat) :
    EvalDistEq (independentFullGame (hopSampler sample cut) (hopObserver source observer remaining))
      (hybrid source sample observer (cut + 1 + remaining) (cut + 1)) := by
  have count : cut + 1 + remaining - (cut + 1) = remaining := by omega
  simp only [independentFullGame, hopSampler, hopObserver, hybrid, count, sampleMaterials,
    bind_assoc, pure_bind, List.append_assoc, List.singleton_append]
  refine EvalDistEq.bind_right sample fun context => ?_
  refine EvalDistEq.bind_right (sampleMaterials cut) fun prior => ?_
  have ignored (computation : ProbComp Bool) :
      EvalDistEq ((($ᵗ RootOutput) : ProbComp RootOutput) >>= fun _ => computation) computation :=
    OracleComp.EvalDistEq.bind_const _ computation
  refine (ignored _).trans ?_
  exact fullOutput_observed (fun record chain =>
    observer context ⟨prior ++ record :: (realEvolution source remaining chain).records,
      (realEvolution source remaining chain).live⟩)

/-- Explicit ordinary endpoint advantages for one ordered step, including its actual tail observer. -/
noncomputable def hopLoss {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (sample : ProbComp Context) (observer : EvolutionObserver Context)
    (cut remaining : Nat) : ℝ :=
  let joint := hopSampler sample cut
  let observe := hopObserver source observer remaining
  (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).boolDistance
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)) +
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).boolDistance
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe))

/-- The adjacent bound is proved inside the same evolving experiment, before summing losses. -/
theorem adjacent_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (cut remaining : Nat) :
    (hybrid source sample observer (cut + 1 + remaining) cut).boolDistance
      (hybrid source sample observer (cut + 1 + remaining) (cut + 1)) ≤
        hopLoss source hmac sample observer cut remaining := by
  have random := (independentHop_eq_hybrid source sample observer cut remaining).evalDist_eq
  simpa only [hybrid_eq_sourceHop, hopLoss, ProbComp.boolDistance, random] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet
      (hopSampler sample cut) (hopObserver source observer remaining)

/-- The complete ordered chain pays exactly one Extract and one HMAC advantage per derivation. -/
theorem ordered_chain_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (rounds : Nat) :
    (hybrid source sample observer rounds 0).boolDistance
      (hybrid source sample observer rounds rounds) ≤
        ∑ cut ∈ Finset.range rounds,
          hopLoss source hmac sample observer cut (rounds - cut - 1) := by
  apply PqxdhComposition.finiteHybridBound_of_hop_bounds
  intro cut before
  have count : cut + 1 + (rounds - cut - 1) = rounds := by omega
  simpa only [count] using
    adjacent_bound source hmac correct sample observer cut (rounds - cut - 1)

/-- Reading the next-chain slot is the exact production byte operation. -/
theorem nextChain_source (source : FixedHkdfSha512NoSaltSource) (chain : RootOutput) :
    (nextChain (PqxdhJointKdf.productionStream source.crypto
      (FixedHkdfDomain.ratchet.address chain.toList))).toList =
        Pqxdh.nextChain source.crypto chain.toList := by rfl

/-- Reading the message key and nonce retains the exact source pair. -/
theorem material_source (source : FixedHkdfSha512NoSaltSource) (chain : RootOutput) :
    let output := PqxdhJointKdf.productionStream source.crypto
      (FixedHkdfDomain.ratchet.address chain.toList)
    ((material output).1.toList, (material output).2.toList) =
      Pqxdh.msgMaterial source.crypto chain.toList := by rfl

/-- Every later chain is computed by the source's repeated next-chain operation. -/
theorem realEvolution_live (source : FixedHkdfSha512NoSaltSource)
    (rounds : Nat) (chain : RootOutput) :
    (realEvolution source rounds chain).live.toList =
      (Pqxdh.nextChain source.crypto)^[rounds] chain.toList := by
  induction rounds generalizing chain with
  | zero => rfl
  | succ rounds ih =>
      simp only [realEvolution, prepend, ih, nextChain_source,
        Function.iterate_succ_apply]

/-- The retained record material is exactly the existing source-shaped skip derivation list. -/
theorem realEvolution_records (source : FixedHkdfSha512NoSaltSource)
    (rounds : Nat) (chain : RootOutput) (base : Nat) :
    (realEvolution source rounds chain).records.map
      (fun record => (record.1.toList, record.2.toList)) =
      (Ratchet.skipKeys (Pqxdh.ratchetCrypto source.crypto) chain.toList base rounds).map
        Prod.snd := by
  induction rounds generalizing chain base with
  | zero => rfl
  | succ rounds ih =>
      simp only [realEvolution, prepend, List.map_cons, ih _ (base + 1), material_source,
        nextChain_source, Ratchet.skipKeys, Pqxdh.ratchetCrypto]

/-- Current-chain disclosure determines every descendant by public source evaluation. -/
theorem descendants_from_live (source : FixedHkdfSha512NoSaltSource)
    (past future : Nat) (chain : RootOutput) :
    (realEvolution source future (realEvolution source past chain).live).live.toList =
      (Pqxdh.nextChain source.crypto)^[past + future] chain.toList := by
  rw [realEvolution_live, realEvolution_live, Function.iterate_add_apply]
  exact Function.Commute.iterate_iterate (Function.Commute.refl _) future past _

/-- Sampling record material counts both key and nonce bytes. -/
theorem material_uniform_query_bound :
    ($ᵗ Material).IsTotalQueryBound 44 := by
  rw [← pairSample]
  exact OracleComp.isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun key =>
      OracleComp.isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 12)
        (fun nonce => show (pure (key, nonce) : ProbComp Material).IsTotalQueryBound 0 from trivial))

/-- Earlier ideal record material is charged in the hop sampler, not ambient free work. -/
theorem sampleMaterials_query_bound (rounds : Nat) :
    (sampleMaterials rounds).IsTotalQueryBound (44 * rounds) := by
  induction rounds with
  | zero => trivial
  | succ rounds ih =>
      simpa only [sampleMaterials, Nat.mul_succ, Nat.add_zero] using
        OracleComp.isTotalQueryBound_bind ih (fun prior =>
          OracleComp.isTotalQueryBound_bind material_uniform_query_bound
            (fun last => show (pure (prior ++ [last]) : ProbComp (List Material)).IsTotalQueryBound 0
              from trivial))

/-- The exact hop sampler counts its context, earlier record material and hidden live chain. -/
theorem hopSampler_query_bound {Context : Type} (sample : ProbComp Context)
    (cut : Nat) {qSample : Nat} (sampleBound : sample.IsTotalQueryBound qSample) :
    (hopSampler sample cut).IsTotalQueryBound (qSample + (44 * cut + 32)) := by
  exact OracleComp.isTotalQueryBound_bind sampleBound (fun context =>
    OracleComp.isTotalQueryBound_bind (sampleMaterials_query_bound cut) (fun prior =>
      OracleComp.isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
        (fun chain => show (pure ((context, prior), chain.toList) :
          ProbComp ((Context × List Material) × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)))

/-- Every ordered HMAC reduction has its own two challenge queries and full local randomness budget. -/
theorem hopReduction_query_bounds {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (cut remaining : Nat)
    {qSample qObserver : Nat} (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context evolution,
      (observer context evolution).IsTotalQueryBound qObserver) :
    let reduction := fullExpandReduction .ratchet (hopSampler sample cut)
      (hopObserver source observer remaining)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery
        ((qSample + (44 * cut + 32)) + qObserver) := by
  exact ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (hopSampler_query_bound sample cut sampleBound)
      (fun context output => observerBound _ _)⟩

noncomputable def sampleEvolution (source : FixedHkdfSha512NoSaltSource)
    (rounds cut : Nat) : ProbComp Evolution := do
  let prior ← sampleMaterials cut
  let chain ← $ᵗ RootOutput
  let suffix := realEvolution source (rounds - cut) chain
  pure ⟨prior ++ suffix.records, suffix.live⟩

/-- A named sampler exposes the exact complete state passed to the observer. -/
theorem hybrid_factor {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : EvolutionObserver Context) (rounds cut : Nat) :
    hybrid source sample observer rounds cut =
      (do let context ← sample
          let evolution ← sampleEvolution source rounds cut
          observer context evolution) := by
  simp [hybrid, sampleEvolution, bind_assoc]

abbrev BidirectionalObserver (Context : Type) := Context → Evolution → Evolution → ProbComp Bool

/-- Both directions retain the same context, and each direction's complete record history. -/
noncomputable def bidirectionalGame {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds leftCut rightCut : Nat) : ProbComp Bool := do
  let context ← sample
  let left ← sampleEvolution source leftRounds leftCut
  let right ← sampleEvolution source rightRounds rightCut
  observer context left right

noncomputable def leftObserver {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (observer : BidirectionalObserver Context) (rightRounds rightCut : Nat) :
    EvolutionObserver Context := fun context left => do
  let right ← sampleEvolution source rightRounds rightCut
  observer context left right

noncomputable def rightContextSampler {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (leftRounds leftCut : Nat) : ProbComp (Context × Evolution) := do
  let context ← sample
  let left ← sampleEvolution source leftRounds leftCut
  pure (context, left)

def rightObserver {Context : Type} (observer : BidirectionalObserver Context) :
    EvolutionObserver (Context × Evolution) := fun (context, left) right => observer context left right

theorem bidirectional_eq_left {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds leftCut rightCut : Nat) :
    bidirectionalGame source sample observer leftRounds rightRounds leftCut rightCut =
      hybrid source sample (leftObserver source observer rightRounds rightCut) leftRounds leftCut := by
  rw [hybrid_factor]
  rfl

theorem bidirectional_eq_right {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds leftCut rightCut : Nat) :
    bidirectionalGame source sample observer leftRounds rightRounds leftCut rightCut =
      hybrid source (rightContextSampler source sample leftRounds leftCut)
        (rightObserver observer) rightRounds rightCut := by
  simp [hybrid_factor, bidirectionalGame, rightContextSampler, rightObserver, bind_assoc]

/-- Both directional chains compose with all observations retained in one common experiment. -/
theorem bidirectional_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (observer : BidirectionalObserver Context)
    (leftRounds rightRounds : Nat) :
    (bidirectionalGame source sample observer leftRounds rightRounds 0 0).boolDistance
      (bidirectionalGame source sample observer leftRounds rightRounds leftRounds rightRounds) ≤
      (∑ cut ∈ Finset.range leftRounds,
        hopLoss source hmac sample (leftObserver source observer rightRounds 0)
          cut (leftRounds - cut - 1)) +
      (∑ cut ∈ Finset.range rightRounds,
        hopLoss source hmac (rightContextSampler source sample leftRounds leftRounds)
          (rightObserver observer) cut (rightRounds - cut - 1)) := by
  have left := ordered_chain_bound source hmac correct sample
    (leftObserver source observer rightRounds 0) leftRounds
  have right := ordered_chain_bound source hmac correct
    (rightContextSampler source sample leftRounds leftRounds) (rightObserver observer) rightRounds
  simp only [← bidirectional_eq_left] at left
  simp only [← bidirectional_eq_right] at right
  exact (ProbComp.boolDistance_triangle _ _ _).trans (add_le_add left right)

end BeaconcryptCore.Computational.PqxdhOrderedChainHybrids

/--
info: 'BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.ordered_chain_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.ordered_chain_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.bidirectional_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.bidirectional_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.realEvolution_records' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.realEvolution_records

/--
info: 'BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.descendants_from_live' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.descendants_from_live

/--
info: 'BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.hopReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrderedChainHybrids.hopReduction_query_bounds
