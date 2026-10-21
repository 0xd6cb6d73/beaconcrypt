import BeaconcryptCore.Computational.RawCtxSelectedParentSampler
import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates

/-!
The same complete uniform predecessor response supplies its retained material and the next secret input. The following endpoint keeps the actual prior context, predecessor address, complete challenge response and continued observation together. The observer never receives the predecessor's second32 coordinate. Public computations inside that observer remain actual fixed computations.

These are the primitive hop and sampling laws consumed by the native reached-cut composition. A source cut must supply its concrete observer and preserve the retained cache and exposure events; no arbitrary reached-state uniformity or absence of disclosure is assumed here. Primitive Extract security remains attached to the displayed joint sampler, and Expand uses the existing ordinary two-query HMAC game.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhOrderedChainHybrids RawCtxSelectedParentEntry

/-- This sampler retains the original full76 draw; it does not sample a new chain independently of its material. -/
noncomputable def joint {Context : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp ((Context × Entry) × Pqxdh.Bytes) := do
  let context ← sample
  let output ← $ᵗ FullOutput
  pure ((context, fromOutput (address context) output), (nextChain output).toList)

/-- The target coordinate can equivalently be sampled after the complete retained context and material. -/
noncomputable def separated {Context : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp ((Context × Entry) × Pqxdh.Bytes) := do
  let context ← sample
  let material ← $ᵗ Material
  let target ← $ᵗ RootOutput
  pure ((context, ⟨address context, material⟩), target.toList)

/-- Equality holds for the full joint distribution, including the retained parent entry and every prior context field. -/
theorem joint_separated {Context : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) : EvalDistEq (joint sample address) (separated sample address) := by
  exact EvalDistEq.bind_right sample (fun context => fullOutput_observed (fun value target =>
    pure ((context, Entry.mk (address context) value), target.toList)))

noncomputable def actual {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observer : FullObserver (Context × Entry)) : ProbComp Bool := do
  let context ← sample
  let parent ← $ᵗ FullOutput
  observer (context, fromOutput (address context) parent)
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address (nextChain parent).toList))

noncomputable def random {Context : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observer : FullObserver (Context × Entry)) : ProbComp Bool :=
  independentFullGame (joint sample address) observer

/-- The exact same predecessor draw and entire continuation are the source side of the existing secret-input endpoint. -/
theorem actual_source {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observer : FullObserver (Context × Entry)) :
    actual source sample address observer = sourceFullGame source .ratchet (joint sample address) observer := by
  simp only [actual, sourceFullGame, joint, bind_assoc, pure_bind]

/-- Coefficient-one Extract and ordinary HMAC terms at the same actual predecessor/input/context distribution. -/
theorem primitive_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observer : FullObserver (Context × Entry)) :
    (actual source sample address observer).boolDistAdvantage (random sample address observer) ≤
      (extractRealGame hmac (joint sample address) (fullExtractReduction hmac .ratchet observer)).boolDistAdvantage
        (extractUniformGame (joint sample address) (fullExtractReduction hmac .ratchet observer)) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint sample address) observer)).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (joint sample address) observer)) := by
  simpa only [actual_source, random] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet (joint sample address) observer

set_option maxRecDepth 2048 in
/-- Sampling the prior context and complete parent response is charged in the actual original order. -/
theorem joint_bound {Context : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (qSample : Nat)
    (bounded : sample.IsTotalQueryBound qSample) :
    (joint sample address).IsTotalQueryBound (qSample + 76) := by
  exact isTotalQueryBound_bind bounded (fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
      (fun output => show
        (pure ((context, fromOutput (address context) output), (nextChain output).toList) :
          ProbComp ((Context × Entry) × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial))

/-- Every constructed HMAC reduction retains the complete predecessor and observer costs and makes at most two challenge queries. -/
theorem reduction_bounds {Context : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observer : FullObserver (Context × Entry))
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet (joint sample address) observer).IsQueryBoundP IsHmacChallengeQuery 2 ∧
      (fullExpandReduction .ratchet (joint sample address) observer).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + qObserve) := by
  exact ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (joint_bound sample address qSample sampleBound) observerBound⟩

/-- The actual parent-then-child source execution retains both the complete parent draw and all observer work. -/
theorem actual_uniform {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observer : FullObserver (Context × Entry)) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserve) :
    (actual source sample address observer).IsTotalQueryBound ((qSample + 76) + qObserve) := by
  simpa only [actual_source] using sourceFullGame_uniform_query_bound source .ratchet _ _
    (joint_bound sample address qSample sampleBound) observerBound

set_option maxRecDepth 2048 in
/-- All challenger worlds pay for the same parent sampler, both random HMAC blocks where used, and the full original observer. -/
theorem challenger_bounds {Context : Type} (hmac : HmacSha512)
    (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observer : FullObserver (Context × Entry)) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context output, (observer context output).IsTotalQueryBound qObserve) :
    (extractRealGame hmac (joint sample address) (fullExtractReduction hmac .ratchet observer)).IsTotalQueryBound
        ((qSample + 76) + qObserve) ∧
    (extractUniformGame (joint sample address) (fullExtractReduction hmac .ratchet observer)).IsTotalQueryBound
        ((qSample + 76) + (64 + qObserve)) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint sample address) observer)).IsTotalQueryBound
        (64 + ((qSample + 76) + qObserve)) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet (joint sample address) observer)).IsTotalQueryBound
        ((qSample + 76) + (64 + (64 + qObserve))) ∧
    (random sample address observer).IsTotalQueryBound ((qSample + 76) + (76 + qObserve)) := by
  refine ⟨?_,
    fullExtractUniform_uniform_query_bound hmac .ratchet _ _ (joint_bound sample address qSample sampleBound) observerBound,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ (joint_bound sample address qSample sampleBound) observerBound,
    fullHmacRandom_uniform_query_bound .ratchet _ _ (joint_bound sample address qSample sampleBound) observerBound,
    independentFullGame_uniform_query_bound _ _ (joint_bound sample address qSample sampleBound) observerBound⟩
  exact isTotalQueryBound_bind (joint_bound sample address qSample sampleBound)
    (fun pair => observerBound pair.1 _)

/-- The complete target-free continuation may retain prior entries and repeat candidates; the unconditioned hit bound counts its actual whole list. -/
theorem candidate_bound {Context Result : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → ProbComp Result)
    (candidates : Result → List RootOutput) (budget : Nat)
    (bounded : ∀ context result, result ∈ support (observe context) → (candidates result).length ≤ budget) :
    Pr{let result ← RawCtxSelectedParentSampler.original sample address observe}[result.1 ∈ candidates result.2] ≤
      (budget : ENNReal) / (2 ^ 256 : ENNReal) := by
  have delayed := (RawCtxSelectedParentSampler.delayed_eq sample address observe).prEvent_eq
    (fun result : RootOutput × Result => result.1 ∈ candidates result.2)
  rw [delayed, RawCtxSelectedParentSampler.delayed]
  refine prEvent_bind_le_of_forall_le _ _ _ (fun context => ?_)
  refine prEvent_bind_le_of_forall_le _ _ _ (fun value => ?_)
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ (fun result supported => ?_)
  rw [bind_pure_comp _ ($ᵗ RootOutput), prEvent_map]
  exact (RawCtxSelectedInputCandidates.uniform_candidates (candidates result)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast bounded _ result supported) _)

end BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint_separated

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.actual_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.primitive_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.joint_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.actual_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.actual_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.challenger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.challenger_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentSecrecy.candidate_bound
