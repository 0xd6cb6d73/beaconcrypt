-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget
import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates
import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule

/-! Exact selected32 cuts at an actual first hidden-seed lookup. Both directional halves and complete state instrumentation stay in the joint law; reaching a target-free global observer is a separate source-compiler obligation. -/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut
open PqxdhRecordLiftInterface PqxdhRecordLiftWorld PqxdhRecordLiftSeed
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- False selects Server-to-Beacon next32; true selects Beacon-to-Server right32. The opposite direction is retained. -/
def split (direction : Bool) : Seed ≃ (RootOutput × RootOutput) :=
  if direction then Equiv.refl _ else Equiv.prodComm _ _

def retained (direction : Bool) (seed : Seed) : RootOutput := (split direction seed).1
def secret (direction : Bool) (seed : Seed) : RootOutput := (split direction seed).2
noncomputable def restore (direction : Bool) (other target : RootOutput) : Seed :=
  (split direction).symm (other, target)

/-- Reconstitution preserves both complete directional halves. -/
theorem restore_split (direction : Bool) (seed : Seed) :
    restore direction (retained direction seed) (secret direction seed) = seed :=
  (split direction).symm_apply_apply seed

/-- Either chosen half has the exact ordinary uniform32 marginal independent of the other half. -/
theorem split_uniform (direction : Bool) :
    𝒮[(split direction) <$> ($ᵗ Seed)] = 𝒮[$ᵗ (RootOutput × RootOutput)] :=
  evalSPMF_map_bijective_uniform_cross Seed (split direction) (split direction).bijective

/-- Factor the actual pair sampler under any complete continuation, in both directions. -/
theorem split_continuation {X : Type} (direction : Bool)
    (continuation : RootOutput → RootOutput → ProbComp X) :
    𝒮[(do let seed ← $ᵗ Seed
          continuation (retained direction seed) (secret direction seed))] =
      𝒮[(do let other ← $ᵗ RootOutput
            let target ← $ᵗ RootOutput
            continuation other target)] := by
  have observed := congrArg (fun distribution => distribution >>=
    fun pair => 𝒮[continuation pair.1 pair.2]) (split_uniform direction)
  simpa only [← evalSPMF_bind, bind_map_left, ← pairSample, bind_assoc, pure_bind,
    retained, secret] using observed

variable {n : Nat}

/-- The mask keeps the complete pre-miss world and the opposite directional half. It contains no copy of the newly drawn target32. -/
structure Mask (n : Nat) where
  before : State n
  slot : Slot n
  role : Role
  other : RootOutput

/-- Rebuild the literal kernel reply and full post-miss state, including all sixty-four underlying draws. -/
noncomputable def realize (direction : Bool) (masked : Mask n) (target : RootOutput) :
    ConcreteRatchetKernel × State n :=
  let seed := restore direction masked.other target
  (kernel masked.role seed, { masked.before with
    seeds := (masked.before.seeds.1.cacheQuery masked.slot seed,
      ⟨masked.before.seeds.2.lookups + 1, masked.before.seeds.2.draws + 1⟩)
    primitive := ({ masked.before.primitive.1 with
      uniform := masked.before.primitive.1.uniform + 64 }, masked.before.primitive.2) })

/-- Selection stops before the chosen slot's first seed draw; the role is part of the retained schedule. -/
structure AtMiss (n : Nat) where
  state : State n
  slot : Slot n
  role : Role
  missing : state.seeds.1 slot = none

def mask (atMiss : AtMiss n) (other : RootOutput) : Mask n :=
  ⟨atMiss.state, atMiss.slot, atMiss.role, other⟩

/-- Reconstruction has the original kernel, whole cache, both seed counters and all native/effect/ROM state. -/
theorem realize_mask (direction : Bool) (atMiss : AtMiss n) (seed : Seed) :
    realize direction (mask atMiss (retained direction seed)) (secret direction seed) =
      (kernel atMiss.role seed, { atMiss.state with
        seeds := (atMiss.state.seeds.1.cacheQuery atMiss.slot seed,
          ⟨atMiss.state.seeds.2.lookups + 1, atMiss.state.seeds.2.draws + 1⟩)
        primitive := ({ atMiss.state.primitive.1 with
          uniform := atMiss.state.primitive.1.uniform + 64 }, atMiss.state.primitive.2) }) := by
  simp only [realize, mask, restore_split]

/-- This private observation reads the actual stored seed after resolution; the fallback is unreachable at a selected miss. -/
noncomputable def seedAt (state : State n) (slot : Slot n) : Seed :=
  (state.seeds.1 slot).getD (Classical.ofNonempty)

/-- Factor one literal World.resolve miss while retaining its complete reply and poststate. -/
theorem miss_continuation {X : Type} (direction : Bool) (atMiss : AtMiss n)
    (continuation : ConcreteRatchetKernel × State n → ProbComp X) :
    𝒮[((resolve atMiss.role (.hidden atMiss.slot)).run atMiss.state >>= continuation)] =
      𝒮[(do let other ← $ᵗ RootOutput
            let target ← $ᵗ RootOutput
            continuation (realize direction (mask atMiss other) target))] := by
  rw [PqxdhRecordLiftWorldBudget.resolve_miss_count atMiss.role atMiss.slot
    atMiss.state atMiss.missing, bind_map_left]
  simpa only [realize_mask] using
    split_continuation direction (fun other target =>
      continuation (realize direction (mask atMiss other) target))

noncomputable def observed {Context X : Type} (direction : Bool)
    (sample : ProbComp (Context × AtMiss n))
    (observe : Context × Mask n → ProbComp X) : ProbComp (RootOutput × X) := do
  let (context, atMiss) ← sample
  let result ← (resolve atMiss.role (.hidden atMiss.slot)).run atMiss.state
  let seed := seedAt result.2 atMiss.slot
  let answer ← observe (context, mask atMiss (retained direction seed))
  pure (secret direction seed, answer)

noncomputable def delayed {Context X : Type}
    (sample : ProbComp (Context × AtMiss n))
    (observe : Context × Mask n → ProbComp X) : ProbComp (RootOutput × X) := do
  let (context, atMiss) ← sample
  let other ← $ᵗ RootOutput
  let answer ← observe (context, mask atMiss other)
  let target ← $ᵗ RootOutput
  pure (target, answer)

/-- The actual resolve miss permits delaying the selected directional half past the entire masked observer. -/
theorem observed_delayed {Context X : Type} (direction : Bool)
    (sample : ProbComp (Context × AtMiss n))
    (observe : Context × Mask n → ProbComp X) :
    𝒮[observed direction sample observe] = 𝒮[delayed sample observe] := by
  simp only [observed, delayed]
  refine evalSPMF_bind_congr' sample (fun pair => ?_)
  rw [PqxdhRecordLiftWorldBudget.resolve_miss_count pair.2.role pair.2.slot
    pair.2.state pair.2.missing, bind_map_left]
  simp only [seedAt, QueryCache.cacheQuery_self, Option.getD_some]
  refine (split_continuation direction (fun other target => do
    let answer ← observe (pair.1, mask pair.2 other)
    pure (target, answer))).trans ?_
  exact evalSPMF_bind_congr' ($ᵗ RootOutput) (fun other =>
    evalSPMF_sample_comm ($ᵗ RootOutput) (observe (pair.1, mask pair.2 other))
      (fun target answer => pure (target, answer)))

/-- Charge every returned candidate, including duplicates, against the actual uniformly sampled hidden half. -/
theorem candidate_bound {Context X : Type} (direction : Bool)
    (sample : ProbComp (Context × AtMiss n))
    (observe : Context × Mask n → ProbComp X) (candidates : X → List RootOutput)
    (budget : Nat) (bounded : ∀ context answer, answer ∈ support (observe context) →
      (candidates answer).length ≤ budget) :
    Pr[fun result => result.1 ∈ candidates result.2 | observed direction sample observe] ≤
      (budget : ENNReal) / (2 ^ 256 : ENNReal) := by
  have same := OracleComp.probEvent_congr'
    (p := fun result : RootOutput × X => result.1 ∈ candidates result.2)
    (q := fun result : RootOutput × X => result.1 ∈ candidates result.2)
    (fun _ _ => Iff.rfl) (observed_delayed direction sample observe)
  rw [same, delayed]
  refine probEvent_bind_le_of_forall_le (fun pair _ => ?_)
  refine probEvent_bind_le_of_forall_le (fun other _ => ?_)
  refine probEvent_bind_le_of_forall_le (fun answer supported => ?_)
  rw [bind_pure_comp, probEvent_map]
  exact (RawCtxSelectedInputCandidates.uniform_candidates (candidates answer)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast bounded _ answer supported) _)

noncomputable def retainedContext {Context : Type}
    (sample : ProbComp (Context × AtMiss n)) : ProbComp (Context × Mask n) := do
  let (context, atMiss) ← sample
  let other ← $ᵗ RootOutput
  pure (context, mask atMiss other)

/-- The primitive observer samples the complete target-free context itself; the primitive input distribution has only Unit context. -/
noncomputable def unitObserver {Context : Type}
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n)) :
    FullObserver Unit := fun _ output => do
  let context ← retainedContext sample
  observe context output

/-- The first post-registration derivation consumes the selected directional half of the seed stored by the actual World.resolve. -/
noncomputable def firstReal {Context : Type} (direction : Bool)
    (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n)) :
    ProbComp Bool := do
  let (context, atMiss) ← sample
  let result ← (resolve atMiss.role (.hidden atMiss.slot)).run atMiss.state
  let seed := seedAt result.2 atMiss.slot
  observe (context, mask atMiss (retained direction seed))
    (PqxdhJointKdf.productionStream source.crypto
      (FixedHkdfDomain.ratchet.address (secret direction seed).toList))

noncomputable def firstUniform {Context : Type}
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n)) :
    ProbComp Bool := do
  let context ← retainedContext sample
  let output ← $ᵗ FullOutput
  observe context output

/-- The actual initial seed miss and next derivation have the ordinary uniform32 primitive input law under the entire retained observer. -/
theorem first_source {Context : Type} (direction : Bool) (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n)) :
    𝒮[firstReal direction source sample observe] =
      𝒮[sourceFullGame source .ratchet PqxdhServerAuthKeySchedule.uniform32
        (unitObserver sample observe)] := by
  have factor : 𝒮[firstReal direction source sample observe] =
      𝒮[(do let context ← retainedContext sample
            let target ← $ᵗ RootOutput
            observe context (PqxdhJointKdf.productionStream source.crypto
              (FixedHkdfDomain.ratchet.address target.toList)))] := by
    simp only [firstReal, retainedContext, bind_assoc, pure_bind]
    refine evalSPMF_bind_congr' sample (fun pair => ?_)
    rw [PqxdhRecordLiftWorldBudget.resolve_miss_count pair.2.role pair.2.slot
      pair.2.state pair.2.missing, bind_map_left]
    simp only [seedAt, QueryCache.cacheQuery_self, Option.getD_some]
    exact split_continuation direction (fun other target => observe
      (pair.1, mask pair.2 other)
      (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address target.toList)))
  rw [factor]
  simpa only [sourceFullGame, PqxdhServerAuthKeySchedule.uniform32, unitObserver,
    bind_assoc, pure_bind] using
    evalSPMF_sample_comm (retainedContext sample) ($ᵗ RootOutput)
      (fun context target => observe context (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address target.toList)))

/-- The uniform endpoint keeps the entire context law and discards only the primitive's unused input draw. -/
theorem first_independent {Context : Type}
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n)) :
    𝒮[firstUniform sample observe] =
      𝒮[independentFullGame PqxdhServerAuthKeySchedule.uniform32 (unitObserver sample observe)] := by
  simp only [firstUniform, independentFullGame, PqxdhServerAuthKeySchedule.uniform32,
    unitObserver, bind_assoc, pure_bind]
  rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ RootOutput) (by simp)]
  exact evalSPMF_sample_comm (retainedContext sample) ($ᵗ FullOutput) observe

/-- The first derivation uses one ordinary uniform32 Extract reduction and one two-query uniform-secret-key HMAC reduction. No joint-sampler security premise is introduced. -/
theorem first_bound {Context : Type} (direction : Bool)
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (sample : ProbComp (Context × AtMiss n))
    (observe : FullObserver (Context × Mask n)) :
    (firstReal direction source sample observe).boolDistAdvantage (firstUniform sample observe) ≤
      (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
        (fullExtractReduction hmac .ratchet (unitObserver sample observe))).boolDistAdvantage
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
        (fullExtractReduction hmac .ratchet (unitObserver sample observe))) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
        (unitObserver sample observe))).boolDistAdvantage
      (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
        (unitObserver sample observe))) := by
  have real := evalDist_eq_of_evalSPMF_eq _ _ (first_source direction source sample observe)
  have random := evalDist_eq_of_evalSPMF_eq _ _ (first_independent sample observe)
  simpa only [ProbComp.boolDistAdvantage, real, random] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet
      PqxdhServerAuthKeySchedule.uniform32 (unitObserver sample observe)

/-- The exact seed sampler pays for both complete32-byte directional halves. -/
theorem seed_bound : ($ᵗ Seed).IsTotalQueryBound 64 := by
  rw [← pairSample]
  exact isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun left =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
        (fun right => show (pure (left, right) : ProbComp Seed).IsTotalQueryBound 0 from trivial))

/-- Every query of the prior sampler and the retained opposite half is charged. -/
theorem retained_bound {Context : Type} (sample : ProbComp (Context × AtMiss n))
    (qSample : Nat) (bounded : sample.IsTotalQueryBound qSample) :
    (retainedContext sample).IsTotalQueryBound (qSample + 32) := by
  refine isTotalQueryBound_bind bounded ?_
  rintro ⟨context, atMiss⟩
  exact isTotalQueryBound_bind (n₂ := 0)
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun other =>
      show (pure (context, mask atMiss other) : ProbComp (Context × Mask n)).IsTotalQueryBound 0 from trivial)

/-- The constructed primitive observer retains every prior and adaptive observer query. -/
theorem observer_bound {Context : Type} (sample : ProbComp (Context × AtMiss n))
    (observe : FullObserver (Context × Mask n)) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve)
    (unitContext : Unit) (output : FullOutput) :
    (unitObserver sample observe unitContext output).IsTotalQueryBound (qSample + 32 + qObserve) :=
  isTotalQueryBound_bind (retained_bound sample qSample sampleBound) (fun context => observeBound context output)

set_option maxRecDepth 2048 in
/-- The original-order source experiment pays for the complete64 seed draw and every prior/observer query. -/
theorem first_real_bound {Context : Type} (direction : Bool)
    (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n))
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (firstReal direction source sample observe).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  refine isTotalQueryBound_bind sampleBound ?_
  rintro ⟨context, atMiss⟩
  dsimp only
  rw [PqxdhRecordLiftWorldBudget.resolve_miss_count atMiss.role atMiss.slot
    atMiss.state atMiss.missing, bind_map_left]
  exact isTotalQueryBound_bind seed_bound (fun seed => observeBound _ _)

/-- The HMAC reduction makes at most two challenge queries, with all sampling charged separately. -/
theorem reduction_bounds {Context : Type} (sample : ProbComp (Context × AtMiss n))
    (observe : FullObserver (Context × Mask n)) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe)).IsQueryBoundP IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe)).IsQueryBoundP IsHmacUniformQuery
        (32 + (qSample + 32 + qObserve)) := by
  refine ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ ?_
      (observer_bound sample observe qSample qObserve sampleBound observeBound)⟩
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)

/-- Challenger bills include the unused32 input draw, complete64 PRF replies, the opposite32 seed half and every contextual query. -/
theorem challenger_bounds {Context : Type} (hmac : HmacSha512)
    (sample : ProbComp (Context × AtMiss n)) (observe : FullObserver (Context × Mask n))
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (unitObserver sample observe))).IsTotalQueryBound
        (32 + (qSample + 32 + qObserve)) ∧
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (unitObserver sample observe))).IsTotalQueryBound
        (32 + (64 + (qSample + 32 + qObserve))) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe))).IsTotalQueryBound (64 + (32 + (qSample + 32 + qObserve))) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe))).IsTotalQueryBound (32 + (64 + (64 + (qSample + 32 + qObserve)))) ∧
    (firstUniform sample observe).IsTotalQueryBound (qSample + 32 + (76 + qObserve)) := by
  have inputBound : PqxdhServerAuthKeySchedule.uniform32.IsTotalQueryBound 32 :=
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
      (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)
  have observerBound := observer_bound sample observe qSample qObserve sampleBound observeBound
  refine ⟨?_, fullExtractUniform_uniform_query_bound hmac .ratchet _ _ inputBound observerBound,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ inputBound observerBound,
    fullHmacRandom_uniform_query_bound .ratchet _ _ inputBound observerBound, ?_⟩
  · exact isTotalQueryBound_bind inputBound (fun pair => observerBound pair.1 _)
  · exact isTotalQueryBound_bind (retained_bound sample qSample sampleBound) (fun context =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
        (fun output => observeBound context output))

/-- The actual post-registration role constructors use the selected halves in opposite physical send/receive fields. -/
theorem kernel_inputs (seed : Seed) :
    ((kernel .server seed).refined.send_chain,
      (kernel .server seed).refined.receive_chain) =
      (RawCtxFreshChainCut.concreteChain (secret false seed),
        RawCtxFreshChainCut.concreteChain (secret true seed)) ∧
    ((kernel .beacon seed).refined.send_chain,
      (kernel .beacon seed).refined.receive_chain) =
      (RawCtxFreshChainCut.concreteChain (secret true seed),
        RawCtxFreshChainCut.concreteChain (secret false seed)) := by
  have server := congrArg (fun work =>
    (fun (value : ConcreteRatchetKernel) =>
      (value.refined.send_chain, value.refined.receive_chain)) <$> work) (kernel_exact .server seed)
  have beacon := congrArg (fun work =>
    (fun (value : ConcreteRatchetKernel) =>
      (value.refined.send_chain, value.refined.receive_chain)) <$> work) (kernel_exact .beacon seed)
  change RustM.ok (RawCtxFreshChainCut.concreteChain seed.1, RawCtxFreshChainCut.concreteChain seed.2) =
    RustM.ok ((kernel .server seed).refined.send_chain, (kernel .server seed).refined.receive_chain) at server
  change RustM.ok (RawCtxFreshChainCut.concreteChain seed.2, RawCtxFreshChainCut.concreteChain seed.1) =
    RustM.ok ((kernel .beacon seed).refined.send_chain, (kernel .beacon seed).refined.receive_chain) at beacon
  exact ⟨(RustM.ok.inj server).symm, (RustM.ok.inj beacon).symm⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.restore_split' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.restore_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.split_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.split_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.split_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.split_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.realize_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.realize_mask

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.miss_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.miss_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.observed_delayed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.observed_delayed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.candidate_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_independent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.seed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.seed_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.retained_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.observer_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.observer_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.first_real_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.challenger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.challenger_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.kernel_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut.kernel_inputs
