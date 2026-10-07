-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainTable
import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates
import BeaconcryptCore.Computational.PqxdhServerAuthKeySchedule

/-! Exact chain/key cuts of an actual persistent full76 cache miss. The retained cache and counters are part of the cut; no concrete HKDF output is asserted uniform. -/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

/-- Select the unavailable 32-byte coordinate; the other32 and nonce12 remain together. -/
inductive Part where
  | chain
  | key
  deriving DecidableEq

abbrev Retained := RootOutput × NonceOutput

def split (part : Part) : FullOutput ≃ (Retained × RootOutput) :=
  materialChainEquiv.trans (match part with
    | .chain => Equiv.refl _
    | .key => {
      toFun := fun value => ((value.2, value.1.2), value.1.1)
      invFun := fun value => ((value.2, value.1.2), value.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

def retained (part : Part) (output : FullOutput) : Retained := (split part output).1
def secret (part : Part) (output : FullOutput) : RootOutput := (split part output).2
noncomputable def restore (part : Part) (value : Retained) (target : RootOutput) : FullOutput :=
  (split part).symm (value, target)

/-- Reconstitution keeps all76 source bytes, including the shared material/chain correlations. -/
theorem restore_split (part : Part) (output : FullOutput) :
    restore part (retained part output) (secret part output) = output :=
  (split part).symm_apply_apply output

/-- Reconstitution exposes precisely the supplied retained44 and target32 coordinates. -/
theorem split_restore (part : Part) (value : Retained) (target : RootOutput) :
    (retained part (restore part value target), secret part (restore part value target)) =
      (value, target) :=
  (split part).apply_symm_apply (value, target)

/-- Either chosen32 coordinate is independent of exactly the other44 bytes under the full uniform sampler. -/
theorem split_uniform (part : Part) :
    𝒮[(split part) <$> ($ᵗ FullOutput)] = 𝒮[$ᵗ (Retained × RootOutput)] :=
  evalSPMF_map_bijective_uniform_cross FullOutput (split part) (split part).bijective

/-- The equality quantifies over the complete continuation, not merely marginal projections. -/
theorem split_continuation {X : Type} (part : Part)
    (continuation : Retained → RootOutput → ProbComp X) :
    𝒮[(do let output ← $ᵗ FullOutput
          continuation (retained part output) (secret part output))] =
      𝒮[(do let value ← $ᵗ Retained
            let target ← $ᵗ RootOutput
            continuation value target)] := by
  have observed := congrArg (fun distribution => distribution >>=
    fun pair => 𝒮[continuation pair.1 pair.2]) (split_uniform part)
  simpa only [← evalSPMF_bind, bind_map_left, ← pairSample, bind_assoc, pure_bind,
    retained, secret] using observed

variable {Slot : Type} [DecidableEq Slot]

/-- This private mask has the entire pre-miss cache, coordinate, other44 bytes and post-miss counters. It never stores the new target32. -/
structure Mask (Slot : Type) where
  before : Table Slot
  coordinate : Coordinate Slot
  value : Retained
  counts : PqxdhRecordLiftLazyTable.Counts

def mask (state : State Slot) (coordinate : Coordinate Slot) (value : Retained) : Mask Slot :=
  ⟨state.1, coordinate, value, ⟨state.2.lookups + 1, state.2.draws + 1⟩⟩

noncomputable def realize (part : Part) (masked : Mask Slot) (target : RootOutput) :
    FullOutput × State Slot :=
  let output := restore part masked.value target
  (output, (masked.before.cacheQuery masked.coordinate output, masked.counts))

/-- The mask realizes the literal answer, complete updated cache and exact lookup/draw counters of the original miss. -/
theorem realize_mask (part : Part) (state : State Slot) (coordinate : Coordinate Slot)
    (output : FullOutput) :
    realize part (mask state coordinate (retained part output)) (secret part output) =
      (output, (state.1.cacheQuery coordinate output,
        ⟨state.2.lookups + 1, state.2.draws + 1⟩)) := by
  simp only [realize, mask, restore_split]

/-- One actual persistent-table miss factors its chosen coordinate under every whole-state continuation. -/
theorem miss_continuation {X : Type} (part : Part) (state : State Slot)
    (coordinate : Coordinate Slot) (missing : state.1 coordinate = none)
    (continuation : FullOutput × State Slot → ProbComp X) :
    𝒮[((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) coordinate).run state >>= continuation)] =
      𝒮[(do let value ← $ᵗ Retained
            let target ← $ᵗ RootOutput
            continuation (realize part (mask state coordinate value) target))] := by
  rw [PqxdhRecordLiftLazyTable.miss_continuation coordinate state missing]
  simpa only [realize_mask] using
    split_continuation part (fun value target => continuation (realize part (mask state coordinate value) target))

/-- The selector stops before a genuine miss; the state is sampled before that miss supplies any fresh bytes. -/
abbrev AtMiss (Slot : Type) :=
  { pair : Coordinate Slot × State Slot // pair.2.1 pair.1 = none }

noncomputable def observed {Context X : Type} (part : Part)
    (sample : ProbComp (Context × AtMiss Slot))
    (observe : Context × Mask Slot → ProbComp X) : ProbComp (RootOutput × X) := do
  let (context, atMiss) ← sample
  let result ← (PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) atMiss.val.1).run atMiss.val.2
  let answer ← observe (context, mask atMiss.val.2 atMiss.val.1 (retained part result.1))
  pure (secret part result.1, answer)

noncomputable def delayed {Context X : Type}
    (sample : ProbComp (Context × AtMiss Slot))
    (observe : Context × Mask Slot → ProbComp X) : ProbComp (RootOutput × X) := do
  let (context, atMiss) ← sample
  let value ← $ᵗ Retained
  let answer ← observe (context, mask atMiss.val.2 atMiss.val.1 value)
  let target ← $ᵗ RootOutput
  pure (target, answer)

/-- The actual selected miss permits delaying only the hidden32 past the entire masked observer. Earlier cache entries, source context and both counters remain in the joint law. -/
theorem observed_delayed {Context X : Type} (part : Part)
    (sample : ProbComp (Context × AtMiss Slot))
    (observe : Context × Mask Slot → ProbComp X) :
    𝒮[observed part sample observe] = 𝒮[delayed sample observe] := by
  simp only [observed, delayed]
  refine evalSPMF_bind_congr' sample (fun pair => ?_)
  rw [PqxdhRecordLiftLazyTable.run_miss pair.2.val.1 pair.2.val.2 pair.2.property,
    bind_map_left]
  refine (split_continuation part (fun value target => do
    let answer ← observe (pair.1, mask pair.2.val.2 pair.2.val.1 value)
    pure (target, answer))).trans ?_
  exact evalSPMF_bind_congr' ($ᵗ Retained) (fun value =>
    evalSPMF_sample_comm ($ᵗ RootOutput)
      (observe (pair.1, mask pair.2.val.2 pair.2.val.1 value))
      (fun target answer => pure (target, answer)))

/-- A target-free adaptive continuation is charged by the whole candidate list it actually returns, including repetitions and aliases. -/
theorem candidate_bound {Context X : Type} (part : Part)
    (sample : ProbComp (Context × AtMiss Slot))
    (observe : Context × Mask Slot → ProbComp X) (candidates : X → List RootOutput)
    (budget : Nat) (bounded : ∀ context answer, answer ∈ support (observe context) →
      (candidates answer).length ≤ budget) :
    Pr[fun result => result.1 ∈ candidates result.2 | observed part sample observe] ≤
      (budget : ENNReal) / (2 ^ 256 : ENNReal) := by
  have same := OracleComp.probEvent_congr'
    (p := fun result : RootOutput × X => result.1 ∈ candidates result.2)
    (q := fun result : RootOutput × X => result.1 ∈ candidates result.2)
    (fun _ _ => Iff.rfl) (observed_delayed part sample observe)
  rw [same, delayed]
  refine probEvent_bind_le_of_forall_le (fun pair _ => ?_)
  refine probEvent_bind_le_of_forall_le (fun value _ => ?_)
  refine probEvent_bind_le_of_forall_le (fun answer supported => ?_)
  rw [bind_pure_comp, probEvent_map]
  exact (RawCtxSelectedInputCandidates.uniform_candidates (candidates answer)).trans
    (ENNReal.div_le_div_right (by exact_mod_cast bounded _ answer supported) _)

noncomputable def retainedContext {Context : Type}
    (sample : ProbComp (Context × AtMiss Slot)) : ProbComp (Context × Mask Slot) := do
  let (context, atMiss) ← sample
  let value ← $ᵗ Retained
  pure (context, mask atMiss.val.2 atMiss.val.1 value)

/-- The ordinary primitive observer itself samples all target-free prior state and the retained44 bytes. Its primitive sampler has Unit context and is exactly uniform32. -/
noncomputable def unitObserver {Context : Type}
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot)) :
    FullObserver Unit := fun _ output => do
  let context ← retainedContext sample
  observe context output

/-- The next actual ratchet derivation consumes the second32 coordinate of this same cached full76 reply. -/
noncomputable def childReal {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot)) :
    ProbComp Bool := do
  let (context, atMiss) ← sample
  let result ← (PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) atMiss.val.1).run atMiss.val.2
  observe (context, mask atMiss.val.2 atMiss.val.1 (retained .chain result.1))
    (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address (secret .chain result.1).toList))

noncomputable def childUniform {Context : Type}
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot)) :
    ProbComp Bool := do
  let context ← retainedContext sample
  let output ← $ᵗ FullOutput
  observe context output

/-- The actual predecessor miss followed by its child derivation supplies the ordinary uniform32 source endpoint, under the entire retained-context observer. -/
theorem child_source {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot)) :
    𝒮[childReal source sample observe] =
      𝒮[sourceFullGame source .ratchet PqxdhServerAuthKeySchedule.uniform32
        (unitObserver sample observe)] := by
  have factor : 𝒮[childReal source sample observe] =
      𝒮[(do let context ← retainedContext sample
            let target ← $ᵗ RootOutput
            observe context (PqxdhJointKdf.productionStream source.crypto
              (FixedHkdfDomain.ratchet.address target.toList)))] := by
    simp only [childReal, retainedContext, bind_assoc, pure_bind]
    refine evalSPMF_bind_congr' sample (fun pair => ?_)
    rw [PqxdhRecordLiftLazyTable.run_miss pair.2.val.1 pair.2.val.2 pair.2.property,
      bind_map_left]
    exact split_continuation .chain (fun value target => observe
      (pair.1, mask pair.2.val.2 pair.2.val.1 value)
      (PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address target.toList)))
  rw [factor]
  simpa only [sourceFullGame, PqxdhServerAuthKeySchedule.uniform32, unitObserver,
    bind_assoc, pure_bind] using
    evalSPMF_sample_comm (retainedContext sample) ($ᵗ RootOutput)
      (fun context target => observe context (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address target.toList)))

omit [DecidableEq Slot] in
/-- The independent endpoint discards only its unused input draw and retains the whole context distribution. -/
theorem child_independent {Context : Type}
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot)) :
    𝒮[childUniform sample observe] =
      𝒮[independentFullGame PqxdhServerAuthKeySchedule.uniform32 (unitObserver sample observe)] := by
  simp only [independentFullGame, PqxdhServerAuthKeySchedule.uniform32, unitObserver,
    bind_assoc, pure_bind]
  rw [OracleComp.DeferredSampling.evalSPMF_bind_const_neverFails ($ᵗ RootOutput) (by simp)]
  exact evalSPMF_sample_comm (retainedContext sample) ($ᵗ FullOutput) observe

/-- The cut uses Extract only at the ordinary uniform32 sampler, plus a two-query uniform-secret-key HMAC reduction. No joint-sampler security assumption is added. -/
theorem child_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceFullCorrect source hmac) (sample : ProbComp (Context × AtMiss Slot))
    (observe : FullObserver (Context × Mask Slot)) :
    (childReal source sample observe).boolDistAdvantage (childUniform sample observe) ≤
      (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
        (fullExtractReduction hmac .ratchet (unitObserver sample observe))).boolDistAdvantage
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
        (fullExtractReduction hmac .ratchet (unitObserver sample observe))) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
        (unitObserver sample observe))).boolDistAdvantage
      (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
        (unitObserver sample observe))) := by
  have real := evalDist_eq_of_evalSPMF_eq _ _ (child_source source sample observe)
  have random := evalDist_eq_of_evalSPMF_eq _ _ (child_independent sample observe)
  simpa only [ProbComp.boolDistAdvantage, real, random] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet
      PqxdhServerAuthKeySchedule.uniform32 (unitObserver sample observe)

omit [DecidableEq Slot] in
/-- Retaining the private mask costs every prior-sampler query plus exactly44 byte draws. -/
theorem retained_bound {Context : Type} (sample : ProbComp (Context × AtMiss Slot))
    (qSample : Nat) (bounded : sample.IsTotalQueryBound qSample) :
    (retainedContext sample).IsTotalQueryBound (qSample + 44) := by
  refine isTotalQueryBound_bind bounded ?_
  rintro ⟨context, atMiss⟩
  exact isTotalQueryBound_bind (n₂ := 0) material_uniform_query_bound (fun value =>
    show (pure (context, mask atMiss.val.2 atMiss.val.1 value) : ProbComp (Context × Mask Slot)).IsTotalQueryBound 0 from trivial)

omit [DecidableEq Slot] in
/-- The primitive observer pays for the entire retained context and arbitrary local continuation. -/
theorem observer_bound {Context : Type} (sample : ProbComp (Context × AtMiss Slot))
    (observe : FullObserver (Context × Mask Slot)) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve)
    (unitContext : Unit) (output : FullOutput) :
    (unitObserver sample observe unitContext output).IsTotalQueryBound (qSample + 44 + qObserve) :=
  isTotalQueryBound_bind (retained_bound sample qSample sampleBound) (fun context => observeBound context output)

set_option maxRecDepth 2048 in
/-- Original source work is billed in its actual order: prior sampler, full76 miss, then all observer queries. -/
theorem child_real_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot))
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (childReal source sample observe).IsTotalQueryBound (qSample + (76 + qObserve)) := by
  refine isTotalQueryBound_bind sampleBound ?_
  rintro ⟨context, atMiss⟩
  dsimp only
  rw [PqxdhRecordLiftLazyTable.run_miss atMiss.val.1 atMiss.val.2 atMiss.property, bind_map_left]
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
    (fun output => observeBound _ _)

omit [DecidableEq Slot] in
/-- The explicit reduction uses two challenge queries and separately charges its unused32 sampler, retained44 and every prior/observer query. -/
theorem reduction_bounds {Context : Type} (sample : ProbComp (Context × AtMiss Slot))
    (observe : FullObserver (Context × Mask Slot)) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe)).IsQueryBoundP IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe)).IsQueryBoundP IsHmacUniformQuery
        (32 + (qSample + 44 + qObserve)) := by
  refine ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ ?_
      (observer_bound sample observe qSample qObserve sampleBound observeBound)⟩
  exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
    (fun input => show (pure ((), input.toList) : ProbComp (Unit × Pqxdh.Bytes)).IsTotalQueryBound 0 from trivial)

omit [DecidableEq Slot] in
/-- Every primitive challenger world pays for the prior sampler and observer; complete64-byte PRF answers remain charged even when only12 bytes are retained. -/
theorem challenger_bounds {Context : Type} (hmac : HmacSha512)
    (sample : ProbComp (Context × AtMiss Slot)) (observe : FullObserver (Context × Mask Slot))
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (unitObserver sample observe))).IsTotalQueryBound
        (32 + (qSample + 44 + qObserve)) ∧
    (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet (unitObserver sample observe))).IsTotalQueryBound
        (32 + (64 + (qSample + 44 + qObserve))) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe))).IsTotalQueryBound (64 + (32 + (qSample + 44 + qObserve))) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (unitObserver sample observe))).IsTotalQueryBound (32 + (64 + (64 + (qSample + 44 + qObserve)))) ∧
    (childUniform sample observe).IsTotalQueryBound (qSample + 44 + (76 + qObserve)) := by
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

end BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.restore_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.restore_split
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.split_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.split_restore
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.split_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.split_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.split_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.split_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.realize_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.realize_mask
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.miss_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.miss_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.observed_delayed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.observed_delayed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.candidate_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_independent
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.retained_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.observer_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.observer_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.child_real_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.reduction_bounds
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.challenger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut.challenger_bounds
