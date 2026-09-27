import BeaconcryptCore.Computational.RawCtxSelectedParentEntry

/-!
One explicitly uniform full76 predecessor response supplies its retained address/material and selected next-chain coordinate under the same complete continuation. Only the chain coordinate is delayed past an observer that receives the original context and retained entry. The context may contain all prior private state and cache information. This is a law of the stated sampler, not a proof that an actual reached source response is uniform or fresh; no source capability or storage service is added.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentSampler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open RawCtxSelectedParentEntry
variable {Context Result : Type}

noncomputable def original (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← sample
  let output ← $ᵗ FullOutput
  let result ← observe (context, fromOutput (address context) output)
  pure (nextChain output, result)

noncomputable def delayed (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← sample
  let material ← $ᵗ Material
  let result ← observe (context, ⟨address context, material⟩)
  let target ← $ᵗ RootOutput
  pure (target, result)

/-- Delaying only the independent chain coordinate retains the same entire context, predecessor entry and observer result. -/
theorem delayed_eq (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → ProbComp Result) :
    𝒮[original sample address observe] = 𝒮[delayed sample address observe] := by
  simp only [original, delayed]
  refine evalSPMF_bind_congr' sample (fun context => ?_)
  refine (fullOutput_observed (fun material target => do
    let result ← observe (context, ⟨address context, material⟩)
    pure (target, result))).trans ?_
  exact evalSPMF_bind_congr' ($ᵗ Material) (fun material =>
    evalSPMF_sample_comm ($ᵗ RootOutput) (observe (context, ⟨address context, material⟩))
      (fun target result => pure (target, result)))

set_option maxRecDepth 2048 in
/-- The original sampler charges the context, all 76 response bytes and every observer query on every reply. -/
theorem original_bound (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → ProbComp Result) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context entry, (observe (context, entry)).IsTotalQueryBound qObserve) :
    (original sample address observe).IsTotalQueryBound (qSample + (76 + qObserve)) := by
  exact isTotalQueryBound_bind sampleBound (fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) (fun output =>
      isTotalQueryBound_bind (observerBound context (fromOutput (address context) output))
        (fun result => show (pure (nextChain output, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial)))

set_option maxRecDepth 2048 in
/-- The delayed program separately charges the 44 material bytes, the full observer, and the later 32 chain bytes. -/
theorem delayed_bound (sample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : Context × Entry → ProbComp Result) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context entry, (observe (context, entry)).IsTotalQueryBound qObserve) :
    (delayed sample address observe).IsTotalQueryBound (qSample + (44 + (qObserve + 32))) := by
  exact isTotalQueryBound_bind sampleBound (fun context =>
    isTotalQueryBound_bind material_uniform_query_bound (fun material =>
      isTotalQueryBound_bind (observerBound context ⟨address context, material⟩) (fun result =>
        isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
          (fun target => show (pure (target, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial))))

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSampler.delayed_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms delayed_eq
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSampler.original_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms original_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentSampler.delayed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms delayed_bound

end BeaconcryptCore.Computational.RawCtxSelectedParentSampler
