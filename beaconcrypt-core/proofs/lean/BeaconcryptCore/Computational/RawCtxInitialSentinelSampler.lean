import BeaconcryptCore.Computational.RawCtxInitialSentinel

/-!
One actual uniform64 initializer supplies the selected and opposite directional halves. The retained-parent interpreter's marker uses those halves in opposite/selected order for either direction. Its twelve-byte material coordinate is analysis-only: the full evaluated continuation discards it, and the literal reduction sampler pays76 bytes while the source initializer pays64. No source nonce, cryptographic callback or table binding is added.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialSentinelSampler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

/-- The full comparison draw supplies the same two independent directional halves after ignoring its reduction-only twelve bytes, through the complete evaluated continuation. -/
theorem full_observed {Result : Type} (next : RootOutput → RootOutput → ProbComp Result) :
    𝒟[(do let output ← $ᵗ FullOutput
          next (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.nextChain output))] =
      𝒟[(do let other ← $ᵗ RootOutput
            let target ← $ᵗ RootOutput
            next other target)] := by
  refine (PqxdhOrderedChainHybrids.fullOutput_observed (fun value target => next value.1 target)).trans ?_
  have projected : 𝒟[(Prod.fst : Material → RootOutput) <$> ($ᵗ Material)] = 𝒟[$ᵗ RootOutput] :=
    evalDist_map_fst_uniformSample_prod
  calc
    _ = 𝒟[(do let other ← Prod.fst <$> ($ᵗ Material)
               let target ← $ᵗ RootOutput
               next other target)] := by rw [bind_map_left]
    _ = _ := by
      rw [evalDist_bind, projected, ← evalDist_bind]

/-- Either actual directional half has the same complete continuation law as the comparison marker sampler; the opposite half is retained and the extra bytes never enter the source continuation. -/
theorem initial_observed {Result : Type} (second : Bool) (next : RootOutput → RootOutput → ProbComp Result) :
    𝒟[(do let output ← $ᵗ HmacBlock
          next (RawCtxInitialChildSecrecy.parts second output).1 (RawCtxInitialChildSecrecy.parts second output).2)] =
      𝒟[(do let output ← $ᵗ FullOutput
            next (material output).1 (nextChain output))] :=
  (RawCtxInitialChildSecrecy.parts_observed second next).trans (full_observed next).symm

def join (second : Bool) (other target : RootOutput) : HmacBlock :=
  if second then other ++ target else target ++ other

noncomputable def labelInitial (second beacon : Bool) (other : RootOutput) :=
  if second then RawCtxSelectedInitialSecond.initialSecond beacon other
  else RawCtxSelectedInitialConstructor.initial beacon other

/-- The orientation change retains every original initializer byte. -/
theorem join_parts (second : Bool) (output : HmacBlock) :
    join second (RawCtxInitialChildSecrecy.parts second output).1 (RawCtxInitialChildSecrecy.parts second output).2 = output := by
  cases second <;> exact RawCtxSelectedInitialConstructor.split_reconstruct output

/-- The actual nonce-free initializer installs opposite directional chains and the same full constructor result under either selected-half representation. -/
theorem constructor (request : RawCtxInitializedKdfFamily.InitialRequest) (second : Bool) (other target : RootOutput) :
    RawCtxSelectedInitialConstructor.from64 request (join second other target) =
      RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) <$>
        labelInitial second request.1 other := by
  cases second
  · exact RawCtxSelectedInitialConstructor.from64_initial request target other
  · exact RawCtxSelectedInitialSecond.from64_second request other target

/-- The exact original initializer and its entire continuation agree with the selected-half representation under the original prior sampler and adaptively chosen direction. -/
theorem native_observed {Context Result : Type} (prior : ProbComp Context)
    (request : Context → RawCtxInitializedKdfFamily.InitialRequest) (second : Context → Bool)
    (next : Context → HmacBlock → RustM ConcreteRatchetKernel → ProbComp Result) :
    𝒟[(do let context ← prior
          let output ← $ᵗ HmacBlock
          next context output (RawCtxSelectedInitialConstructor.from64 (request context) output))] =
      𝒟[(do let context ← prior
            let output ← $ᵗ FullOutput
            next context (join (second context) (material output).1 (nextChain output))
              (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain (nextChain output)) <$>
                labelInitial (second context) (request context).1 (material output).1))] := by
  refine evalDist_bind_congr' prior (fun context => ?_)
  simpa only [join_parts, constructor] using initial_observed (second context)
    (fun other target => next context (join (second context) other target)
      (RawCtxSelectedInitialConstructor.from64 (request context) (join (second context) other target)))

set_option maxRecDepth 2048 in
/-- The two literal programs pay their different draw sizes separately:64 source bytes and76 comparison bytes, each plus all prior and complete continuation work. -/
theorem execution_queries {Context Result : Type} (prior : ProbComp Context)
    (request : Context → RawCtxInitializedKdfFamily.InitialRequest) (second : Context → Bool)
    (next : Context → HmacBlock → RustM ConcreteRatchetKernel → ProbComp Result)
    (qPrior qNext : Nat) (priorBound : prior.IsTotalQueryBound qPrior)
    (nextBound : ∀ context output state, (next context output state).IsTotalQueryBound qNext) :
    (do let context ← prior
        let output ← $ᵗ HmacBlock
        next context output (RawCtxSelectedInitialConstructor.from64 (request context) output)).IsTotalQueryBound (qPrior + (64 + qNext)) ∧
      (do let context ← prior
          let output ← $ᵗ FullOutput
          next context (join (second context) (material output).1 (nextChain output))
            (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain (nextChain output)) <$>
              labelInitial (second context) (request context).1 (material output).1)).IsTotalQueryBound (qPrior + (76 + qNext)) := by
  exact ⟨RawCtxSelectedInitialConstructor.uniform_native_bound prior request next qPrior qNext priorBound nextBound,
    isTotalQueryBound_bind priorBound (fun context =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76)
        (fun output => nextBound context _ _))⟩

end BeaconcryptCore.Computational.RawCtxInitialSentinelSampler

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.full_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.full_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.initial_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.initial_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.join_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.join_parts

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.constructor

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.native_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.native_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.execution_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSentinelSampler.execution_queries
