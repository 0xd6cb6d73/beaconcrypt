import BeaconcryptCore.Computational.RawCtxSelectedInitialEntry

/-!
The initial first32 coordinate is delayed only from explicitly uniform 64/76-byte samplers. Both laws quantify over the complete continuation and retain the other directional chain, the full76 nonce when sampled, the address and all earlier context. They do not transport source costs through distribution equality or claim that an arbitrary reached native response is uniform.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialSampler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedInitialEntry

abbrev Remainder := RootOutput × NonceOutput

def firstChain (output : FullOutput) : RootOutput :=
  JointKdfProjection.first32.project output

def remainder (output : FullOutput) : Remainder :=
  (JointKdfProjection.second32.project output, JointKdfProjection.final12.project output)

def fullEquiv : FullOutput ≃ (Remainder × RootOutput) :=
  PqxdhProjectionCollisions.jointKdfStreamProjectionEquiv.trans {
    toFun := fun parts => (parts.2, parts.1)
    invFun := fun parts => (parts.2, parts.1)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Uniform full76 splits into the retained second32/nonce pair and the missing first32. -/
theorem full_uniform :
    𝒮[(fun output : FullOutput => (remainder output, firstChain output)) <$>
      ($ᵗ FullOutput)] = 𝒮[$ᵗ (Remainder × RootOutput)] := by
  exact evalSPMF_map_bijective_uniform_cross FullOutput fullEquiv fullEquiv.bijective

/-- Splitting the same full output preserves every effect and result of an arbitrary complete continuation. -/
theorem full_observed {Result : Type} (continuation : Remainder → RootOutput → ProbComp Result) :
    𝒮[(do let output ← $ᵗ FullOutput
          continuation (remainder output) (firstChain output))] =
      𝒮[(do let other ← $ᵗ Remainder
            let target ← $ᵗ RootOutput
            continuation other target)] := by
  have observed := congrArg (fun (distribution : SPMF (Remainder × RootOutput)) => distribution >>=
    fun pair => 𝒮[continuation pair.1 pair.2]) full_uniform
  simpa only [← evalSPMF_bind, bind_map_left, ← pairSample, bind_assoc, pure_bind] using observed

noncomputable def original {Context Result : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → ProbComp Result) :
    ProbComp (RootOutput × Result) := do
  let context ← sample
  let output ← $ᵗ FullOutput
  let result ← observe (context, fromOutput (address context) output)
  pure (firstChain output, result)

noncomputable def delayed {Context Result : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → ProbComp Result) :
    ProbComp (RootOutput × Result) := do
  let context ← sample
  let other ← $ᵗ Remainder
  let result ← observe (context, ⟨address context, other.1, other.2⟩)
  let target ← $ᵗ RootOutput
  pure (target, result)

/-- Delaying only the missing first32 retains the same original context, full76 remainder and complete observation. -/
theorem delayed_eq {Context Result : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → ProbComp Result) :
    𝒮[original sample address observe] = 𝒮[delayed sample address observe] := by
  simp only [original, delayed]
  refine evalSPMF_bind_congr' sample (fun context => ?_)
  refine (full_observed (fun other target => do
    let result ← observe (context, ⟨address context, other.1, other.2⟩)
    pure (target, result))).trans ?_
  exact evalSPMF_bind_congr' ($ᵗ Remainder) (fun other =>
    evalSPMF_sample_comm ($ᵗ RootOutput) (observe (context, ⟨address context, other.1, other.2⟩))
      (fun target result => pure (target, result)))

def initialOther (output : HmacBlock) : RootOutput := (vectorSplitEquiv 32 32 output).2

def initialEquiv : HmacBlock ≃ (RootOutput × RootOutput) :=
  (vectorSplitEquiv 32 32).trans (Equiv.prodComm RootOutput RootOutput)

/-- Uniform initial64 contains two independent32-byte halves, in retained-other/selected-first order. -/
theorem initial_uniform :
    𝒮[(fun output : HmacBlock => (initialOther output, PqxdhSecretInputKdf.first32 output)) <$>
      ($ᵗ HmacBlock)] = 𝒮[$ᵗ (RootOutput × RootOutput)] := by
  exact evalSPMF_map_bijective_uniform_cross HmacBlock initialEquiv initialEquiv.bijective

/-- The two halves may be passed separately to the full continuation without discarding any initial64 bit. -/
theorem initial_observed {Result : Type} (continuation : RootOutput → RootOutput → ProbComp Result) :
    𝒮[(do let output ← $ᵗ HmacBlock
          continuation (initialOther output) (PqxdhSecretInputKdf.first32 output))] =
      𝒮[(do let other ← $ᵗ RootOutput
            let target ← $ᵗ RootOutput
            continuation other target)] := by
  have observed := congrArg (fun (distribution : SPMF (RootOutput × RootOutput)) => distribution >>=
    fun pair => 𝒮[continuation pair.1 pair.2]) initial_uniform
  simpa only [← evalSPMF_bind, bind_map_left, ← pairSample, bind_assoc, pure_bind] using observed

/-- The initial64 split and the full76 split select the same two byte vectors. -/
theorem shared_prefix_parts (output : FullOutput) :
    initialOther (initialPrefix output) = (remainder output).1 ∧
      PqxdhSecretInputKdf.first32 (initialPrefix output) = firstChain output := by
  rcases output with ⟨bytes, width⟩
  constructor <;> apply List.Vector.toList_injective
  all_goals simp [initialOther, initialPrefix, vectorSplitEquiv, firstChain,
    PqxdhSecretInputKdf.first32, remainder, JointKdfProjection.project,
    List.Vector.take, List.Vector.toList, PqxdhJointKdf.first32, PqxdhJointKdf.second32, streamBytes, List.drop_take, List.take_take]

noncomputable def initialOriginal {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → RootOutput → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← sample
  let output ← $ᵗ HmacBlock
  let result ← observe context (initialOther output)
  pure (PqxdhSecretInputKdf.first32 output, result)

noncomputable def initialDelayed {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → RootOutput → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← sample
  let other ← $ᵗ RootOutput
  let result ← observe context other
  let target ← $ᵗ RootOutput
  pure (target, result)

/-- An actual64-byte uniform draw can delay first32 past a complete observer that retains the other direction. -/
theorem initial_delayed_eq {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → RootOutput → ProbComp Result) :
    𝒮[initialOriginal sample observe] = 𝒮[initialDelayed sample observe] := by
  simp only [initialOriginal, initialDelayed]
  refine evalSPMF_bind_congr' sample (fun context => ?_)
  refine (initial_observed (fun other target => do
    let result ← observe context other
    pure (target, result))).trans ?_
  exact evalSPMF_bind_congr' ($ᵗ RootOutput) (fun other =>
    evalSPMF_sample_comm ($ᵗ RootOutput) (observe context other) (fun target result => pure (target, result)))

set_option maxRecDepth 2048 in
/-- The full76 source sampler pays every context, output-byte and continuation request. -/
theorem original_bound {Context Result : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context entry, (observe (context, entry)).IsTotalQueryBound qObserve) :
    (original sample address observe).IsTotalQueryBound (qSample + (76 + qObserve)) := by
  exact isTotalQueryBound_bind sampleBound (fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) (fun output =>
      isTotalQueryBound_bind (observerBound context (fromOutput (address context) output))
        (fun result => show (pure (firstChain output, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial)))

set_option maxRecDepth 2048 in
/-- The delayed full76 interpreter pays44 retained bytes, all continuation work and32 delayed bytes. -/
theorem delayed_bound {Context Result : Type} (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (observe : Context × Entry → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context entry, (observe (context, entry)).IsTotalQueryBound qObserve) :
    (delayed sample address observe).IsTotalQueryBound (qSample + (44 + (qObserve + 32))) := by
  exact isTotalQueryBound_bind sampleBound (fun context =>
    isTotalQueryBound_bind PqxdhOrderedChainHybrids.material_uniform_query_bound (fun other =>
      isTotalQueryBound_bind (observerBound context ⟨address context, other.1, other.2⟩) (fun result =>
        isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
          (fun target => show (pure (target, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial))))

set_option maxRecDepth 2048 in
/-- The initial64 program pays64 actual uniform byte requests plus all context and observation work. -/
theorem initial_original_bound {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → RootOutput → ProbComp Result) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context other, (observe context other).IsTotalQueryBound qObserve) :
    (initialOriginal sample observe).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  exact isTotalQueryBound_bind sampleBound (fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) (fun output =>
      isTotalQueryBound_bind (observerBound context (initialOther output))
        (fun result => show (pure (PqxdhSecretInputKdf.first32 output, result) :
          ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial)))

set_option maxRecDepth 2048 in
/-- The initial64 delayed program pays both32-byte draws explicitly without using a distribution equality as a cost proof. -/
theorem initial_delayed_bound {Context Result : Type} (sample : ProbComp Context)
    (observe : Context → RootOutput → ProbComp Result) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observerBound : ∀ context other, (observe context other).IsTotalQueryBound qObserve) :
    (initialDelayed sample observe).IsTotalQueryBound (qSample + (32 + (qObserve + 32))) := by
  exact isTotalQueryBound_bind sampleBound (fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun other =>
      isTotalQueryBound_bind (observerBound context other) (fun result =>
        isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
          (fun target => show (pure (target, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial))))

end BeaconcryptCore.Computational.RawCtxSelectedInitialSampler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.full_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.full_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.full_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.full_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.delayed_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.delayed_eq

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_observed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.shared_prefix_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.shared_prefix_parts

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_delayed_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_delayed_eq

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.original_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.original_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.delayed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.delayed_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_original_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_original_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_delayed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSampler.initial_delayed_bound
