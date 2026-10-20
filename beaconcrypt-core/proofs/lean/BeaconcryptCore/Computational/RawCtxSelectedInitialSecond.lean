import BeaconcryptCore.Computational.RawCtxSelectedInitialConstructor
import BeaconcryptCore.Computational.RawCtxSelectedParentTable

/-!
The actual64-byte initializer also supports hiding its second32 coordinate: Beacon sends and Server receives on that coordinate. The retained state stores only first32, with the same opposite role orientation, zero counters and empty cache. The proofs split one actual64 draw into its two halves and retain arbitrary complete continuations. Full76 appears only through an explicit prefix comparison; no initial nonce or additional12-byte source draw is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedInitialSecond
open RawCtxSelectedChain RawCtxChainInterpretation
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialRatchetComplementarity PqxdhRefinement
open RawCtxSelectedInitialConstructor RawCtxSelectedInitialSampler

abbrev secondChain := initialOther

def initialSecond (beacon : Bool) (other : RootOutput) : RustM Kernel :=
  initial (!beacon) other

/-- The exact source split places the hidden second32 in Beacon-send and Server-receive. -/
theorem split64_second (request : RawCtxInitializedKdfFamily.InitialRequest) (other target : RootOutput) :
    pqxdh.split_initial_ratchet_kdf_output (response64 (other ++ target)).bytes
      (if request.1 then (beaconPending request.2).initialization else (serverPending request.2).initialization) =
    ok ⟨interpret (RawCtxFreshChainCut.concreteChain target) (sendSlot (!request.1) other),
      interpret (RawCtxFreshChainCut.concreteChain target) (receiveSlot (!request.1) other)⟩ := by
  rcases request with ⟨role, root⟩
  cases role with
  | false =>
    obtain ⟨left, right, split, hleft, hright⟩ := splitInitialServer_exact (response64 (other ++ target)).bytes
    simpa only [chain_eq_of_refines hleft (halves64 other target).1,
      chain_eq_of_refines hright (halves64 other target).2,
      Bool.not_false, sendSlot, receiveSlot, Bool.false_eq_true, ite_false, ite_true, serverPending, interpret] using split
  | true =>
    obtain ⟨left, right, split, hleft, hright⟩ := splitInitialBeacon_exact (response64 (other ++ target)).bytes
    simpa only [chain_eq_of_refines hleft (halves64 other target).2,
      chain_eq_of_refines hright (halves64 other target).1,
      Bool.not_true, sendSlot, receiveSlot, Bool.false_eq_true, ite_false, ite_true, beaconPending, interpret] using split

/-- The original64-byte initializer is exactly the second32-hidden constructor in both roles. -/
theorem from64_second (request : RawCtxInitializedKdfFamily.InitialRequest) (other target : RootOutput) :
    from64 request (other ++ target) =
      nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initialSecond request.1 other := by
  have split := split64_second request other target
  rcases request with ⟨role, root⟩
  cases role <;> simp only [from64, Bool.false_eq_true, ite_false, ite_true,
    pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition] at split ⊢
  all_goals rw [split, bind_tc_ok, new_map]
  all_goals rfl

/-- Uniform64 splits in retained-first/selected-second order without losing any original response bit. -/
theorem second_uniform :
    𝒮[(fun output : HmacBlock => (PqxdhSecretInputKdf.first32 output, secondChain output)) <$>
      ($ᵗ HmacBlock)] = 𝒮[$ᵗ (RootOutput × RootOutput)] := by
  exact evalSPMF_map_bijective_uniform_cross HmacBlock (vectorSplitEquiv 32 32)
    (vectorSplitEquiv 32 32).bijective

/-- The same two-half draw preserves an arbitrary complete continuation in retained-first order. -/
theorem second_observed {Result : Type} (continuation : RootOutput → RootOutput → ProbComp Result) :
    𝒮[(do let output ← $ᵗ HmacBlock
          continuation (PqxdhSecretInputKdf.first32 output) (secondChain output))] =
      𝒮[(do let other ← $ᵗ RootOutput
            let target ← $ᵗ RootOutput
            continuation other target)] := by
  have observed := congrArg (fun (distribution : SPMF (RootOutput × RootOutput)) => distribution >>=
    fun pair => 𝒮[continuation pair.1 pair.2]) second_uniform
  simpa only [← evalSPMF_bind, bind_map_left, ← pairSample, bind_assoc, pure_bind] using observed

/-- A retained full76 predecessor initializes only its first32 and hidden second32; the analysis nonce is unused. -/
theorem full_second (request : RawCtxInitializedKdfFamily.InitialRequest)
    (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput) :
    RawCtxInitializedKdfFamily.initialProject request (RawCtxSelectedParentEntry.realize entry target) =
      nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initialSecond request.1 entry.material.1 := by
  rw [← full_prefix, ← split_reconstruct (initialPrefix (RawCtxSelectedParentEntry.realize entry target))]
  simp only [(shared_prefix_parts (RawCtxSelectedParentEntry.realize entry target)).1,
    (shared_prefix_parts (RawCtxSelectedParentEntry.realize entry target)).2,
    remainder, firstChain, RawCtxSelectedParentEntry.projection_parts, RawCtxSelectedParentEntry.projected]
  exact from64_second request entry.material.1 target

/-- The fixed source supplies the exact second32-hidden constructor from its actual initial64 response. -/
theorem source_second (source : FixedHkdfSha512NoSaltSource) (request : RawCtxInitializedKdfFamily.InitialRequest) :
    RawCtxInitializedKdfFamily.initialReply source request =
      nativeKernel (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain
        (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)))) <$>
      initialSecond request.1 (RawCtxSelectedParentEntry.fromOutput
        (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)
        (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩))).material.1 := by
  rw [← RawCtxInitializedKdfFamily.initial_projection]
  simpa only [RawCtxSelectedParentEntry.realize_fromOutput] using full_second request
    (RawCtxSelectedParentEntry.fromOutput (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)
      (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)))
    (PqxdhOrderedChainHybrids.nextChain
      (productionStream source.crypto (RawCtxKdfRequestTable.address ⟨request.2, ratchet.SYM_RATCHET_INFO⟩)))

/-- Splitting the actual64 draw preserves both roles and every result of the complete native continuation. -/
theorem uniform_native_second {Context Result : Type} (sample : ProbComp Context)
    (request : Context → RawCtxInitializedKdfFamily.InitialRequest)
    (observe : Context → HmacBlock → RustM ConcreteRatchetKernel → ProbComp Result) :
    𝒮[(do let context ← sample
          let output ← $ᵗ HmacBlock
          observe context output (from64 (request context) output))] =
    𝒮[(do let context ← sample
          let other ← $ᵗ RootOutput
          let target ← $ᵗ RootOutput
          observe context (other ++ target)
            (nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initialSecond (request context).1 other))] := by
  refine evalSPMF_bind_congr' sample (fun context => ?_)
  simpa only [split_reconstruct, from64_second] using
    second_observed (fun other target =>
      observe context (other ++ target) (from64 (request context) (other ++ target)))

noncomputable def original {Context Result : Type} (sample : ProbComp Context)
    (role : Context → Bool) (observe : Context → RustM Kernel → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← sample
  let output ← $ᵗ HmacBlock
  let result ← observe context (initialSecond (role context) (PqxdhSecretInputKdf.first32 output))
  pure (secondChain output, result)

noncomputable def delayed {Context Result : Type} (sample : ProbComp Context)
    (role : Context → Bool) (observe : Context → RustM Kernel → ProbComp Result) : ProbComp (RootOutput × Result) := do
  let context ← sample
  let other ← $ᵗ RootOutput
  let result ← observe context (initialSecond (role context) other)
  let target ← $ᵗ RootOutput
  pure (target, result)

/-- The omitted second32 may be drawn after a complete observer of the actual private constructor and retained first32. -/
theorem delayed_second {Context Result : Type} (sample : ProbComp Context)
    (role : Context → Bool) (observe : Context → RustM Kernel → ProbComp Result) :
    𝒮[original sample role observe] = 𝒮[delayed sample role observe] := by
  simp only [original, delayed]
  refine evalSPMF_bind_congr' sample (fun context => ?_)
  refine (second_observed (fun other target => do
    let result ← observe context (initialSecond (role context) other)
    pure (target, result))).trans ?_
  exact evalSPMF_bind_congr' ($ᵗ RootOutput) (fun other =>
    evalSPMF_sample_comm_vcvioLegacy ($ᵗ RootOutput) (observe context (initialSecond (role context) other))
      (fun target result => pure (target, result)))

set_option maxRecDepth 2048 in
/-- The original second32 cut pays64 uniform bytes and every earlier sampler and observation request. -/
theorem original_bound {Context Result : Type} (sample : ProbComp Context)
    (role : Context → Bool) (observe : Context → RustM Kernel → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context kernel, (observe context kernel).IsTotalQueryBound qObserve) :
    (original sample role observe).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  exact isTotalQueryBound_bind sampleBound fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) fun output =>
      isTotalQueryBound_bind (observeBound context _) fun result =>
        show (pure (secondChain output, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial

set_option maxRecDepth 2048 in
/-- The delayed interpreter separately pays both32-byte draws and the entire retained-state observation. -/
theorem delayed_bound {Context Result : Type} (sample : ProbComp Context)
    (role : Context → Bool) (observe : Context → RustM Kernel → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context kernel, (observe context kernel).IsTotalQueryBound qObserve) :
    (delayed sample role observe).IsTotalQueryBound (qSample + (32 + (qObserve + 32))) := by
  exact isTotalQueryBound_bind sampleBound fun context =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) fun other =>
      isTotalQueryBound_bind (observeBound context _) fun result =>
        isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) fun target =>
          show (pure (target, result) : ProbComp (RootOutput × Result)).IsTotalQueryBound 0 from trivial

/-- Both actual role initializers use the same selected and retained halves, with complementary directions and no second source draw. -/
theorem paired_roles (root : Std.Array Std.U8 32#usize) (other target : RootOutput) :
    (from64 (false, root) (other ++ target), from64 (true, root) (other ++ target)) =
      (nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initialSecond false other,
        nativeKernel (RawCtxFreshChainCut.concreteChain target) <$> initialSecond true other) := by
  rw [from64_second, from64_second]

end BeaconcryptCore.Computational.RawCtxSelectedInitialSecond

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.split64_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.split64_second
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.from64_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.from64_second
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.second_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.second_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.second_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.second_observed
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.full_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.full_second
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.source_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.source_second
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.uniform_native_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.uniform_native_second
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.delayed_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.delayed_second
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.original_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.original_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.delayed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.delayed_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.paired_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedInitialSecond.paired_roles
