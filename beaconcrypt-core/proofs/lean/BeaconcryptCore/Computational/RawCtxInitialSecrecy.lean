import BeaconcryptCore.Computational.RawCtxSelectedInitialSecond
import BeaconcryptCore.Computational.PqxdhInitialBuilderCut

/-!
One exact root/context sampler feeds the actual paired64 source initializer. The two role constructors consume the same64 bytes and preserve opposite directions, zero counters, empty cache and the complete RustM result. The primitive observer receives the earlier context and the paired initializer results only after expansion; neither the root nor an initial half is added to its pre-Extract context. Public operations inside the observer remain the same real code.

The reduction reuses the checked full76 endpoint through an explicit prefix-only comparison observer. That comparison pays two HMAC challenge calls and its own full76/random-block draws. The actual randomized initializer draws only64 bytes, charged separately. These are conditional ordinary-game reductions at the displayed exact joint sampler; the authenticated-root composition and source family must instantiate that sampler and observer.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedInitialConstructor

abbrev Pair := RustM ConcreteRatchetKernel × RustM ConcreteRatchetKernel
abbrev Sampler (Context : Type) := ProbComp (Context × RootOutput)
abbrev Observer (Context : Type) := Context → Pair → ProbComp Bool

def rootBytes (root : RootOutput) : Std.Array Std.U8 32#usize :=
  (RawCtxFreshChainCut.concreteChain root).bytes

def pair64 (output : HmacBlock) : Pair :=
  (from64 (false, rootBytes (List.Vector.replicate 32 0)) output,
    from64 (true, rootBytes (List.Vector.replicate 32 0)) output)

/-- The source's completed initializer depends on the role and response, not the consumed pending root field. -/
theorem root_field_unused (role : Bool) (left right : Std.Array Std.U8 32#usize) (output : HmacBlock) :
    from64 (role, left) output = from64 (role, right) output := by
  rw [← split_reconstruct output, from64_initial, from64_initial]

/-- The registration builder and paired source initializer consume the same exact64-byte response. -/
theorem root_initializer (source : FixedHkdfSha512NoSaltSource) (role : Bool) (root : RootOutput) :
    PqxdhRootTableInitialization.initialKernelRun source role root =
      RawCtxInitializedKdfFamily.initialReply source (role, rootBytes root) := by
  rfl

/-- Serialization supplies exactly the original32-byte root and shared ratchet domain to initialization. -/
theorem root_address (root : RootOutput) :
    RawCtxKdfRequestTable.address ⟨rootBytes root, ratchet.SYM_RATCHET_INFO⟩ =
      FixedHkdfDomain.ratchet.address root.toList := by
  simp [RawCtxKdfRequestTable.address, rootBytes, RawCtxFreshChainCut.concreteChain,
    PqxdhRefinement.absBytes, List.map_map, Function.comp_def, FixedHkdfDomain.address, FixedHkdfDomain.info]
  exact PqxdhInitialRatchetComplementarity.absBytes_ratchetSymmetricInfo

/-- Both actual source roles consume one shared64 prefix and can be constructed without retaining the consumed root field. -/
theorem source_pair (source : FixedHkdfSha512NoSaltSource) (root : RootOutput) :
    (PqxdhRootTableInitialization.initialKernelRun source false root,
      PqxdhRootTableInitialization.initialKernelRun source true root) =
      pair64 (initialPrefix (productionStream source.crypto (FixedHkdfDomain.ratchet.address root.toList))) := by
  simp only [root_initializer, ← RawCtxInitializedKdfFamily.initial_projection, ← full_prefix, root_address, pair64]
  exact congrArg₂ Prod.mk (root_field_unused false _ _ _) (root_field_unused true _ _ _)

def joint {Context : Type} (sample : Sampler Context) : SecretInputSampler Context :=
  ((fun pair : Context × RootOutput => (pair.1, pair.2.toList)) <$> sample : ProbComp (Context × Pqxdh.Bytes))

noncomputable def actual {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : Sampler Context) (observe : Observer Context) : ProbComp Bool := do
  let (context, root) ← sample
  observe context (PqxdhRootTableInitialization.initialKernelRun source false root,
    PqxdhRootTableInitialization.initialKernelRun source true root)

noncomputable def random {Context : Type} (sample : Sampler Context) (observe : Observer Context) : ProbComp Bool := do
  let (context, _) ← sample
  let output ← $ᵗ HmacBlock
  observe context (pair64 output)

noncomputable def observer {Context : Type} (observe : Observer Context) : FullObserver Context :=
  fun context output => observe context (pair64 (initialPrefix output))

/-- The exact source initializer game is the existing secret-input game on the serialized root and unchanged pre-expansion context. -/
theorem actual_source {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : Sampler Context) (observe : Observer Context) :
    actual source sample observe = sourceFullGame source .ratchet (joint sample) (observer observe) := by
  simp only [actual, sourceFullGame, joint, bind_map_left, observer, source_pair]

/-- The prefix-only full76 comparison has the same evaluated complete observation as the actual64 randomized initializer. -/
theorem random_comparison {Context : Type} (sample : Sampler Context) (observe : Observer Context) :
    𝒟[independentFullGame (joint sample) (observer observe)] = 𝒟[random sample observe] := by
  apply evalDist_eq_of_evalSPMF_eq
  simp only [independentFullGame, joint, bind_map_left, random]
  refine evalSPMF_bind_congr' (m := ProbComp) (sample : ProbComp (Context × RootOutput)) (fun pair => ?_)
  have projected := congrArg (fun distribution : SPMF HmacBlock => distribution >>=
    fun output => evalSPMF (observe pair.1 (pair64 output))) initialPrefix_uniform_vcvioLegacy
  simpa only [← evalSPMF_bind, bind_map_left, observer] using projected

/-- The actual paired64 initializer reduces with coefficient one to fixed-salt Extract on this exact root/context sampler and ordinary HMAC PRF. -/
theorem primitive_bound {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : Sampler Context) (observe : Observer Context) :
    (actual source sample observe).boolDistAdvantage (random sample observe) ≤
      (extractRealGame hmac (joint sample) (fullExtractReduction hmac .ratchet (observer observe))).boolDistAdvantage
        (extractUniformGame (joint sample) (fullExtractReduction hmac .ratchet (observer observe))) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint sample) (observer observe))).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (joint sample) (observer observe))) := by
  simpa only [← actual_source, ProbComp.boolDistAdvantage, random_comparison sample observe] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet (joint sample) (observer observe)

/-- Serializing the root into the exact Extract sampler retains every earlier uniform query without adding a draw. -/
theorem joint_bound {Context : Type} (sample : Sampler Context) (budget : Nat)
    (bounded : sample.IsTotalQueryBound budget) : (joint sample).IsTotalQueryBound budget := by
  simpa only [joint, IsTotalQueryBound, isQueryBound_map_iff] using bounded

/-- The existing full-output comparison reduction pays two HMAC challenge queries and the entire root sampler and original continuation. -/
theorem reduction_bounds {Context : Type} (sample : Sampler Context) (observe : Observer Context)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context pair, (observe context pair).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet (joint sample) (observer observe)).IsQueryBoundP IsHmacChallengeQuery 2 ∧
      (fullExpandReduction .ratchet (joint sample) (observer observe)).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery (qSample + qObserve) := by
  exact ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (joint_bound sample qSample sampleBound)
      (fun context output => observeBound context _)⟩

/-- The actual fixed initializer adds no uniform draw; all sampler and continuation sampling remains charged. -/
theorem actual_uniform {Context : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : Sampler Context) (observe : Observer Context) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context pair, (observe context pair).IsTotalQueryBound qObserve) :
    (actual source sample observe).IsTotalQueryBound (qSample + qObserve) := by
  exact isTotalQueryBound_bind sampleBound fun pair => observeBound pair.1 _

set_option maxRecDepth 2048 in
/-- The actual randomized initializer separately pays its one64-byte draw, including a challenge discarded by later rejection. -/
theorem random_uniform {Context : Type} (sample : Sampler Context) (observe : Observer Context)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context pair, (observe context pair).IsTotalQueryBound qObserve) :
    (random sample observe).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  exact isTotalQueryBound_bind sampleBound fun pair =>
    isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      fun output => observeBound pair.1 _

set_option maxRecDepth 2048 in
/-- Every endpoint of the full76 comparison is billed separately; none of its extra random bytes is assigned to the actual64 source execution. -/
theorem challenger_uniform {Context : Type} (hmac : HmacSha512)
    (sample : Sampler Context) (observe : Observer Context) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context pair, (observe context pair).IsTotalQueryBound qObserve) :
    (extractRealGame hmac (joint sample) (fullExtractReduction hmac .ratchet (observer observe))).IsTotalQueryBound
        (qSample + qObserve) ∧
      (extractUniformGame (joint sample) (fullExtractReduction hmac .ratchet (observer observe))).IsTotalQueryBound
        (qSample + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (joint sample) (observer observe))).IsTotalQueryBound
        (64 + (qSample + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet (joint sample) (observer observe))).IsTotalQueryBound
        (qSample + (64 + (64 + qObserve))) ∧
      (independentFullGame (joint sample) (observer observe)).IsTotalQueryBound
        (qSample + (76 + qObserve)) := by
  exact ⟨isTotalQueryBound_bind (joint_bound sample qSample sampleBound) (fun pair => observeBound pair.1 _),
    fullExtractUniform_uniform_query_bound _ _ _ _ (joint_bound sample qSample sampleBound) (fun context output => observeBound context _),
    fullHmacReal_uniform_query_bound _ _ _ _ (joint_bound sample qSample sampleBound) (fun context output => observeBound context _),
    fullHmacRandom_uniform_query_bound _ _ _ (joint_bound sample qSample sampleBound) (fun context output => observeBound context _),
    independentFullGame_uniform_query_bound _ _ (joint_bound sample qSample sampleBound) (fun context output => observeBound context _)⟩

end BeaconcryptCore.Computational.RawCtxInitialSecrecy

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.root_field_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.root_field_unused
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.root_initializer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.root_initializer
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.root_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.root_address
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.source_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.source_pair
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.actual_source
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.random_comparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.random_comparison
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.primitive_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.joint_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.joint_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.reduction_bounds
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.actual_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.actual_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.random_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.random_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSecrecy.challenger_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSecrecy.challenger_uniform
