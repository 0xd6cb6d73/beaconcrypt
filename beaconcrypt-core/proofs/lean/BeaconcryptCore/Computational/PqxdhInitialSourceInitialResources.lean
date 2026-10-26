import BeaconcryptCore.Computational.PqxdhInitialSourceFirstResources
import BeaconcryptCore.Computational.PqxdhInitialNativeBudgets

/-!
The initializer reduction observes the actual complete source execution and final publication/freshness event. Its query allowance is derived from the original firstbuilder/post syntax and each original callback, with the real retained initializer's32-byte cache allowance. The primitive reduction pays the preparation, independent32-byte input and all observer work. Support-sensitive accounting avoids requiring impossible resource caps for source inputs that preparation cannot produce.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy
open PqxdhInitialSourceFirstResources (Caps)
open PqxdhInitialNativeBudgets
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

def budget (qPre qApplication qSelector qAux : Nat) : ExternalBudget :=
  ⟨qPre, qApplication, 32, qSelector, qAux⟩

def uniformCap (qPost qPre qApplication qSelector qAux : Nat) : Nat :=
  (7 + qPost * 67) * callbackCap (budget qPre qApplication qSelector qAux)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (qPost qCheck qKnown qPre qApplication qSelector qAux : Nat)

/-- Each original source callback retains its actual random-query cost when the exact supplied initializer response is installed. -/
theorem callbacks (input : Input extra M P I D K X Response A N S B)
    (caps : Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)
    (root : RootOutput) (response : PqxdhInitialRootLabelService.Response) :
    LocalBounds (PqxdhInitialOriginFinishPath.withInitial source input.selectedMessage root response input.other)
      (budget qPre qApplication qSelector qAux) := by
  intro query state cache
  rcases query with query | (reply | (secrets | (query | query)))
  · exact caps.preBound query state cache
  · exact caps.applicationBound reply state cache
  · change (((Prod.snd <$> PqxdhInitialNativeInitializer.initial source input.selectedMessage root response secrets).run state).run cache).IsTotalQueryBound 32
    simp only [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
    exact PqxdhInitialNativeInitializer.initial_uniform source input.selectedMessage root response secrets state cache
  · exact caps.selectorBound query state cache
  · exact caps.auxBound query state cache

/-- The actual complete source publication/freshness bit inherits the original source callback bill, for any supplied response and any chain stage. -/
theorem one_uniform (input : Input extra M P I D K X Response A N S B)
    (caps : Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)
    (root : RootOutput) (response : PqxdhInitialRootLabelService.Response) (stage : Nat) :
    (sourceGame source writer sender route decode input root response stage).IsTotalQueryBound
      (uniformCap qPost qPre qApplication qSelector qAux) := by
  unfold sourceGame PqxdhInitialSourceExperiment.game
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  exact PqxdhInitialNativeBudgets.source_uniform source writer stage
    (PqxdhInitialOriginFinishPath.withInitial source input.selectedMessage root response input.other)
    (budget qPre qApplication qSelector qAux)
    (callbacks source qPost qCheck qKnown qPre qApplication qSelector qAux input caps root response)
    (PqxdhInitialSelectedOrigin.mark source input.selectedMessage) sender route decode
    (PqxdhInitialSourceExperiment.execution response input.index input.metadata { input.ready with root := root } input.post input.before)
    qPost caps.postBound (PqxdhInitialSourceExperiment.initialState
      (PqxdhInitialSourceExperiment.root source root response input.selected) input.shared input.privateState input.cache)

variable (prior : ProbComp (Context extra M P I D K X Response A N S B))
  (caps : ∀ input, Sum.inr input ∈ support prior → Caps input qPost qCheck qKnown qPre qApplication qSelector qAux)

include caps in
/-- Every source context actually supplied by preparation has the same full-source observer cap; completed source branches perform no observer work. -/
theorem observer_uniform (context : Context extra M P I D K X Response A N S B)
    (supported : context ∈ support prior) (output : FullOutput) :
    (observer source writer sender route decode context output).IsTotalQueryBound
      (uniformCap qPost qPre qApplication qSelector qAux) := by
  cases context with
  | inl decision => trivial
  | inr input =>
      exact one_uniform source writer sender route decode qPost qCheck qKnown qPre qApplication qSelector qAux input
        (caps input supported) _ _ 0

include caps in
/-- The exact initializer HMAC reduction asks at most two challenge queries and pays preparation plus the independent32-byte root plus all original source observation work. The proof uses only source contexts reached by its actual sampler. -/
theorem reduction_queries (qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) :
    (fullExpandReduction .ratchet (sampler prior) (observer source writer sender route decode)).IsQueryBoundP
      IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet (sampler prior) (observer source writer sender route decode)).IsQueryBoundP
      IsHmacUniformQuery ((qPrior + 32) + uniformCap qPost qPre qApplication qSelector qAux) := by
  refine ⟨fullExpandReduction_hmac_query_bound _ _ _, ?_⟩
  unfold fullExpandReduction
  apply isQueryBoundP_bind (local_uniform_query_bound (sampler_uniform prior qPrior bounded))
  rintro ⟨context, input⟩ reached
  have sourceReached := mem_support_of_mem_support_liftComp HmacAdversarySpec (sampler prior) (context, input) reached
  simp only [sampler, mem_support_bind_iff, mem_support_pure_iff] at sourceReached
  obtain ⟨context, supported, root, _, same⟩ := sourceReached
  rw [same]
  dsimp only
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [IsHmacUniformQuery]), fun first => ?_⟩
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [IsHmacUniformQuery]), fun second => ?_⟩
  exact local_uniform_query_bound (observer_uniform source writer sender route decode qPost qCheck qKnown qPre qApplication
    qSelector qAux prior caps context supported (joinBlocks first second))

private theorem bind_uniform_support {Value Result : Type} (first : ProbComp Value)
    (next : Value → ProbComp Result) (n m : Nat) (bounded : first.IsTotalQueryBound n)
    (tail : ∀ value ∈ support first, (next value).IsTotalQueryBound m) :
    (first >>= next).IsTotalQueryBound (n + m) := by
  apply (isQueryBoundP_true_iff _ _).mp
  exact isQueryBoundP_bind ((isQueryBoundP_true_iff _ _).mpr bounded)
    (fun value reached => (isQueryBoundP_true_iff _ _).mpr (tail value reached))

private theorem sampled_context (pair : Context extra M P I D K X Response A N S B × Pqxdh.Bytes)
    (reached : pair ∈ support (m := ProbComp) (sampler prior)) : pair.1 ∈ support prior := by
  simp only [sampler, mem_support_bind_iff, mem_support_pure_iff] at reached
  obtain ⟨context, supported, root, _, same⟩ := reached
  rw [same]
  exact supported

include caps in
/-- All four literal primitive challenger games retain the actual preparation and observer work, separately charging the replacement64-byte Extract key and both complete random HMAC blocks. -/
theorem challenger_queries (hmac : HmacSha512) (qPrior : Nat) (bounded : prior.IsTotalQueryBound qPrior) :
    let sample := sampler prior
    let observe := observer source writer sender route decode
    let u := uniformCap qPost qPre qApplication qSelector qAux
    (extractRealGame hmac sample (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((qPrior + 32) + u) ∧
      (extractUniformGame sample (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((qPrior + 32) + (64 + u)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet sample observe)).IsTotalQueryBound (64 + ((qPrior + 32) + u)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet sample observe)).IsTotalQueryBound ((qPrior + 32) + (64 + (64 + u))) := by
  have sampleBound := sampler_uniform prior qPrior bounded
  have observerBound := observer_uniform source writer sender route decode qPost qCheck qKnown qPre qApplication qSelector qAux prior caps
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bind_uniform_support _ _ _ _ sampleBound (fun pair reached => observerBound pair.1 (sampled_context prior pair reached) _)
  · apply bind_uniform_support _ _ _ _ sampleBound
    intro pair reached
    exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      (fun _ => observerBound pair.1 (sampled_context prior pair reached) _)
  · unfold hmacPrfRealGame
    apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
    intro key
    rw [fullExpandReduction_real]
    exact bind_uniform_support _ _ _ _ sampleBound (fun pair reached => observerBound pair.1 (sampled_context prior pair reached) _)
  · rw [fullExpandReduction_random]
    apply bind_uniform_support _ _ _ _ sampleBound
    intro pair reached
    apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
    intro first
    exact isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64)
      (fun _ => observerBound pair.1 (sampled_context prior pair reached) _)

end BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.one_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.one_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.observer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.observer_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.reduction_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceInitialResources.challenger_queries
