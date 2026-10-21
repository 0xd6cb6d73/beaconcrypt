import BeaconcryptCore.Computational.PqxdhInitialChainComposition

/-!
# Bounded adaptive observation of a private source chain

The exact source material loop and a finite material tape give the same complete client result and derivation count, with caller randomness forwarded in order. The checked observer lifts the existing ordered Extract/HMAC sum to adaptive stopping. Uniform initial-chain independence, absence of chain-reveal capabilities, all sampling budgets, and local deterministic source work are explicit; actual root, consuming ratchet, native adapter and global composition remain separate.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids

abbrev NextSpec : OracleSpec Unit := fun _ => Material
abbrev ChainSpec := unifSpec + NextSpec

def IsNext : ChainSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsNext := fun query => match query with
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

structure SourceState where
  chain : RootOutput
  requests : Nat

structure TapeState where
  remaining : List Material
  requests : Nat

/-- The private source capability runs the same full 76-byte derivation on every request. -/
def sourceImpl (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl ChainSpec (StateT SourceState ProbComp) := fun query state =>
  match query with
  | .inl coin => do
      let value ← unifSpec.query coin
      pure (value, state)
  | .inr _ =>
      let output := PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address state.chain.toList)
      pure (material output, ⟨nextChain output, state.requests + 1⟩)

/-- The arbitrary fallback is unreachable for a client within the checked remaining-request budget. -/
def tapeImpl (fallback : Material) : QueryImpl ChainSpec (StateT TapeState ProbComp) :=
  fun query state => match query with
  | .inl coin => do
      let value ← unifSpec.query coin
      pure (value, state)
  | .inr _ => match state.remaining with
      | [] => pure (fallback, ⟨[], state.requests + 1⟩)
      | head :: tail => pure (head, ⟨tail, state.requests + 1⟩)

/-- The returned result and number of actual derivations are the observable capability output. -/
def sourceView {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp ChainSpec Result) (state : SourceState) : ProbComp (Result × Nat) :=
  (fun result => (result.1, result.2.requests)) <$> (simulateQ (sourceImpl source) client).run state

def tapeView {Result : Type} (fallback : Material)
    (client : OracleComp ChainSpec Result) (state : TapeState) : ProbComp (Result × Nat) :=
  (fun result => (result.1, result.2.requests)) <$> (simulateQ (tapeImpl fallback) client).run state

/-- Every adaptive continuation sees the exact source material sequence; only private intermediate chains are projected. -/
theorem sourceView_tapeView {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (client : OracleComp ChainSpec Result) (budget : Nat)
    (bound : IsQueryBoundP client IsNext budget) (chain : RootOutput) (requests : Nat) :
    sourceView source client ⟨chain, requests⟩ =
      tapeView fallback client ⟨(realEvolution source budget chain).records, requests⟩ := by
  induction client using OracleComp.inductionOn generalizing budget chain requests with
  | pure value => simp [sourceView, tapeView]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    cases query with
    | inl coin =>
      unfold sourceView tapeView
      rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      simp only [simulateQ_spec_query, sourceImpl, StateT.run, bind_assoc, pure_bind, map_bind, tapeImpl]
      apply congrArg
      funext value
      apply ih value budget
      simpa [IsNext] using bound.2 value
    | inr request =>
      have positive : 0 < budget := (or_iff_right (by simp [IsNext])).mp bound.1
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      apply ih
      convert bound.2 (material (PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address chain.toList))) using 1
      · change next (id _) = next _
        rfl
      · simp [IsNext]

/-- The finite-history observer executes the original adaptive client and its complete final observation. -/
def tapeObserver {Context Result : Type} (fallback : Material)
    (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) : EvolutionObserver Context :=
  fun context evolution => do
    let result ← tapeView fallback (client context) ⟨evolution.records, 0⟩
    finish context result

/-- One private uniform initial chain feeds the actual adaptive source capability. -/
noncomputable def sourceGame {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) : ProbComp Bool := do
  let context ← sample
  let chain ← $ᵗ RootOutput
  let result ← sourceView source (client context) ⟨chain, 0⟩
  finish context result

/-- A finite random material tape is an efficient comparison experiment; all reserved material is sampled and charged. -/
noncomputable def eagerGame {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (budget : Nat) : ProbComp Bool := do
  let context ← sample
  let records ← sampleMaterials budget
  let result ← tapeView fallback (client context) ⟨records, 0⟩
  finish context result

/-- Full adaptive source behavior is exactly the initial finite-history hybrid under its checked observer. -/
theorem sourceGame_eq_hybrid {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (budget : Nat)
    (bound : ∀ context, IsQueryBoundP (client context) IsNext budget) :
    sourceGame source sample client finish =
      hybrid source sample (tapeObserver fallback client finish) budget 0 := by
  unfold sourceGame hybrid
  simp only [sampleMaterials, Nat.sub_zero, List.nil_append, pure_bind]
  apply bind_congr
  intro context
  apply bind_congr
  intro chain
  rw [sourceView_tapeView source fallback (client context) budget (bound context)]
  rfl

/-- The final unused live chain is removed only by its independent lossless distribution. -/
theorem final_hybrid_eq_eager {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (budget : Nat) :
    EvalDistEq (hybrid source sample (tapeObserver fallback client finish) budget budget)
      (eagerGame fallback sample client finish budget) := by
  simp only [hybrid, eagerGame, tapeObserver, Nat.sub_self, realEvolution, List.append_nil]
  refine EvalDistEq.bind_right sample (fun context => ?_)
  refine EvalDistEq.bind_right (sampleMaterials budget) (fun records => ?_)
  exact OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) _

/-- Adaptive stopping incurs no selection loss: the same budget-many ordered Extract/HMAC reductions apply. -/
theorem adaptive_advantage_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (budget : Nat)
    (bound : ∀ context, IsQueryBoundP (client context) IsNext budget) :
    (sourceGame source sample client finish).boolDistAdvantage
      (eagerGame fallback sample client finish budget) ≤
      ∑ cut ∈ Finset.range budget,
        hopLoss source hmac sample (tapeObserver fallback client finish) cut (budget - cut - 1) := by
  have random := (final_hybrid_eq_eager source fallback sample client finish budget).evalDist_eq
  simpa only [sourceGame_eq_hybrid source fallback sample client finish budget bound,
    ProbComp.boolDistAdvantage, random] using
      ordered_chain_bound source hmac correct sample (tapeObserver fallback client finish) budget

abbrev IsCoin (query : ChainSpec.Domain) : Prop := ¬ IsNext query

/-- Actual source execution forwards exactly the caller's explicit uniform requests; derivation is local source work. -/
theorem sourceRun_uniform_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp ChainSpec Result) (state : SourceState) (coins : Nat)
    (bound : IsQueryBoundP client IsCoin coins) :
    IsTotalQueryBound ((simulateQ (sourceImpl source) client).run state) coins := by
  have forwarded : IsQueryBoundP ((simulateQ (sourceImpl source) client).run state) (fun _ => True) coins := by
    apply IsQueryBoundP.simulateQ_run_StateT_of_step bound
    intro query state
    cases query <;> simp [sourceImpl, StateT.run, IsCoin, IsNext]
  simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using forwarded

/-- Tape lookup makes no hidden randomness request, including its unreachable exhausted branch. -/
theorem tapeRun_uniform_bound {Result : Type} (fallback : Material)
    (client : OracleComp ChainSpec Result) (state : TapeState) (coins : Nat)
    (bound : IsQueryBoundP client IsCoin coins) :
    IsTotalQueryBound ((simulateQ (tapeImpl fallback) client).run state) coins := by
  have forwarded : IsQueryBoundP ((simulateQ (tapeImpl fallback) client).run state) (fun _ => True) coins := by
    apply IsQueryBoundP.simulateQ_run_StateT_of_step bound
    intro query state
    cases query with
    | inl coin => simp [tapeImpl, StateT.run, IsCoin, IsNext]
    | inr request => cases entries : state.remaining <;> simp [tapeImpl, StateT.run, IsCoin, IsNext, entries]
  simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using forwarded

/-- Complete observer accounting includes all adaptive client coins and every possible final observation. -/
theorem tapeObserver_uniform_bound {Context Result : Type} (fallback : Material)
    (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (coins after : Nat)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after)
    (context : Context) (evolution : Evolution) :
    IsTotalQueryBound (tapeObserver fallback client finish context evolution) (coins + after) := by
  apply isTotalQueryBound_bind
  · rw [tapeView, IsTotalQueryBound, isQueryBound_map_iff]
    exact tapeRun_uniform_bound fallback (client context) _ coins (clientBound context)
  · exact finishBound context

/-- One source derivation increments the retained count exactly once; caller coins leave it unchanged. -/
theorem sourceImpl_requests (source : FixedHkdfSha512NoSaltSource)
    (query : ChainSpec.Domain) (state : SourceState)
    (result : ChainSpec.Range query × SourceState)
    (supported : result ∈ support ((sourceImpl source query).run state)) :
    result.2.requests = state.requests + if IsNext query then 1 else 0 := by
  cases query with
  | inl coin =>
    simp only [sourceImpl, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨value, _, rfl⟩ := supported
    simp [IsNext]
  | inr request =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    simp [IsNext]

/-- Every supported adaptive source result charges its actual derivations, including the final requested step before stopping. -/
theorem sourceRun_requests_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp ChainSpec Result) (budget : Nat)
    (bound : IsQueryBoundP client IsNext budget) (state : SourceState)
    (result : Result × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl source) client).run state)) :
    result.2.requests ≤ state.requests + budget := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    simp
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
    obtain ⟨reply, actual, rest⟩ := supported
    have step := sourceImpl_requests source query state reply actual
    have tail := ih reply.1 (if IsNext query then budget - 1 else budget)
      (bound.2 reply.1) reply.2 rest
    by_cases advances : IsNext query
    · have positive := bound.1.resolve_left (not_not.mpr advances)
      simp only [advances, ite_true] at step tail
      omega
    · simp only [advances, ite_false, Nat.add_zero] at step tail
      omega

/-- The real adaptive game charges its context, one initial chain, client coins and complete final observation. -/
theorem sourceGame_uniform_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    IsTotalQueryBound (sourceGame source sample client finish) (qSample + (32 + (coins + after))) := by
  apply isTotalQueryBound_bind sampleBound
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro chain
  apply isTotalQueryBound_bind
  · rw [sourceView, IsTotalQueryBound, isQueryBound_map_iff]
    exact sourceRun_uniform_bound source (client context) _ coins (clientBound context)
  · exact finishBound context

/-- The comparison charges every one of its finite reserved material draws, including an unused suffix after early stopping. -/
theorem eagerGame_uniform_bound {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (budget qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    IsTotalQueryBound (eagerGame fallback sample client finish budget)
      (qSample + (44 * budget + (coins + after))) := by
  apply isTotalQueryBound_bind sampleBound
  intro context
  apply isTotalQueryBound_bind (sampleMaterials_query_bound budget)
  intro records
  apply isTotalQueryBound_bind
  · rw [tapeView, IsTotalQueryBound, isQueryBound_map_iff]
    exact tapeRun_uniform_bound fallback (client context) _ coins (clientBound context)
  · exact finishBound context

/-- Each concrete adaptive reduction retains all client and final-observer work, with two HMAC challenge queries. -/
theorem adaptiveReduction_query_bounds {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (cut remaining qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    let reduction := PqxdhFullSecretInputKdf.fullExpandReduction .ratchet (hopSampler sample cut)
      (hopObserver source (tapeObserver fallback client finish) remaining)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery ((qSample + (44 * cut + 32)) + (coins + after)) := by
  exact hopReduction_query_bounds source sample (tapeObserver fallback client finish) cut remaining
    sampleBound (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound)

/-- All five endpoint worlds retain the actual adaptive observer budget and all hidden sampler/block draws. -/
theorem adaptiveChallenger_query_bounds {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (fallback : Material) (sample : ProbComp Context)
    (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × Nat → ProbComp Bool) (cut remaining qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    let joint := hopSampler sample cut
    let observe := hopObserver source (tapeObserver fallback client finish) remaining
    let qJoint := qSample + (44 * cut + 32)
    let qObserver := coins + after
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      (qJoint + qObserver) ∧
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      (qJoint + (64 + qObserver)) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (64 + (qJoint + qObserver)) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (qJoint + (64 + (64 + qObserver))) ∧
    (independentFullGame joint observe).IsTotalQueryBound (qJoint + (76 + qObserver)) := by
  exact PqxdhInitialChainComposition.hopChallenger_query_bounds source hmac sample
    (tapeObserver fallback client finish) cut remaining qSample (coins + after) sampleBound
    (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound)

end BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceView_tapeView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceView_tapeView

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceGame_eq_hybrid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceGame_eq_hybrid

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.final_hybrid_eq_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.final_hybrid_eq_eager

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.adaptive_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.adaptive_advantage_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.tapeRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.tapeRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.tapeObserver_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.tapeObserver_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceImpl_requests' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceImpl_requests

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceRun_requests_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceRun_requests_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.sourceGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.eagerGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.eagerGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.adaptiveReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.adaptiveReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.adaptiveChallenger_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation.adaptiveChallenger_query_bounds
