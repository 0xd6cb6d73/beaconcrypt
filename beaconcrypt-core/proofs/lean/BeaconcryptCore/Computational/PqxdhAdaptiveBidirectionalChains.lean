import BeaconcryptCore.Computational.PqxdhAdaptiveChainObservation

/-!
# Adaptive joint observation after actual source initialization

One independent uniform root feeds the actual shared 64-byte source initialization.
Two private next-material capabilities then retain arbitrary adaptive directional
interleaving, caller randomness, complete results and both actual request counters.
The same initial Extract/HMAC pair and both ordered sums compare this execution with
two independent finite material tapes. Current/intermediate-chain reveals, actual
root generation, native ratchet consumption, aliases and global composition remain
separate. Deterministic source KDF calls and list/byte operations remain local work.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhOrderedChainHybrids PqxdhInitialChainComposition

/-- False selects the first source half; true selects the second. -/
abbrev NextSpec : OracleSpec Bool := fun _ => Material
abbrev ChainSpec := unifSpec + NextSpec

def IsDirection (selected : Bool) : ChainSpec.Domain → Prop
  | .inl _ => False
  | .inr direction => direction = selected

instance (selected : Bool) : DecidablePred (IsDirection selected) := fun query =>
  match query with
  | .inl _ => isFalse id
  | .inr direction => inferInstanceAs (Decidable (direction = selected))

structure SourceState where
  chains : RootOutput × RootOutput
  requests : Nat × Nat

structure TapeState where
  remaining : List Material × List Material
  requests : Nat × Nat

def sourceImpl (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl ChainSpec (StateT SourceState ProbComp) := fun query state =>
  match query with
  | .inl coin => do
      let value ← unifSpec.query coin
      pure (value, state)
  | .inr false =>
      let output := PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address state.chains.1.toList)
      pure (material output, ⟨(nextChain output, state.chains.2),
        (state.requests.1 + 1, state.requests.2)⟩)
  | .inr true =>
      let output := PqxdhJointKdf.productionStream source.crypto
        (FixedHkdfDomain.ratchet.address state.chains.2.toList)
      pure (material output, ⟨(state.chains.1, nextChain output),
        (state.requests.1, state.requests.2 + 1)⟩)

def tapeImpl (fallback : Material) : QueryImpl ChainSpec (StateT TapeState ProbComp) :=
  fun query state => match query with
  | .inl coin => do
      let value ← unifSpec.query coin
      pure (value, state)
  | .inr false => match state.remaining.1 with
      | [] => pure (fallback, ⟨([], state.remaining.2), (state.requests.1 + 1, state.requests.2)⟩)
      | head :: tail => pure (head, ⟨(tail, state.remaining.2), (state.requests.1 + 1, state.requests.2)⟩)
  | .inr true => match state.remaining.2 with
      | [] => pure (fallback, ⟨(state.remaining.1, []), (state.requests.1, state.requests.2 + 1)⟩)
      | head :: tail => pure (head, ⟨(state.remaining.1, tail), (state.requests.1, state.requests.2 + 1)⟩)

def sourceView {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp ChainSpec Result) (state : SourceState) : ProbComp (Result × (Nat × Nat)) :=
  (fun result => (result.1, result.2.requests)) <$> (simulateQ (sourceImpl source) client).run state

def tapeView {Result : Type} (fallback : Material)
    (client : OracleComp ChainSpec Result) (state : TapeState) : ProbComp (Result × (Nat × Nat)) :=
  (fun result => (result.1, result.2.requests)) <$> (simulateQ (tapeImpl fallback) client).run state

/-- Both complete source directions remain in one adaptive observation, including cross-direction choices and early stopping. -/
theorem sourceView_tapeView {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (client : OracleComp ChainSpec Result) (left right : Nat)
    (leftBound : IsQueryBoundP client (IsDirection false) left)
    (rightBound : IsQueryBoundP client (IsDirection true) right)
    (chains : RootOutput × RootOutput) (requests : Nat × Nat) :
    sourceView source client ⟨chains, requests⟩ =
      tapeView fallback client ⟨((realEvolution source left chains.1).records,
        (realEvolution source right chains.2).records), requests⟩ := by
  induction client using OracleComp.inductionOn generalizing left right chains requests with
  | pure value => simp [sourceView, tapeView]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at leftBound rightBound
    cases query with
    | inl coin =>
      unfold sourceView tapeView
      rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      simp only [simulateQ_spec_query, sourceImpl, StateT.run, bind_assoc, pure_bind, map_bind, tapeImpl]
      apply congrArg
      funext value
      apply ih value left right
      · simpa [IsDirection] using leftBound.2 value
      · simpa [IsDirection] using rightBound.2 value
    | inr direction =>
      cases direction with
      | false =>
        have positive : 0 < left := (or_iff_right (by simp [IsDirection])).mp leftBound.1
        obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        apply ih
        · convert leftBound.2 (material (PqxdhJointKdf.productionStream source.crypto
            (FixedHkdfDomain.ratchet.address chains.1.toList))) using 1
          · change next (id _) = next _
            rfl
          · simp [IsDirection]
        · convert rightBound.2 (material (PqxdhJointKdf.productionStream source.crypto
            (FixedHkdfDomain.ratchet.address chains.1.toList))) using 1
          · change next (id _) = next _
            rfl
          · simp [IsDirection]
      | true =>
        have positive : 0 < right := (or_iff_right (by simp [IsDirection])).mp rightBound.1
        obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
        apply ih
        · convert leftBound.2 (material (PqxdhJointKdf.productionStream source.crypto
            (FixedHkdfDomain.ratchet.address chains.2.toList))) using 1
          · change next (id _) = next _
            rfl
          · simp [IsDirection]
        · convert rightBound.2 (material (PqxdhJointKdf.productionStream source.crypto
            (FixedHkdfDomain.ratchet.address chains.2.toList))) using 1
          · change next (id _) = next _
            rfl
          · simp [IsDirection]

/-- The two-history observer runs the unchanged interleaving client and its entire final observation. -/
def tapeObserver {Context Result : Type} (fallback : Material)
    (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) : BidirectionalObserver Context :=
  fun context left right => do
    let result ← tapeView fallback (client context) ⟨(left.records, right.records), (0, 0)⟩
    finish context result

/-- The actual single 64-byte source initialization feeds both private directional capabilities. -/
noncomputable def actualGame {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) : ProbComp Bool := do
  let context ← sample
  let root ← $ᵗ RootOutput
  let result ← sourceView source (client context) ⟨sourceInitialChains source root, (0, 0)⟩
  finish context result

/-- The independent finite comparison reserves both full material tapes before the unchanged client. -/
noncomputable def eagerGame {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat) : ProbComp Bool := do
  let context ← sample
  let leftRecords ← sampleMaterials left
  let rightRecords ← sampleMaterials right
  let result ← tapeView fallback (client context) ⟨(leftRecords, rightRecords), (0, 0)⟩
  finish context result

/-- Source initialization and arbitrary directional interleaving have the same complete checked finite-history observer. -/
theorem actualGame_eq_initialized {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat)
    (leftBound : ∀ context, IsQueryBoundP (client context) (IsDirection false) left)
    (rightBound : ∀ context, IsQueryBoundP (client context) (IsDirection true) right) :
    actualGame source sample client finish =
      actualInitializedGame source sample (tapeObserver fallback client finish) left right := by
  unfold actualGame actualInitializedGame
  apply bind_congr
  intro context
  apply bind_congr
  intro root
  rw [sourceView_tapeView source fallback (client context) left right (leftBound context) (rightBound context)]
  rfl

/-- Removing two unused independent live-chain draws retains the whole two-tape continuation. -/
theorem final_bidirectional_eq_eager {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat) :
    𝒟[bidirectionalGame source sample (tapeObserver fallback client finish) left right left right] =
      𝒟[eagerGame fallback sample client finish left right] := by
  apply EvalDistEq.evalDist_eq
  simp only [bidirectionalGame, eagerGame, tapeObserver, sampleEvolution, Nat.sub_self,
    realEvolution, List.append_nil, bind_assoc, pure_bind]
  refine EvalDistEq.bind_right sample (fun context => ?_)
  refine EvalDistEq.bind_right (sampleMaterials left) (fun leftRecords => ?_)
  refine (OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) _).trans ?_
  refine EvalDistEq.bind_right (sampleMaterials right) (fun rightRecords => ?_)
  exact OracleComp.EvalDistEq.bind_const ($ᵗ RootOutput) _

/-- One initial hop and the two ordered directional sums cover arbitrary adaptive interleaving without a scheduling-selection factor. -/
theorem adaptive_initialized_advantage_bound {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (fallback : Material) (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right : Nat)
    (leftBound : ∀ context, IsQueryBoundP (client context) (IsDirection false) left)
    (rightBound : ∀ context, IsQueryBoundP (client context) (IsDirection true) right) :
    let observer := tapeObserver fallback client finish
    (actualGame source sample client finish).boolDistAdvantage
      (eagerGame fallback sample client finish left right) ≤
      initialLoss source hmac sample observer left right +
      ((∑ cut ∈ Finset.range left,
        hopLoss source hmac sample (leftObserver source observer right 0) cut (left - cut - 1)) +
       (∑ cut ∈ Finset.range right,
        hopLoss source hmac (rightContextSampler source sample left left)
          (rightObserver observer) cut (right - cut - 1))) := by
  have random := final_bidirectional_eq_eager source fallback sample client finish left right
  simpa only [actualGame_eq_initialized source fallback sample client finish left right leftBound rightBound,
    ProbComp.boolDistAdvantage, random] using
      actualInitializedGame_evolving_bound source hmac correct sample (tapeObserver fallback client finish) left right

def IsCoin : ChainSpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsCoin := fun query => match query with
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- The whole source interpreter forwards only the client's original uniform requests. -/
theorem sourceRun_uniform_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (client : OracleComp ChainSpec Result) (state : SourceState) (coins : Nat)
    (bound : IsQueryBoundP client IsCoin coins) :
    IsTotalQueryBound ((simulateQ (sourceImpl source) client).run state) coins := by
  have forwarded : IsQueryBoundP ((simulateQ (sourceImpl source) client).run state) (fun _ => True) coins := by
    apply IsQueryBoundP.simulateQ_run_StateT_of_step bound
    intro query state
    cases query with
    | inl coin => simp [sourceImpl, StateT.run, IsCoin]
    | inr direction => cases direction <;> simp [sourceImpl, StateT.run, IsCoin]
  simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using forwarded

/-- Both private tapes retain arbitrary client randomness and perform no additional draw when read. -/
theorem tapeRun_uniform_bound {Result : Type} (fallback : Material)
    (client : OracleComp ChainSpec Result) (state : TapeState) (coins : Nat)
    (bound : IsQueryBoundP client IsCoin coins) :
    IsTotalQueryBound ((simulateQ (tapeImpl fallback) client).run state) coins := by
  have forwarded : IsQueryBoundP ((simulateQ (tapeImpl fallback) client).run state) (fun _ => True) coins := by
    apply IsQueryBoundP.simulateQ_run_StateT_of_step bound
    intro query state
    cases query with
    | inl coin => simp [tapeImpl, StateT.run, IsCoin]
    | inr direction => cases direction with
      | false => cases entries : state.remaining.1 <;> simp [tapeImpl, StateT.run, IsCoin, entries]
      | true => cases entries : state.remaining.2 <;> simp [tapeImpl, StateT.run, IsCoin, entries]
  simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] using forwarded

/-- Every complete finite-history observer retains the entire adaptive client and all final observation work. -/
theorem tapeObserver_uniform_bound {Context Result : Type} (fallback : Material)
    (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (coins after : Nat)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after)
    (context : Context) (left right : Evolution) :
    IsTotalQueryBound (tapeObserver fallback client finish context left right) (coins + after) := by
  apply isTotalQueryBound_bind
  · rw [tapeView, IsTotalQueryBound, isQueryBound_map_iff]
    exact tapeRun_uniform_bound fallback (client context) _ coins (clientBound context)
  · exact finishBound context

/-- The source charges its context, one independent root, all client coins and the complete final observer. -/
theorem actualGame_uniform_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    IsTotalQueryBound (actualGame source sample client finish) (qSample + (32 + (coins + after))) := by
  apply isTotalQueryBound_bind sampleBound
  intro context
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro root
  apply isTotalQueryBound_bind
  · rw [sourceView, IsTotalQueryBound, isQueryBound_map_iff]
    exact sourceRun_uniform_bound source (client context) _ coins (clientBound context)
  · exact finishBound context

/-- Both comparison tapes charge all reserved key/nonce draws, including unused suffixes after adaptive stopping. -/
theorem eagerGame_uniform_bound {Context Result : Type} (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    IsTotalQueryBound (eagerGame fallback sample client finish left right)
      (qSample + (44 * left + (44 * right + (coins + after)))) := by
  apply isTotalQueryBound_bind sampleBound
  intro context
  apply isTotalQueryBound_bind (sampleMaterials_query_bound left)
  intro leftRecords
  apply isTotalQueryBound_bind (sampleMaterials_query_bound right)
  intro rightRecords
  apply isTotalQueryBound_bind
  · rw [tapeView, IsTotalQueryBound, isQueryBound_map_iff]
    exact tapeRun_uniform_bound fallback (client context) _ coins (clientBound context)
  · exact finishBound context

def directionCount (selected : Bool) (requests : Nat × Nat) : Nat :=
  if selected then requests.2 else requests.1

/-- Exactly the requested direction advances once; coins and the opposite direction retain its count. -/
theorem sourceImpl_requests (source : FixedHkdfSha512NoSaltSource) (selected : Bool)
    (query : ChainSpec.Domain) (state : SourceState)
    (result : ChainSpec.Range query × SourceState)
    (supported : result ∈ support ((sourceImpl source query).run state)) :
    directionCount selected result.2.requests = directionCount selected state.requests +
      if IsDirection selected query then 1 else 0 := by
  cases query with
  | inl coin =>
    simp only [sourceImpl, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at supported
    obtain ⟨value, _, rfl⟩ := supported
    simp [IsDirection]
  | inr direction =>
    cases direction <;> obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    all_goals cases selected <;> simp [directionCount, IsDirection]

/-- Every supported complete source execution counts each actual selected derivation, including its final request before stopping. -/
theorem sourceRun_requests_bound {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (selected : Bool) (client : OracleComp ChainSpec Result) (budget : Nat)
    (bound : IsQueryBoundP client (IsDirection selected) budget) (state : SourceState)
    (result : Result × SourceState)
    (supported : result ∈ support ((simulateQ (sourceImpl source) client).run state)) :
    directionCount selected result.2.requests ≤ directionCount selected state.requests + budget := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    simp
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
    obtain ⟨reply, actual, rest⟩ := supported
    have step := sourceImpl_requests source selected query state reply actual
    have tail := ih reply.1 (if IsDirection selected query then budget - 1 else budget)
      (bound.2 reply.1) reply.2 rest
    by_cases advances : IsDirection selected query
    · have positive := bound.1.resolve_left (not_not.mpr advances)
      simp only [advances, ite_true] at step tail
      omega
    · simp only [advances, ite_false, Nat.add_zero] at step tail
      omega

/-- The initial reduction includes the same complete interleaving client after its two challenge calls. -/
theorem adaptiveInitialReduction_query_bounds {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    let reduction := fullExpandReduction .ratchet (rootSampler sample)
      (initialObserver source (tapeObserver fallback client finish) left right)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery ((qSample + 32) + (coins + after)) := by
  exact initialReduction_query_bounds source sample (tapeObserver fallback client finish)
    left right qSample (coins + after) sampleBound
    (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound)

/-- A left-hop reduction retains and charges the unselected real right chain and full adaptive observer. -/
theorem adaptiveLeftReduction_query_bounds {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (right cut remaining qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    let observer := tapeObserver fallback client finish
    let reduction := fullExpandReduction .ratchet (hopSampler sample cut)
      (hopObserver source (leftObserver source observer right 0) remaining)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery
        ((qSample + (44 * cut + 32)) + (32 + (coins + after))) := by
  exact leftHopReduction_query_bounds source sample (tapeObserver fallback client finish)
    right cut remaining qSample (coins + after) sampleBound
    (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound)

/-- A right-hop reduction retains and charges the complete previously idealized left history. -/
theorem adaptiveRightReduction_query_bounds {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left cut remaining qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    let observer := tapeObserver fallback client finish
    let reduction := fullExpandReduction .ratchet
      (hopSampler (rightContextSampler source sample left left) cut)
      (hopObserver source (rightObserver observer) remaining)
    reduction.IsQueryBoundP IsHmacChallengeQuery 2 ∧
      reduction.IsQueryBoundP IsHmacUniformQuery
        (((qSample + (44 * left + 32)) + (44 * cut + 32)) + (coins + after)) := by
  exact rightHopReduction_query_bounds source sample (tapeObserver fallback client finish)
    left cut remaining qSample (coins + after) sampleBound
    (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound)

/-- The five unchanged primitive worlds, recording their full actual sampling costs. -/
def FullWorldBounds {Context : Type} (hmac : HmacSha512) (joint : SecretInputSampler Context)
    (observe : FullObserver Context) (qJoint qObserver : Nat) : Prop :=
  (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      (qJoint + qObserver) ∧
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
      (qJoint + (64 + qObserver)) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (64 + (qJoint + qObserver)) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
      (qJoint + (64 + (64 + qObserver))) ∧
    (independentFullGame joint observe).IsTotalQueryBound (qJoint + (76 + qObserver))

/-- Every initial challenger world retains the sampled root, full adaptive observation and PRK/key/block costs. -/
theorem adaptiveInitialChallenger_query_bounds {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left right qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    FullWorldBounds hmac (rootSampler sample)
      (initialObserver source (tapeObserver fallback client finish) left right)
      (qSample + 32) (coins + after) := by
  exact initialChallenger_query_bounds source hmac sample (tapeObserver fallback client finish)
    left right qSample (coins + after) sampleBound
    (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound)

/-- Each left challenger keeps the opposite real chain in its complete observer, including in every random world. -/
theorem adaptiveLeftChallenger_query_bounds {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (right cut remaining qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    FullWorldBounds hmac (hopSampler sample cut)
      (hopObserver source (leftObserver source (tapeObserver fallback client finish) right 0) remaining)
      (qSample + (44 * cut + 32)) (32 + (coins + after)) := by
  apply hopChallenger_query_bounds source hmac sample
    (leftObserver source (tapeObserver fallback client finish) right 0)
    cut remaining qSample (32 + (coins + after)) sampleBound
  intro context left
  simpa only [Nat.mul_zero, Nat.zero_add] using
    leftObserver_query_bound source (tapeObserver fallback client finish) right 0 (coins + after)
      (tapeObserver_uniform_bound fallback client finish coins after clientBound finishBound) context left

/-- Each right challenger charges the entire left history and all right-prefix, live-chain and block samples. -/
theorem adaptiveRightChallenger_query_bounds {Context Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (fallback : Material)
    (sample : ProbComp Context) (client : Context → OracleComp ChainSpec Result)
    (finish : Context → Result × (Nat × Nat) → ProbComp Bool) (left cut remaining qSample coins after : Nat)
    (sampleBound : IsTotalQueryBound sample qSample)
    (clientBound : ∀ context, IsQueryBoundP (client context) IsCoin coins)
    (finishBound : ∀ context result, IsTotalQueryBound (finish context result) after) :
    FullWorldBounds hmac (hopSampler (rightContextSampler source sample left left) cut)
      (hopObserver source (rightObserver (tapeObserver fallback client finish)) remaining)
      ((qSample + (44 * left + 32)) + (44 * cut + 32)) (coins + after) := by
  exact hopChallenger_query_bounds source hmac (rightContextSampler source sample left left)
    (rightObserver (tapeObserver fallback client finish)) cut remaining
    (qSample + (44 * left + 32)) (coins + after)
    (rightContextSampler_query_bound source sample left left qSample sampleBound)
    (fun context right => tapeObserver_uniform_bound fallback client finish coins after
      clientBound finishBound context.1 context.2 right)

end BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceView_tapeView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceView_tapeView

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.actualGame_eq_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.actualGame_eq_initialized

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.final_bidirectional_eq_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.final_bidirectional_eq_eager

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptive_initialized_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptive_initialized_advantage_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.tapeRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.tapeRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.tapeObserver_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.tapeObserver_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.actualGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.actualGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.eagerGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.eagerGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceImpl_requests' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceImpl_requests

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceRun_requests_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.sourceRun_requests_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveInitialReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveInitialReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveLeftReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveLeftReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveRightReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveRightReduction_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveInitialChallenger_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveInitialChallenger_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveLeftChallenger_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveLeftChallenger_query_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveRightChallenger_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveBidirectionalChains.adaptiveRightChallenger_query_bounds
