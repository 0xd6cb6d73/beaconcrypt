import BeaconcryptCore.Computational.AdaptiveCtxReplayQueryBounds

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary AdaptiveCtxReplayTable AdaptiveCtxHonestCache
open CtxHonestTagSampling CtxComputationalSecurity JointEagerTable

/-- The selected raw slot is actually interpreted before stopping; its failed lookup and complete next state remain in the experiment. -/
noncomputable def stopAtRaw {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ℕ → OracleComp ReceiveSpec (Option Pqxdh.Bytes) :=
  OracleComp.recOn adversary
    (fun _ _ => pure none)
    (fun query _ recurse index =>
      match query with
      | .inl request => do
        let answer ← ReceiveSpec.query (.inl request)
        recurse answer index
      | .inr raw => do
        let answer ← ReceiveSpec.query (.inr raw)
        match index with
        | 0 => pure (some raw)
        | index + 1 => recurse answer index)

@[simp] theorem stopAtRaw_pure {Result : Type} (value : Result) (index : ℕ) :
    stopAtRaw (pure value) index = pure none := rfl

theorem stopAtRaw_primitive {Result : Type} (request : (unifSpec + CtxAdversarySpec).Domain)
    (next : (unifSpec + CtxAdversarySpec).Range request → OracleComp ReceiveSpec Result) (index : ℕ) :
    stopAtRaw (liftM (ReceiveSpec.query (.inl request)) >>= next) index = (do
      let answer ← ReceiveSpec.query (.inl request)
      stopAtRaw (next answer) index) := rfl

theorem stopAtRaw_receive {Result : Type} (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp ReceiveSpec Result) (index : ℕ) :
    stopAtRaw (liftM (ReceiveSpec.query (.inr raw)) >>= next) index = (do
      let answer ← ReceiveSpec.query (.inr raw)
      match index with
      | 0 => pure (some raw)
      | index + 1 => stopAtRaw (next answer) index) := rfl

/-- Stopping adds no request in any explicit resource class, including the selected raw request already charged to the source. -/
theorem stopAtRaw_query_bound {Result : Type} (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (adversary : OracleComp ReceiveSpec Result) {bound : ℕ}
    (bounded : adversary.IsQueryBoundP p bound) (index : ℕ) :
    (stopAtRaw adversary index).IsQueryBoundP p bound := by
  induction adversary using OracleComp.inductionOn generalizing bound index with
  | pure value => simp
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inl request =>
      rw [stopAtRaw_primitive, OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer (bounded.2 answer) index⟩
    | inr raw =>
      rw [stopAtRaw_receive, OracleComp.isQueryBoundP_query_bind_iff]
      refine ⟨bounded.1, ?_⟩
      intro answer
      cases index with
      | zero => exact OracleComp.isQueryBoundP_pure _ _ _
      | succ index => exact ih answer (bounded.2 answer) index

/-- The winning candidate is tested against the actual final persistent cache, not an adversary-visible table. -/
def CachedGuess {Result : Type} {bound : ℕ}
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound)
    (terminal : Result × AdaptiveCtxReceive.ReceiveState) : Prop :=
  ∃ index : Fin bound, ∃ target,
    (selector terminal.1).get index = some target ∧ Eligible terminal.2 target ∧
      terminal.2.ctx.cache.suffixCache (outerSuffix target.nonce target.context target.record.tag) =
        some target.record.commit

/-- Completing missing cells retains every already installed candidate commitment. -/
theorem cachedGuess_implies_completed {Result : Type} {bound : ℕ}
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound)
    (terminal : Result × AdaptiveCtxReceive.ReceiveState) (tail : Suffix → CtxDigest)
    (won : CachedGuess selector terminal) :
    GuessEvent selector (tableExtending (sourceDictionary terminal.2) tail, terminal) := by
  obtain ⟨index, target, selected, eligible, cached⟩ := won
  refine ⟨index, target, selected, eligible, ?_⟩
  simp only [tableExtending, sourceDictionary, typedSuffix, List.Vector.toList, cached, Option.getD_some]

/-- The actual persistent cache's eligible final vector costs the same q/2^512 after joint completion. -/
theorem cachedGuess_bound {Result : Type} {bound : ℕ} (decode : RawDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey) (adversary : OracleComp ReceiveSpec Result)
    (selector : Result → List.Vector (Option CtxUnclaimedAcceptance.Target) bound) :
    Pr{let x ← (simulateQ (replayImpl decode c key) adversary).run initialState}[CachedGuess selector x] ≤
      (bound : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  classical
  have split : ∀ {A B C T : Type} (run : ProbComp (A × B)) (draw : ProbComp T) (dict : B → C)
      (extend : C → T → T) (won : A × B → Prop) (event : T × (A × B) → Prop),
      (∀ terminal, won terminal → ∀ tail ∈ support draw, event (extend (dict terminal.2) tail, terminal)) →
      Pr{let x ← run}[won x] ≤
        Pr{let x ← (run >>= fun terminal => draw >>= fun tail =>
          pure (extend (dict terminal.2) tail, terminal))}[event x] := by
    intro A B C T run draw dict extend won event implied
    rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_bind_eq_tsum]
    refine ENNReal.tsum_le_tsum fun terminal => ?_
    by_cases hit : won terminal
    · have chance : Pr{let x ← (draw >>= fun tail =>
          pure (extend (dict terminal.2) tail, terminal))}[event x] = 1 := by
        rw [bind_pure_comp _ draw, prEvent_map]
        exact OracleComp.prEvent_eq_one_of_forall_mem_support _ _ (implied terminal hit)
      rw [ite_eq_left hit, chance, mul_one]
    · rw [ite_eq_right hit]
      exact zero_le
  have security := completedSource_guess_bound (bound := bound) decode c key adversary selector
  refine le_trans ?_ security
  unfold completedSource
  exact split _ _ sourceDictionary tableExtending (CachedGuess selector) (GuessEvent selector)
    fun terminal won tail _ => cachedGuess_implies_completed selector terminal tail won

/-- One raw stopping position contributes exactly one unchanged decoded candidate; malformed and absent positions remain none. -/
def oneSlot (decode : RawDecoder) (raw : Option Pqxdh.Bytes) :
    List.Vector (Option CtxUnclaimedAcceptance.Target) 1 :=
  List.Vector.ofFn (fun _ => raw.bind decode)

/-- A post-lookup discrepancy is tested against the actual retained cell and public issued-tuple history. -/
def RawBad (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) : Prop :=
  ∃ target, decode raw = some target ∧ Eligible state target ∧
    state.ctx.cache.suffixCache (outerSuffix target.nonce target.context target.record.tag) = some target.record.commit

instance (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) :
    Decidable (RawBad decode raw state) := by
  unfold RawBad
  cases parsed : decode raw with
  | none => exact isFalse (by rintro ⟨target, impossible, _⟩; cases impossible)
  | some target =>
    exact decidable_of_iff (Eligible state target ∧
      state.ctx.cache.suffixCache (outerSuffix target.nonce target.context target.record.tag) = some target.record.commit)
      (by simp)

/-- The one-slot final event is precisely the selected raw request's actual post-lookup discrepancy event. -/
theorem oneSlot_some (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) :
    CachedGuess (oneSlot decode) (some raw, state) ↔ RawBad decode raw state := by
  simp only [CachedGuess, oneSlot, List.Vector.get_ofFn, Option.bind_some, RawBad]
  exact ⟨fun ⟨_, target, selected, rest⟩ => ⟨target, selected, rest⟩,
    fun ⟨target, selected, rest⟩ => ⟨0, target, selected, rest⟩⟩

/-- Failure to reach the selected raw position never wins by fallback. -/
theorem oneSlot_none (decode : RawDecoder) (state : AdaptiveCtxReceive.ReceiveState) :
    ¬CachedGuess (oneSlot decode) (none, state) := by
  simp [CachedGuess, oneSlot]

/-- Each stopped source actually executes its selected raw lookup and then makes only one final commitment guess. No qRaw factor appears in this individual bound. -/
theorem stopped_guess_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) (index : ℕ) :
    Pr{let x ← (simulateQ (replayImpl decode c key) (stopAtRaw adversary index)).run initialState}[CachedGuess (oneSlot decode) x] ≤
        (1 : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  simpa only [Nat.cast_one] using cachedGuess_bound decode c key (stopAtRaw adversary index) (oneSlot decode)

/-- The challenger-only monitor follows exact replay-only replies and cache updates until the first post-lookup discrepancy. -/
noncomputable def firstDiscrepancy {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) :
    AdaptiveCtxReceive.ReceiveState → ProbComp Bool :=
  OracleComp.recOn adversary
    (fun _ _ => pure false)
    (fun query _ recurse state => match query with
      | .inl request => do
        let result ← (replayImpl decode c key (.inl request)).run state
        recurse result.1 result.2
      | .inr raw => do
        let result ← replayRaw decode raw state
        if RawBad decode raw result.2 then pure true
        else recurse result.1 result.2)

@[simp] theorem firstDiscrepancy_pure {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (value : Result) (state : AdaptiveCtxReceive.ReceiveState) :
    firstDiscrepancy decode c key (pure value) state = pure false := rfl

theorem firstDiscrepancy_primitive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (request : (unifSpec + CtxAdversarySpec).Domain)
    (next : (unifSpec + CtxAdversarySpec).Range request → OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) :
    firstDiscrepancy decode c key (liftM (ReceiveSpec.query (.inl request)) >>= next) state = (do
      let result ← (replayImpl decode c key (.inl request)).run state
      firstDiscrepancy decode c key (next result.1) result.2) := rfl

theorem firstDiscrepancy_receive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (next : Option Pqxdh.Bytes → OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxReceive.ReceiveState) :
    firstDiscrepancy decode c key (liftM (ReceiveSpec.query (.inr raw)) >>= next) state = (do
      let result ← replayRaw decode raw state
      if RawBad decode raw result.2 then pure true
      else firstDiscrepancy decode c key (next result.1) result.2) := rfl

/-- The selected experiment retains the full source poststate after the selected raw request, with no later continuation. -/
noncomputable def indexedGame {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) (index : ℕ)
    (state : AdaptiveCtxReceive.ReceiveState) : ProbComp (Option Pqxdh.Bytes × AdaptiveCtxReceive.ReceiveState) :=
  (simulateQ (replayImpl decode c key) (stopAtRaw adversary index)).run state

theorem indexedGame_primitive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (request : (unifSpec + CtxAdversarySpec).Domain)
    (next : (unifSpec + CtxAdversarySpec).Range request → OracleComp ReceiveSpec Result)
    (index : ℕ) (state : AdaptiveCtxReceive.ReceiveState) :
    indexedGame decode c key (liftM (ReceiveSpec.query (.inl request)) >>= next) index state = (do
      let result ← (replayImpl decode c key (.inl request)).run state
      indexedGame decode c key (next result.1) index result.2) := by
  simp only [indexedGame, stopAtRaw_primitive, simulateQ_query_bind, StateT.run_bind,
    OracleQuery.input_query]
  rfl

theorem indexedGame_receive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (next : Option Pqxdh.Bytes → OracleComp ReceiveSpec Result)
    (index : ℕ) (state : AdaptiveCtxReceive.ReceiveState) :
    indexedGame decode c key (liftM (ReceiveSpec.query (.inr raw)) >>= next) index state = (do
      let result ← replayRaw decode raw state
      match index with
      | 0 => pure (some raw, result.2)
      | index + 1 => indexedGame decode c key (next result.1) index result.2) := by
  simp only [indexedGame, stopAtRaw_receive, simulateQ_query_bind, StateT.run_bind, OracleQuery.input_query]
  apply bind_congr
  intro result
  cases index <;> simp [simulateQ_pure, StateT.run_pure]

/-- Each possible first discrepancy is charged once to its own stopped raw slot, including malformed and repeated attempts. -/
theorem firstDiscrepancy_le_indexed_sum {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (state : AdaptiveCtxReceive.ReceiveState)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery count) :
    Pr{let bad ← firstDiscrepancy decode c key adversary state}[bad = true] ≤
      ∑ index ∈ Finset.range count,
        Pr{let x ← indexedGame decode c key adversary index state}[CachedGuess (oneSlot decode) x] := by
  classical
  induction adversary using OracleComp.inductionOn generalizing count state with
  | pure value =>
    rw [firstDiscrepancy_pure, prEvent_pure]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_le]
  | query_bind query next ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    cases query with
    | inr raw =>
      have positive : 0 < count := by simpa [AdaptiveCtxReceive.IsRawQuery] using bounded.1
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
      rw [firstDiscrepancy_receive]
      simp_rw [indexedGame_receive]
      apply AdaptiveRawNonceAead.probEvent_bind_le_sum
      intro result supported
      by_cases bad : RawBad decode raw result.2
      · rw [ite_eq_left bad]
        have current : Pr{let x ← (pure (some raw, result.2) : ProbComp _)}[CachedGuess (oneSlot decode) x] = 1 := by
          simp only [prEvent_pure, oneSlot_some, bad, ite_true]
        calc
          Pr{let flag ← (pure true : ProbComp Bool)}[flag = true] = 1 := by
            rw [prEvent_pure]
            simp
          _ = Pr{let x ← (pure (some raw, result.2) : ProbComp _)}[CachedGuess (oneSlot decode) x] := current.symm
          _ ≤ _ := by
            rw [Finset.sum_range_succ']
            exact le_add_of_nonneg_left zero_le
      · rw [ite_eq_right bad]
        have restBound : (next result.1).IsQueryBoundP AdaptiveCtxReceive.IsRawQuery remaining := by
          simpa only [ite_eq_left (show AdaptiveCtxReceive.IsRawQuery (.inr raw) from trivial),
            Nat.succ_sub_one] using bounded.2 result.1
        have tail := ih result.1 remaining result.2 restBound
        rw [Finset.sum_range_succ']
        exact tail.trans (le_add_of_nonneg_right zero_le)
    | inl request =>
      rw [firstDiscrepancy_primitive]
      simp_rw [indexedGame_primitive]
      apply AdaptiveRawNonceAead.probEvent_bind_le_sum
      intro result supported
      exact ih result.1 count result.2
        (by simpa only [ite_eq_right (show ¬AdaptiveCtxReceive.IsRawQuery (.inl request) from id)] using
          bounded.2 result.1)

/-- The first persistent-cache alias discrepancy costs qRaw/2^512, with exactly one selected guess per counted raw position. -/
theorem firstDiscrepancy_bound {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp ReceiveSpec Result) (qRaw : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw) :
    Pr{let bad ← firstDiscrepancy decode c key adversary initialState}[bad = true] ≤
      (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  have indexed := firstDiscrepancy_le_indexed_sum decode c key adversary qRaw initialState bounded
  refine indexed.trans ((Finset.sum_le_sum fun index _ => stopped_guess_bound decode c key adversary index).trans_eq ?_)
  simp only [div_eq_mul_inv, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.stopAtRaw_query_bound' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.stopAtRaw_query_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.cachedGuess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.cachedGuess_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.stopped_guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.stopped_guess_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.firstDiscrepancy_le_indexed_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.firstDiscrepancy_le_indexed_sum

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.firstDiscrepancy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxStoppedRaw.firstDiscrepancy_bound
