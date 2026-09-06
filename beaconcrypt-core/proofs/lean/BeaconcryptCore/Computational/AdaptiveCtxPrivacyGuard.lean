import BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open AdaptiveCtxReceive AdaptiveCtxCanonical AdaptiveCtxIndependent AdaptiveCtxLoggedSource
open AdaptiveCtxReplayDictionary AdaptiveCtxAliasCoupling AdaptiveCtxLogSimulation

abbrev PublicHistory := List CtxSuccessfulSeal

/-- The guard knows only full records returned by successful sealing requests and their original submitted plaintexts. -/
def publicReply (decode : RawDecoder) (history : PublicHistory) (raw : Pqxdh.Bytes) : Option Pqxdh.Bytes :=
  match decode raw with
  | none => none
  | some target => replayPlaintext { emptyCtxIndependentTagState with successfulSeals := history } target

/-- Successful source seals append their actual returned record; rejected requests and all other replies retain the public history. -/
def recordReply (query : ReceiveSpec.Domain) (answer : ReceiveSpec.Range query)
    (history : PublicHistory) : PublicHistory :=
  match query with
  | .inl (.inr (.inr input)) => match answer with
    | none => history
    | some record => ⟨input, record⟩ :: history
  | _ => history

/-- Execute each unchanged source request before returning its reply. Raw responses are replaced only after their actual cache/counter effects, using public full-tuple replay history. -/
def guard (decode : RawDecoder) : QueryImpl ReceiveSpec (StateT PublicHistory (OracleComp ReceiveSpec)) :=
  fun query history => match query with
  | .inl request => do
      let answer ← ReceiveSpec.query (.inl request)
      pure (answer, recordReply (.inl request) answer history)
  | .inr raw => do
      let _ ← ReceiveSpec.query (.inr raw)
      pure (publicReply decode history raw, history)

/-- The public replay guard retains its complete successful history; it receives no hidden record key and never uses the discarded raw reply to choose its returned plaintext. -/
def guardedClient {Result : Type} (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Result) :
    OracleComp ReceiveSpec (Result × PublicHistory) :=
  (simulateQ (guard decode) adversary).run []

/-- Every source slot forwards one identical request, even when the eventual raw reply is discarded. -/
theorem guard_query_bound (decode : RawDecoder) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (query : ReceiveSpec.Domain) (history : PublicHistory) :
    ((guard decode query).run history).IsQueryBoundP p (if p query then 1 else 0) := by
  cases query <;>
    simp only [guard, StateT.run, bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
      OracleComp.isQueryBoundP_query_iff] <;>
    split <;> simp_all

/-- The full public guard preserves any declared source query-class bound, including every raw attempt and rejected sealing request. -/
theorem guardedClient_query_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (p : ReceiveSpec.Domain → Prop) [DecidablePred p]
    (count : ℕ) (bounded : adversary.IsQueryBoundP p count) :
    (guardedClient decode adversary).IsQueryBoundP p count :=
  bounded.simulateQ_run_StateT_of_step (guard_query_bound decode p) []

/-- Discarding only the logged raw reply recovers the exact replay kernel; every actual suffix lookup, counter and failed-query cache effect remains. -/
theorem guardedRaw_eq_replay (decode : RawDecoder) (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState) :
    (fun result => (publicReply decode state.ctx.successfulSeals raw, result.2)) <$>
      loggedRaw decode raw state = replayRaw decode raw state := by
  cases parsed : decode raw with
  | none => simp [loggedRaw, replayRaw, publicReply, parsed]
  | some target =>
    simp only [loggedRaw, replayRaw, publicReply, parsed, map_bind, map_pure]
    rfl

/-- The public sealing history equals the actual complete source sealing log after every supported request, including rejected raw and nonce-reuse attempts. -/
theorem loggedImpl_recordReply (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (result : ReceiveSpec.Range query × AdaptiveCtxReceive.ReceiveState)
    (supported : result ∈ support ((loggedImpl decode c key query).run state)) :
    recordReply query result.1 state.ctx.successfulSeals = result.2.ctx.successfulSeals := by
  cases query with
  | inl request =>
    cases request with
    | inl coin =>
      change result ∈ support ((unifSpec.query coin : ProbComp _) >>= fun answer => pure (answer, state)) at supported
      obtain ⟨answer, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl
    | inr operation =>
      change result ∈ support (independentCtx c key operation state) at supported
      unfold independentCtx at supported
      obtain ⟨ctxResult, step, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      cases operation with
      | inl hash =>
        change ctxResult ∈ support ((ctxIndependentPublicOracle hash).run state.ctx) at step
        simp only [ctxIndependentPublicOracle, StateT.run] at step
        obtain ⟨lookup, _, step⟩ := (mem_support_bind_iff _ _ _).mp step
        obtain rfl := eq_of_mem_support_pure step
        rfl
      | inr input =>
        change ctxResult ∈ support ((ctxKeyFreeSealOracle c key input).run state.ctx) at step
        simp only [ctxKeyFreeSealOracle, StateT.run] at step
        split at step
        · obtain rfl := eq_of_mem_support_pure step
          rfl
        · obtain ⟨lookup, _, step⟩ := (mem_support_bind_iff _ _ _).mp step
          obtain rfl := eq_of_mem_support_pure step
          rfl
  | inr raw =>
    change result ∈ support (loggedRaw decode raw state) at supported
    cases parsed : decode raw with
    | none =>
      simp only [loggedRaw, parsed] at supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl
    | some target =>
      simp only [loggedRaw, parsed] at supported
      obtain ⟨lookup, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl

/-- Interpreting one guarded query recovers the exact replay-only source transition and its complete poststate, including the redundant public history. -/
theorem guard_query_complete (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState) :
    (simulateQ (loggedImpl decode c key)
      ((guard decode query).run state.ctx.successfulSeals)).run state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$>
        ((replayImpl decode c key query).run state) := by
  cases query with
  | inl request =>
    simp only [guard, StateT.run, bind_pure_comp, simulateQ_map,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have same : replayImpl decode c key (.inl request) state = loggedImpl decode c key (.inl request) state := by
      cases request <;> rfl
    rw [same]
    change (fun result => ((result.1, recordReply (.inl request) result.1 state.ctx.successfulSeals), result.2)) <$>
      loggedImpl decode c key (.inl request) state = _
    simp only [← bind_pure_comp]
    apply OracleComp.bind_congr_of_forall_mem_support
    intro result supported
    rw [loggedImpl_recordReply decode c key (.inl request) state result supported]
  | inr raw =>
    simp only [guard, StateT.run, bind_pure_comp, simulateQ_map,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change (fun result => ((publicReply decode state.ctx.successfulSeals raw, state.ctx.successfulSeals), result.2)) <$>
      loggedRaw decode raw state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$> replayRaw decode raw state
    cases parsed : decode raw with
    | none => simp [loggedRaw, replayRaw, publicReply, parsed]
    | some target =>
      simp only [loggedRaw, replayRaw, publicReply, parsed, map_bind, map_pure]
      rfl

/-- The public guard and the actual replay comparison have the same complete adaptive source result, including every cache and the exact redundant successful history. -/
theorem guard_run_complete {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : OracleComp ReceiveSpec Result) (state : AdaptiveCtxReceive.ReceiveState) :
    (simulateQ (loggedImpl decode c key)
      ((simulateQ (guard decode) adversary).run state.ctx.successfulSeals)).run state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$>
        ((simulateQ (replayImpl decode c key) adversary).run state) := by
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rw [guard_query_complete, bind_map_left, map_bind]
    apply OracleComp.bind_congr_of_forall_mem_support
    exact fun result _ => ih result.1 result.2

/-- Erasing only the redundant public guard history recovers the exact complete replay-source result. -/
theorem guardedGame_complete {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (adversary : OracleComp ReceiveSpec Result) :
    (fun result => (result.1.1, result.2)) <$>
      ((simulateQ (loggedImpl decode c key) (guardedClient decode adversary)).run initialState) =
      ((simulateQ (replayImpl decode c key) adversary).run initialState) := by
  rw [show guardedClient decode adversary =
      ((simulateQ (guard decode) adversary).run initialState.ctx.successfulSeals) from rfl,
    guard_run_complete]
  simp only [Functor.map_map, Prod.eta]
  change id <$> _ = _
  exact id_map _

/-- Retaining the same sampled analysis key and erasing only the redundant guard log gives the exact replay game. -/
theorem retainedGuard_complete {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Result) :
    (fun result => (result.1, (result.2.1.1, result.2.2))) <$>
      retainedDirectLoggedGame decode c (guardedClient decode adversary) =
      retainedReplayGame decode c adversary := by
  simp only [retainedDirectLoggedGame, loggedGame, retainedReplayGame, map_bind,
    bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro key _
  simpa only [Functor.map_map, Function.comp_def] using
    congrArg (fun computation => (Prod.mk key) <$> computation)
      (guardedGame_complete decode c key adversary)

/-- The conventional ciphertext distinguisher returns only the original adversary's Boolean decision. Hidden keys and private terminal state are not outputs of this reduction. -/
noncomputable def viewReduction (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool) :
    ModifiedNonceAeadINDDollarAdversary :=
  ⟨(fun result => result.1.1.1) <$> sourceClient decode (guardedClient decode adversary)⟩

/-- The actual replay comparison's public decision, with its terminal analysis key and private state discarded. -/
noncomputable def replayView (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Bool) : ProbComp Bool :=
  (fun result => result.2.1) <$> retainedReplayGame decode c adversary

/-- The ordinary real encryption experiment realizes the exact public replay view, preserving full source histories before this final observation projection. -/
theorem viewReduction_real_eq (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Bool) :
    modifiedNonceAeadINDDollarRealExp c (viewReduction decode adversary) =
      replayView decode c adversary := by
  have exactClient := congrArg
    (fun computation => (fun result => result.2.1.1) <$> computation)
    (retainedDirectLoggedGame_eq_client decode c (guardedClient decode adversary))
  have ordinary : (fun result => result.2.1.1) <$>
      retainedLoggedGame decode c (guardedClient decode adversary) =
      modifiedNonceAeadINDDollarRealExp c (viewReduction decode adversary) := by
    simp only [retainedLoggedGame, modifiedNonceAeadINDDollarRealExp, viewReduction,
      map_bind, simulateQ_map, StateT.run_map, Functor.map_map,
      bind_pure_comp]
  rw [← ordinary, ← exactClient]
  simpa only [replayView, Functor.map_map, Function.comp_def] using
    congrArg (fun computation => (fun result => result.2.1) <$> computation)
      (retainedGuard_complete decode c adversary)

/-- Explicit ordinary-random sealing simulation with the same source cache code and full-tuple replay guard. A stronger independent canonical-ideal description requires a separate simulation theorem. -/
noncomputable def randomView (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool) : ProbComp Bool :=
  modifiedNonceAeadINDDollarRandomExp (viewReduction decode adversary)

/-- After the exact real-view simulation, ciphertext replacement is precisely one ordinary Boolean IND$ reduction. -/
theorem replay_random_advantage (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Bool) :
    (replayView decode c adversary).boolDistAdvantage (randomView decode adversary) =
      modifiedNonceAeadINDDollarAdvantage c (viewReduction decode adversary) := by
  rw [← viewReduction_real_eq]
  rfl

/-- The canonical shared-ROM adversary's final decision; no analysis key or private terminal state is publicly disclosed. -/
noncomputable def canonicalView (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Bool) : ProbComp Bool :=
  (fun result => result.2.1) <$> AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c adversary

/-- Contracting the complete canonical/replay coupling to the actual adversary decision retains every previously charged integrity, prefix and alias term. -/
theorem canonical_replay_advantage_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp ReceiveSpec Bool)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((canonicalView decode c adversary).boolDistAdvantage (replayView decode c adversary)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c adversary qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) := by
  let left := AdaptiveCtxPrefixValidation.canonicalProjection <$>
    AdaptiveCtxPrefixValidation.retainedCanonicalGame decode c adversary
  let right := retainedReplayGame decode c adversary
  let decision := fun result : CtxKey × (Bool × AdaptiveCtxReceive.ReceiveState) => result.2.1
  have variation := (abs_probOutput_toReal_sub_le_tvDist (decision <$> left) (decision <$> right)).trans
    (tvDist_map_le decision left right)
  have projected : (canonicalView decode c adversary).boolDistAdvantage (replayView decode c adversary) ≤
      tvDist left right := by
    simpa only [ProbComp.boolDistAdvantage, canonicalView, replayView, left, right, decision,
      Functor.map_map, AdaptiveCtxPrefixValidation.canonicalProjection, Prod.map_apply,
      Function.comp_def, Prod.map_fst, id_eq] using variation
  exact (ENNReal.ofReal_le_ofReal projected).trans
    (canonical_replay_distance_bound decode c fallback adversary qHash qSeal qRaw
      hashBound sealBound rawBound small)

/-- Adaptive one-key ciphertext privacy against the explicit ordinary-random replay simulation. Both ordinary IND$ reductions and the same doubled indexed integrity family remain explicit. -/
theorem canonical_random_advantage_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp ReceiveSpec Bool)
    (qHash qSeal qRaw : ℕ)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (small : qSeal < 2 ^ 96) :
    ENNReal.ofReal ((canonicalView decode c adversary).boolDistAdvantage (randomView decode adversary)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction decode c adversary qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : ℕ) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c (viewReduction decode adversary)) := by
  have triangle := ENNReal.ofReal_le_ofReal (ProbComp.boolDistAdvantage_triangle
    (canonicalView decode c adversary) (replayView decode c adversary) (randomView decode adversary))
  rw [ENNReal.ofReal_add
    (show 0 ≤ (canonicalView decode c adversary).boolDistAdvantage (replayView decode c adversary)
      from abs_nonneg _)
    (show 0 ≤ (replayView decode c adversary).boolDistAdvantage (randomView decode adversary)
      from abs_nonneg _), replay_random_advantage] at triangle
  exact triangle.trans (add_le_add
    (canonical_replay_advantage_bound decode c fallback adversary qHash qSeal qRaw
      hashBound sealBound rawBound small) le_rfl)

end BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guardedClient_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guardedClient_query_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guardedRaw_eq_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guardedRaw_eq_replay

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.loggedImpl_recordReply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.loggedImpl_recordReply

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guard_query_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guard_query_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guard_run_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guard_run_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guardedGame_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.guardedGame_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.retainedGuard_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.retainedGuard_complete

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.viewReduction_real_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.viewReduction_real_eq

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.replay_random_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.replay_random_advantage

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard.canonical_random_advantage_bound
