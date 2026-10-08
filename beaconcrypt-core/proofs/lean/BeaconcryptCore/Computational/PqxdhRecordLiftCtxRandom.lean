-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-!
# Record-lift CTX privacy: the random one-key target is the IND$ random experiment (items 4 and 5, stage S4)

**The random target.** `randomTarget decode` runs `PqxdhRecordLiftIdeal.randomImpl` (random mode of `PqxdhRecordLiftIdeal.keyImpl`, `randomTarget_keyImpl`) on the shared BLAKE2b cache, exactly as the replay one-key target `AdaptiveCtxSharedModes.targetImpl false` runs replay mode (`replayTarget_keyImpl`). `target_step` and `target_schedule` show that it is the receive-state interpreter `randomReplayImpl` (coins, independent public hashing, `randomReceiveSeal`: nonce refusal, a uniform body of the plaintext's length, a uniform 16-byte tag and the commitment from the key-free suffix dictionary, and replay-dictionary raw acceptance `AdaptiveCtxReplayDictionary.replayRaw`), through the replay mode's own state projection.

**The IND$ random experiment.** `AdaptiveCtxPrivacyGuard.randomView decode client` is the modified-nonce AEAD IND$ random experiment run on `AdaptiveCtxPrivacyGuard.viewReduction decode client`: the client behind the public replay guard, compiled by the key-free CTX wrapper `AdaptiveCtxReceive.wrapped` and the raw-log simulator `AdaptiveCtxLogSimulation.runLogged`. `runLogged_eq` writes the log simulator as a stateful interpreter (`logImpl`); `randomLogged` and `randomLinked` compose it with the random challenger and the wrapper; `linked_step` and `linked_schedule` show that the composite is the direct logged random source `loggedRandomImpl` with the challenger's state determined by the receive state (`lift`); `guard_query` and `guard_run` remove the guard (its raw replies are the replay dictionary's, `AdaptiveCtxPrivacyGuard.guardedRaw_eq_replay`). `randomView_eq` concludes that `randomView` is the random replay source, and `randomTargetView_randomView` that it is the random one-key target view.

**The per-key privacy hop.** `replay_random_target`: for every one-key client, the replay one-key target and the random one-key target differ by exactly the ordinary IND$ advantage of `viewReduction`, so `PqxdhRecordLiftIdeal.privacyLoss` is the replay-to-random distance of the one-key targets (`privacyLoss_eq`). This closes the open point of `PqxdhRecordLiftIdeal` (guide `doc/impl/record-lift-ideal.md`): random mode is the IND$ random experiment behind `AdaptiveCtxPrivacyGuard.replay_random_advantage`. `random_forward`, `forward_step`, `forward_complete`, `local_public_history` and `public_history_step` give the random target the forwarding and public-history laws that `AdaptiveCtxSharedModes` proves for real and replay mode, for the three-mode challenger of `PqxdhRecordLiftCtxPrivModes`.

**Contracts.** No theorem of this module has an assumption or contract hypothesis. The contracts of the brief's H-7 list that each theorem uses are listed in `doc/impl/record-lift-ctx-priv.md`. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom
open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt CtxNonceAeadIndDollar
open CtxNonceAeadIndDollarValidation AdaptiveCtxReceive AdaptiveCtxSharedHash
open AdaptiveCtxReplayDictionary AdaptiveCtxLoggedSource

/-- Random sealing on the receive state. -/
noncomputable def randomReceiveSeal (input : CtxSealInput) (state : ReceiveState) :
    ProbComp (Option CtxRomRecord × ReceiveState) :=
  if input.nonce ∈ state.ctx.usedNonces then pure (none, state)
  else do
    let body ← $ᵗ (FixedBytes input.plaintext.length)
    let tag ← $ᵗ (FixedBytes 16)
    let lookup ← ctxKeyFreeSuffixStep (outerSuffix input.nonce input.context tag.toList) state.ctx.cache
    let record : CtxRomRecord := ⟨body.toList, tag.toList, tag.toList_length, lookup.1⟩
    pure (some record, ⟨state.ctx.addSeal ⟨input, record⟩ lookup.2, state.rawAttempts,
      outerSuffix input.nonce input.context tag.toList :: state.privateInputs⟩)

/-- Public hashing on the receive state. -/
noncomputable def publicReceive (query : CtxRO.Domain) (state : ReceiveState) :
    ProbComp (CtxDigest × ReceiveState) := do
  let result ← (ctxIndependentPublicOracle query).run state.ctx
  pure (result.1, ⟨result.2, state.rawAttempts, state.privateInputs⟩)

/-- The random receive state with replay-dictionary acceptance. -/
noncomputable def randomReplayImpl (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT ReceiveState ProbComp) := fun query state =>
  match query with
  | .inl (.inl coin) => do
      let answer ← unifSpec.query coin
      pure (answer, state)
  | .inl (.inr (.inl hash)) => publicReceive hash state
  | .inl (.inr (.inr input)) => randomReceiveSeal input state
  | .inr raw => replayRaw decode raw state

/-- The random one-key CTX target on the shared cache. -/
noncomputable def randomTarget (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxSharedModes.State ProbComp) :=
  (hashImpl.mapStateTBase (PqxdhRecordLiftIdeal.randomImpl decode)).flattenStateT

set_option backward.isDefEq.respectTransparency false in
/-- A random-mode seal on the shared cache is `randomReceiveSeal` on the reassembled receive state. -/
theorem seal_interpretation (input : CtxSealInput) (entry : AdaptiveCtxSharedReplay.Local)
    (cache : CtxRO.QueryCache) :
    AdaptiveCtxSharedReplay.reassemble <$>
        (simulateQ hashImpl (PqxdhRecordLiftIdeal.randomSeal input entry)).run cache =
      randomReceiveSeal input (AdaptiveCtxSharedReplay.install entry cache) := by
  by_cases used : input.nonce ∈ entry.1.usedNonces
  · simp only [PqxdhRecordLiftIdeal.randomSeal, used, ite_true, simulateQ_pure, StateT.run_pure, map_pure]
    simp [randomReceiveSeal, AdaptiveCtxSharedReplay.install, AdaptiveCtxSharedReplay.reassemble, used]
  · simp only [PqxdhRecordLiftIdeal.randomSeal, used, ite_false, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, AdaptiveCtxSharedReplay.hash_uniform, bind_map_left, map_bind]
    simp only [randomReceiveSeal, AdaptiveCtxSharedReplay.install, used, ite_false]
    apply bind_congr
    intro body
    apply bind_congr
    intro tag
    simp only [AdaptiveCtxSharedReplay.localPrivate, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      AdaptiveCtxSharedReplay.hash_uniform, bind_map_left, StateT.run_pure, bind_assoc, pure_bind, map_pure]
    rw [AdaptiveCtxSharedReplay.private_lookup_exact]
    simp only [bind_map_left]
    apply bind_congr
    intro lookup
    rfl


set_option backward.isDefEq.respectTransparency false in
/-- Every random-mode request on the shared cache is `randomReplayImpl` on the reassembled receive state. -/
theorem local_interpretation (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (entry : AdaptiveCtxSharedReplay.Local) (cache : CtxRO.QueryCache) :
    AdaptiveCtxSharedReplay.reassemble <$>
        (simulateQ hashImpl ((PqxdhRecordLiftIdeal.randomImpl decode query).run entry)).run cache =
      (randomReplayImpl decode query).run (AdaptiveCtxSharedReplay.install entry cache) := by
  cases query with
  | inl request =>
      cases request with
      | inl coin =>
          change AdaptiveCtxSharedReplay.reassemble <$> (simulateQ hashImpl (do
            let answer ← HashSpec.query (.inl coin)
            pure (answer, entry))).run cache = _
          simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
          rw [StateT.run_bind]
          simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
          rfl
      | inr operation =>
          cases operation with
          | inl hash =>
              change AdaptiveCtxSharedReplay.reassemble <$> (simulateQ hashImpl (do
                let answer ← HashSpec.query (.inr hash)
                pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2))).run
                  cache = _
              simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
              rw [StateT.run_bind]
              simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
              simp only [randomReplayImpl, publicReceive, ctxIndependentPublicOracle, StateT.run,
                bind_pure_comp, Functor.map_map]
              rfl
          | inr input => exact seal_interpretation input entry cache
  | inr raw => exact AdaptiveCtxSharedReplay.raw_interpretation decode raw entry cache

/-- The random target is the random replay source through the replay mode's state projection, request by request. -/
theorem target_step (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : AdaptiveCtxSharedModes.State) :
    Prod.map id AdaptiveCtxSharedModes.replayProjection <$> (randomTarget decode query).run state =
      (randomReplayImpl decode query).run (AdaptiveCtxSharedModes.replayProjection state) := by
  simp only [randomTarget, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq]
  exact local_interpretation decode query state.1 state.2

/-- The random target is the random replay source through the replay mode's state projection, for every program. -/
theorem target_schedule (decode : RawDecoder) {Result : Type} (client : OracleComp ReceiveSpec Result)
    (state : AdaptiveCtxSharedModes.State) :
    Prod.map id AdaptiveCtxSharedModes.replayProjection <$> (simulateQ (randomTarget decode) client).run state =
      (simulateQ (randomReplayImpl decode) client).run (AdaptiveCtxSharedModes.replayProjection state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (target_step decode) client state

/-- The decision of a one-key client against the random target. -/
noncomputable def randomTargetView (decode : RawDecoder) (client : OracleComp ReceiveSpec Bool) : ProbComp Bool :=
  Prod.fst <$> (simulateQ (randomTarget decode) client).run AdaptiveCtxSharedModes.initialState

/-- The random target view is the random replay source's decision. -/
theorem randomTargetView_eq (decode : RawDecoder) (client : OracleComp ReceiveSpec Bool) :
    randomTargetView decode client =
      Prod.fst <$> (simulateQ (randomReplayImpl decode) client).run AdaptiveCtxReceive.initialState := by
  have projected := congrArg (fun work => Prod.fst <$> work)
    (target_schedule decode client AdaptiveCtxSharedModes.initialState)
  rw [randomTargetView]
  simpa only [Functor.map_map, Prod.map_fst, id_eq, AdaptiveCtxSharedModes.replay_initial] using projected

/-! ### The IND$ random experiment -/

open AdaptiveRawNonceAead (AdaptiveSpec SealHistory recordPrimitiveAnswer simulatedOpen)

/-- `runLogged` as a stateful simulation. -/
def logImpl (decode : AdaptiveRawNonceAead.RawDecoder) :
    QueryImpl AdaptiveSpec (StateT SealHistory (OracleComp ModifiedNonceAeadAdversarySpec)) := fun query history =>
  match query with
  | .inl primitive => do
      let answer ← ModifiedNonceAeadAdversarySpec.query primitive
      pure (answer, recordPrimitiveAnswer primitive answer history)
  | .inr raw => pure (simulatedOpen decode history raw, history)

/-- The raw-log simulator is the stateful interpreter `logImpl`. -/
theorem runLogged_eq (decode : AdaptiveRawNonceAead.RawDecoder) {Result : Type}
    (adversary : OracleComp AdaptiveSpec Result) (history : SealHistory) :
    AdaptiveCtxLogSimulation.runLogged decode adversary history =
      (simulateQ (logImpl decode) adversary).run history := by
  induction adversary using OracleComp.inductionOn generalizing history with
  | pure result => simp
  | query_bind query next ih =>
      cases query with
      | inl primitive =>
          rw [AdaptiveCtxLogSimulation.runLogged_primitive]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
            StateT.run_bind]
          change _ = ((do
            let answer ← ModifiedNonceAeadAdversarySpec.query primitive
            pure (answer, recordPrimitiveAnswer primitive answer history)) >>= fun p =>
              (simulateQ (logImpl decode) (next p.1)).run p.2)
          simp only [bind_assoc, pure_bind, ih]
      | inr raw =>
          rw [AdaptiveCtxLogSimulation.runLogged_raw]
          simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
            StateT.run_bind]
          change _ = ((pure (simulatedOpen decode history raw, history) : OracleComp _ _) >>= fun p =>
              (simulateQ (logImpl decode) (next p.1)).run p.2)
          simp only [pure_bind, ih]


/-- The logged IND$ random challenger: primitive queries go to the random challenger and raw queries are answered from the log. -/
noncomputable def randomLogged (decode : AdaptiveRawNonceAead.RawDecoder) :
    QueryImpl AdaptiveSpec (StateT (SealHistory × ModifiedNonceAeadHandlerState) ProbComp) :=
  (modifiedNonceAeadINDDollarRandomImpl.mapStateTBase (logImpl decode)).flattenStateT

/-- One request of the logged random challenger. -/
theorem randomLogged_run (decode : AdaptiveRawNonceAead.RawDecoder) (query : AdaptiveSpec.Domain)
    (history : SealHistory) (state : ModifiedNonceAeadHandlerState) :
    (randomLogged decode query).run (history, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ modifiedNonceAeadINDDollarRandomImpl ((logImpl decode query).run history)).run state := rfl

/-- A lifted probabilistic computation passes through the logged random challenger unchanged. -/
theorem randomLogged_uniform (decode : AdaptiveRawNonceAead.RawDecoder) {Result : Type} (work : ProbComp Result)
    (state : SealHistory × ModifiedNonceAeadHandlerState) :
    (simulateQ (randomLogged decode) (OracleComp.liftComp work AdaptiveSpec)).run state =
      (fun answer => (answer, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (simulateQ (randomLogged decode) (AdaptiveSpec.query (.inl (.inl coin)))).run before = _
  rcases before with ⟨history, primitive⟩
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [randomLogged_run]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ modifiedNonceAeadINDDollarRandomImpl (do
      let answer ← ModifiedNonceAeadAdversarySpec.query (.inl coin)
      pure (answer, history))).run primitive = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$> ((do
      let answer ← liftM (unifSpec.query coin)
      pure (answer, primitive) : ProbComp _) >>= fun result => pure ((result.1, history), result.2)) = _
  simp only [bind_pure_comp, Functor.map_map]


/-- A primitive seal of the logged random challenger is the random seal oracle, logged. -/
theorem randomLogged_seal (decode : AdaptiveRawNonceAead.RawDecoder) (input : ModifiedNonceAeadSealInput)
    (history : SealHistory) (state : ModifiedNonceAeadHandlerState) :
    (simulateQ (randomLogged decode) (AdaptiveSpec.query (.inl (.inr input)))).run (history, state) =
      (fun result => (result.1, (recordPrimitiveAnswer (.inr input) result.1 history, result.2))) <$>
        (modifiedNonceAeadINDDollarRandomSealOracle input).run state := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [randomLogged_run]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ modifiedNonceAeadINDDollarRandomImpl (do
      let answer ← ModifiedNonceAeadAdversarySpec.query (.inr input)
      pure (answer, recordPrimitiveAnswer (.inr input) answer history))).run state = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$> ((modifiedNonceAeadINDDollarRandomSealOracle input).run
    state >>= fun result => pure ((result.1, recordPrimitiveAnswer (.inr input) result.1 history), result.2)) = _
  simp only [bind_pure_comp, Functor.map_map]

/-- A raw opening of the logged random challenger is answered from the log. -/
theorem randomLogged_raw (decode : AdaptiveRawNonceAead.RawDecoder) (raw : Pqxdh.Bytes)
    (history : SealHistory) (state : ModifiedNonceAeadHandlerState) :
    (simulateQ (randomLogged decode) (AdaptiveSpec.query (.inr raw))).run (history, state) =
      pure (simulatedOpen decode history raw, (history, state)) := by
  simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rw [randomLogged_run]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ modifiedNonceAeadINDDollarRandomImpl (pure (simulatedOpen decode history raw, history) :
      OracleComp ModifiedNonceAeadAdversarySpec _)).run state = _
  simp only [simulateQ_pure, StateT.run_pure, map_pure]

/-- Run equation of the IND$ random seal oracle. -/
theorem randomSealOracle_run (input : ModifiedNonceAeadSealInput) (state : ModifiedNonceAeadHandlerState) :
    (modifiedNonceAeadINDDollarRandomSealOracle input).run state =
      (if input.nonce ∈ state.usedNonces then pure (none, state)
      else do
        let body ← $ᵗ (FixedBytes input.plaintext.length)
        let tag ← $ᵗ (FixedBytes 16)
        pure (some ⟨body.toList, tag.toList, tag.toList_length⟩,
          state.addSeal ⟨input, ⟨body.toList, tag.toList, tag.toList_length⟩⟩)) :=
  rfl

/-- The key-free CTX wrapper linked to the logged random challenger. -/
noncomputable def randomLinked (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT (ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) ProbComp) :=
  ((randomLogged (baseDecoder decode)).mapStateTBase (reductionImpl decode)).flattenStateT

/-- One request of the wrapper linked to the logged random challenger. -/
theorem randomLinked_run (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : ReceiveState)
    (base : SealHistory × ModifiedNonceAeadHandlerState) :
    (randomLinked decode query).run (state, base) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (randomLogged (baseDecoder decode)) ((reductionImpl decode query).run state)).run base := rfl

/-- The direct logged random source. -/
noncomputable def loggedRandomImpl (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT ReceiveState ProbComp) := fun query state =>
  match query with
  | .inl (.inl coin) => do
      let answer ← unifSpec.query coin
      pure (answer, state)
  | .inl (.inr (.inl hash)) => publicReceive hash state
  | .inl (.inr (.inr input)) => randomReceiveSeal input state
  | .inr raw => loggedRaw decode raw state

/-- The logged random challenger's state determined by the receive state. -/
def lift (state : ReceiveState) : ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState) :=
  (state, (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals,
    ctxIndependentTagStateToModifiedNonceAead state.ctx)

set_option backward.isDefEq.respectTransparency false in
/-- Every request of the wrapper linked to the logged random challenger is the logged random source, with the challenger's log and state determined by the receive state. -/
theorem linked_step (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : ReceiveState) :
    (randomLinked decode query).run (lift state) = Prod.map id lift <$> (loggedRandomImpl decode query).run state := by
  rw [lift, randomLinked_run]
  rcases query with (coin | (hash | input)) | raw
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (randomLogged (baseDecoder decode)) ((fun answer => (answer, state)) <$>
        OracleComp.liftComp (unifSpec.query coin : ProbComp _) AdaptiveSpec)).run _ = _
    simp only [simulateQ_map, StateT.run_map, randomLogged_uniform, Functor.map_map]
    rfl
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (randomLogged (baseDecoder decode)) (publicStep hash state)).run _ = _
    simp only [publicStep, simulateQ_bind, simulateQ_pure, StateT.run_bind, randomLogged_uniform, bind_map_left,
      StateT.run_pure, map_bind, map_pure]
    simp only [loggedRandomImpl, publicReceive, ctxIndependentPublicOracle, StateT.run, bind_assoc, pure_bind,
      map_bind, map_pure]
    rfl
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (randomLogged (baseDecoder decode)) (sealStep input state)).run _ = _
    simp only [sealStep, simulateQ_bind, StateT.run_bind, randomLogged_seal, bind_map_left]
    by_cases used : input.nonce ∈ state.ctx.usedNonces
    · simp [modifiedNonceAeadINDDollarRandomSealOracle, CtxSealInput.toModifiedNonceAeadSealInput,
        ctxIndependentTagStateToModifiedNonceAead, used, loggedRandomImpl, randomReceiveSeal, StateT.run]
      rfl
    · have unused : (CtxSealInput.toModifiedNonceAeadSealInput input).nonce ∉
          (ctxIndependentTagStateToModifiedNonceAead state.ctx).usedNonces := used
      simp only [randomSealOracle_run, unused, ite_false, bind_assoc, pure_bind, map_bind]
      change _ = Prod.map id lift <$> randomReceiveSeal input state
      simp only [randomReceiveSeal, used, ite_false, map_bind]
      apply bind_congr
      intro body
      apply bind_congr
      intro tag
      simp only [privateStep, simulateQ_bind, simulateQ_pure, StateT.run_bind, randomLogged_uniform, bind_map_left,
        StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind]
      apply bind_congr
      intro lookup
      rfl
  · change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (randomLogged (baseDecoder decode)) (rawStep decode raw state)).run _ =
        Prod.map id lift <$> loggedRaw decode raw state
    cases parsed : decode raw with
    | none =>
        simp only [rawStep, loggedRaw, parsed, simulateQ_pure, StateT.run_pure, map_pure]
        rfl
    | some target =>
        simp only [rawStep, loggedRaw, parsed, privateStep, simulateQ_bind, StateT.run_bind,
          randomLogged_uniform, bind_map_left, map_bind, map_pure, bind_assoc, pure_bind]
        apply bind_congr
        rintro ⟨digest, cache⟩
        by_cases equal : target.record.commit = digest
        · simp only [equal, ite_true, simulateQ_bind, simulateQ_pure, StateT.run_bind, randomLogged_raw, pure_bind,
            StateT.run_pure, map_pure]
          have opened : simulatedOpen (baseDecoder decode)
              (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals raw =
              AdaptiveRawNonceAead.loggedPlaintext (ctxIndependentTagStateToModifiedNonceAead state.ctx).successfulSeals
                (baseTarget target) := by
            simp only [simulatedOpen, baseDecoder, parsed, Option.map_some, Option.bind_some]
          rw [opened]
          rfl
        · simp only [equal, ite_false, simulateQ_pure, StateT.run_pure, map_pure]
          rfl


/-- A step-wise state embedding lifts to every program. -/
theorem run_simulateQ_embed {ι : Type} {spec : OracleSpec ι} {σ τ : Type}
    (impl₁ : QueryImpl spec (StateT σ ProbComp)) (impl₂ : QueryImpl spec (StateT τ ProbComp)) (embed : τ → σ)
    (step : ∀ query state, (impl₁ query).run (embed state) = Prod.map id embed <$> (impl₂ query).run state)
    {α : Type} (program : OracleComp spec α) (state : τ) :
    (simulateQ impl₁ program).run (embed state) = Prod.map id embed <$> (simulateQ impl₂ program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      rw [step, bind_map_left]
      exact bind_congr fun result => ih result.1 result.2

/-- The wrapper linked to the logged random challenger is the logged random source, for every program. -/
theorem linked_schedule (decode : RawDecoder) {Result : Type} (client : OracleComp ReceiveSpec Result)
    (state : ReceiveState) :
    (simulateQ (randomLinked decode) client).run (lift state) =
      Prod.map id lift <$> (simulateQ (loggedRandomImpl decode) client).run state :=
  run_simulateQ_embed _ _ lift (linked_step decode) client state

/-! ### The public replay guard -/

set_option backward.isDefEq.respectTransparency false in
/-- The guard's recorded history is the actual successful-seal history after every non-raw request. -/
theorem recordReply_history (decode : RawDecoder) (request : (unifSpec + CtxAdversarySpec).Domain)
    (state : ReceiveState) :
    (fun result => ((result.1, AdaptiveCtxPrivacyGuard.recordReply (.inl request) result.1 state.ctx.successfulSeals),
        result.2)) <$> (loggedRandomImpl decode (.inl request)).run state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$>
        (loggedRandomImpl decode (.inl request)).run state := by
  rcases request with coin | (hash | input)
  · change _ <$> (do let answer ← unifSpec.query coin; pure (answer, state) : ProbComp _) =
      _ <$> (do let answer ← unifSpec.query coin; pure (answer, state) : ProbComp _)
    simp only [map_bind, map_pure]
    rfl
  · change _ <$> publicReceive hash state = _ <$> publicReceive hash state
    simp only [publicReceive, ctxIndependentPublicOracle, StateT.run, map_bind, map_pure, bind_assoc, pure_bind]
    rfl
  · change _ <$> randomReceiveSeal input state = _ <$> randomReceiveSeal input state
    unfold randomReceiveSeal
    split
    · simp only [map_pure]
      rfl
    · simp only [map_bind, map_pure]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- One guarded request on the logged random source is the random replay source's request. -/
theorem guard_query (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : ReceiveState) :
    (simulateQ (loggedRandomImpl decode)
      ((AdaptiveCtxPrivacyGuard.guard decode query).run state.ctx.successfulSeals)).run state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$>
        (randomReplayImpl decode query).run state := by
  cases query with
  | inl request =>
    simp only [AdaptiveCtxPrivacyGuard.guard, StateT.run, bind_pure_comp, simulateQ_map,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    have same : randomReplayImpl decode (.inl request) state = loggedRandomImpl decode (.inl request) state := by
      rcases request with coin | (hash | input) <;> rfl
    rw [same]
    change (((fun a => (a, AdaptiveCtxPrivacyGuard.recordReply (.inl request) a state.ctx.successfulSeals)) <$>
      loggedRandomImpl decode (.inl request)).run state) = _
    rw [StateT.run_map]
    exact recordReply_history decode request state
  | inr raw =>
    simp only [AdaptiveCtxPrivacyGuard.guard, StateT.run, bind_pure_comp, simulateQ_map,
      simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change (((fun _ => (AdaptiveCtxPrivacyGuard.publicReply decode state.ctx.successfulSeals raw,
      state.ctx.successfulSeals)) <$> loggedRandomImpl decode (.inr raw)).run state) = _
    rw [StateT.run_map]
    change (fun result => ((AdaptiveCtxPrivacyGuard.publicReply decode state.ctx.successfulSeals raw,
      state.ctx.successfulSeals), result.2)) <$> loggedRaw decode raw state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$> replayRaw decode raw state
    cases parsed : decode raw with
    | none => simp [loggedRaw, replayRaw, AdaptiveCtxPrivacyGuard.publicReply, parsed]
    | some target =>
      simp only [loggedRaw, replayRaw, AdaptiveCtxPrivacyGuard.publicReply, parsed, map_bind, map_pure]
      rfl

/-- The public guard on the logged random source is the random replay source. -/
theorem guard_run {Result : Type} (decode : RawDecoder) (client : OracleComp ReceiveSpec Result)
    (state : ReceiveState) :
    (simulateQ (loggedRandomImpl decode)
      ((simulateQ (AdaptiveCtxPrivacyGuard.guard decode) client).run state.ctx.successfulSeals)).run state =
      (fun result => ((result.1, result.2.ctx.successfulSeals), result.2)) <$>
        (simulateQ (randomReplayImpl decode) client).run state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
    simp only [StateT.run_bind, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    rw [guard_query, bind_map_left, map_bind]
    exact bind_congr fun result => ih result.1 result.2

/-- **The IND$ random experiment behind `randomView` is the random replay source.** -/
theorem randomView_eq (decode : RawDecoder) (client : OracleComp ReceiveSpec Bool) :
    AdaptiveCtxPrivacyGuard.randomView decode client =
      Prod.fst <$> (simulateQ (randomReplayImpl decode) client).run AdaptiveCtxReceive.initialState := by
  simp only [AdaptiveCtxPrivacyGuard.randomView, modifiedNonceAeadINDDollarRandomExp,
    AdaptiveCtxPrivacyGuard.viewReduction, AdaptiveCtxLogSimulation.sourceClient, runLogged_eq,
    AdaptiveCtxReceive.wrapped, simulateQ_map, StateT.run_map]
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  rw [show (AdaptiveCtxReceive.initialState, ([] : SealHistory), emptyModifiedNonceAeadHandlerState) =
      lift AdaptiveCtxReceive.initialState from rfl]
  rw [show ((modifiedNonceAeadINDDollarRandomImpl.mapStateTBase (logImpl (baseDecoder decode))).flattenStateT.mapStateTBase
      (reductionImpl decode)).flattenStateT = randomLinked decode from rfl]
  rw [linked_schedule, AdaptiveCtxPrivacyGuard.guardedClient,
    show ([] : AdaptiveCtxPrivacyGuard.PublicHistory) = AdaptiveCtxReceive.initialState.ctx.successfulSeals from rfl,
    guard_run]
  simp only [Functor.map_map, bind_pure_comp]
  rfl


/-- **The random one-key target is the IND$ random experiment behind `randomView`.** -/
theorem randomTargetView_randomView (decode : RawDecoder) (client : OracleComp ReceiveSpec Bool) :
    randomTargetView decode client = AdaptiveCtxPrivacyGuard.randomView decode client := by
  rw [randomTargetView_eq, randomView_eq]

/-- The random one-key target is `PqxdhRecordLiftIdeal.keyImpl` in random mode on the shared cache, for every primitive record and key (random mode reads neither). -/
theorem randomTarget_keyImpl (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    randomTarget decode =
      (hashImpl.mapStateTBase (PqxdhRecordLiftIdeal.keyImpl decode crypto key .random)).flattenStateT := rfl

/-- The replay one-key target is `PqxdhRecordLiftIdeal.keyImpl` in replay mode on the shared cache. -/
theorem replayTarget_keyImpl (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    AdaptiveCtxSharedModes.targetImpl false decode crypto key =
      (hashImpl.mapStateTBase (PqxdhRecordLiftIdeal.keyImpl decode crypto key .replay)).flattenStateT := rfl

/-- **Replay versus random, one key.** The replay one-key target and the random one-key target differ, for every one-key client, by exactly the ordinary IND$ advantage of the view reduction, that is `PqxdhRecordLiftIdeal.privacyLoss` (without `ofReal`). -/
theorem replay_random_target (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp ReceiveSpec Bool) :
    (AdaptiveCtxSharedModes.targetView false decode crypto client).boolDistAdvantage (randomTargetView decode client) =
      modifiedNonceAeadINDDollarAdvantage crypto (AdaptiveCtxPrivacyGuard.viewReduction decode client) := by
  rw [AdaptiveCtxSharedModes.replay_view_eq, randomTargetView_randomView]
  exact AdaptiveCtxPrivacyGuard.replay_random_advantage decode crypto client

/-- The per-key privacy loss of the targets is the replay-to-random distance of the one-key targets. -/
theorem privacyLoss_eq (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp ReceiveSpec Bool) :
    PqxdhRecordLiftIdeal.privacyLoss decode crypto client =
      ENNReal.ofReal ((AdaptiveCtxSharedModes.targetView false decode crypto client).boolDistAdvantage
        (randomTargetView decode client)) := by
  rw [replay_random_target]
  rfl


/-! ### Forwarded coins and hashes on the random target -/

open AdaptiveCtxSharedTarget (SharedState sharedImpl forward cache_schedule)

/-- Random mode answers a forwarded coin or public hash like the other modes. -/
theorem random_forward (decode : RawDecoder) (query : HashSpec.Domain) (entry : AdaptiveCtxSharedModes.Entry) :
    (PqxdhRecordLiftIdeal.randomImpl decode (AdaptiveCtxSharedModes.forwardIndex query)).run entry = (do
      let answer ← HashSpec.query query
      pure (AdaptiveCtxSharedModes.forwardReply query answer, AdaptiveCtxSharedModes.afterHash query entry)) := by
  cases query <;> rfl

/-- One request of the random target. -/
theorem target_run (decode : RawDecoder) (query : ReceiveSpec.Domain) (state : AdaptiveCtxSharedModes.State) :
    (randomTarget decode query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ hashImpl ((PqxdhRecordLiftIdeal.randomImpl decode query).run state.1)).run state.2 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A forwarded coin or public hash has the shared-cache effect on the random target. -/
theorem forward_step (decode : RawDecoder) (before : AdaptiveCtxSharedModes.State) (query : HashSpec.Domain)
    (shared : SharedState) :
    Prod.map id (AdaptiveCtxSharedModes.replaceShared before) <$> (sharedImpl query).run shared =
      (simulateQ (randomTarget decode) (forward query)).run (AdaptiveCtxSharedModes.replaceShared before shared) := by
  cases query with
  | inl coin =>
      rw [forward, simulateQ_spec_query, target_run]
      have linked := random_forward decode (.inl coin) (AdaptiveCtxSharedModes.replaceShared before shared).1
      simp only [AdaptiveCtxSharedModes.forwardIndex, AdaptiveCtxSharedModes.forwardReply] at linked
      rw [linked]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [StateT.run_bind]
      simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
      rw [AdaptiveCtxSharedModes.hash_uniform_step]
      simp [sharedImpl, StateT.run, AdaptiveCtxSharedModes.replaceShared, AdaptiveCtxSharedModes.afterHash]
  | inr hash =>
      rw [forward, simulateQ_spec_query, target_run]
      have linked := random_forward decode (.inr hash) (AdaptiveCtxSharedModes.replaceShared before shared).1
      simp only [AdaptiveCtxSharedModes.forwardIndex, AdaptiveCtxSharedModes.forwardReply] at linked
      rw [linked]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [StateT.run_bind]
      simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
      simp [sharedImpl, hashImpl, StateT.run, AdaptiveCtxSharedModes.replaceShared, AdaptiveCtxSharedModes.afterHash]

/-- Forwarded hash work on the random target changes only the shared cache and the public history. -/
theorem forward_complete (decode : RawDecoder) (before : AdaptiveCtxSharedModes.State) {Result : Type}
    (work : OracleComp HashSpec Result) :
    (simulateQ (randomTarget decode) (simulateQ forward work)).run before =
      Prod.map id (AdaptiveCtxSharedModes.replaceShared before) <$>
        (simulateQ sharedImpl work).run (before.2, before.1.1.publicInputs) := by
  have schedule : Prod.map id (AdaptiveCtxSharedModes.replaceShared before) <$>
      (simulateQ sharedImpl work).run (before.2, before.1.1.publicInputs) =
      (simulateQ (randomTarget decode) (simulateQ forward work)).run
        (AdaptiveCtxSharedModes.replaceShared before (before.2, before.1.1.publicInputs)) := by
    simpa only [QueryImpl.simulateQ_compose] using
      map_run_simulateQ_eq_of_query_map_eq sharedImpl (randomTarget decode ∘ₛ forward)
        (AdaptiveCtxSharedModes.replaceShared before) (forward_step decode before) work
        (before.2, before.1.1.publicInputs)
  exact schedule.symm

set_option backward.isDefEq.respectTransparency false in
/-- The random local state keeps no information in its public history: replacing it commutes with every request. -/
theorem local_public_history (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (entry : AdaptiveCtxSharedModes.Entry) (history : List Pqxdh.Bytes) :
    Prod.map id (fun after => AdaptiveCtxSharedModes.replaceEntryPublic after
        (AdaptiveCtxSharedTarget.nextPublic query history)) <$>
      (PqxdhRecordLiftIdeal.randomImpl decode query).run entry =
      (PqxdhRecordLiftIdeal.randomImpl decode query).run (AdaptiveCtxSharedModes.replaceEntryPublic entry history) := by
  rcases query with (coin | (hash | input)) | raw
  all_goals simp only [StateT.run, PqxdhRecordLiftIdeal.randomImpl]
  all_goals simp [AdaptiveCtxSharedModes.replaceEntryPublic, AdaptiveCtxSharedTarget.nextPublic,
    PqxdhRecordLiftIdeal.randomSeal, AdaptiveCtxSharedReplay.localRaw, AdaptiveCtxSharedReplay.localPrivate,
    AdaptiveCtxReplayDictionary.replayPlaintext, AdaptiveCtxSharedReplay.install]
  all_goals split <;> simp_all [Functor.map_map, Prod.map_def]

set_option backward.isDefEq.respectTransparency false in
/-- The random target's public history can be kept separately. -/
theorem public_history_step (decode : RawDecoder) (query : ReceiveSpec.Domain)
    (before : AdaptiveCtxSharedModes.State) (history : List Pqxdh.Bytes) :
    Prod.map id (fun after => AdaptiveCtxSharedModes.replacePublic after
        (AdaptiveCtxSharedTarget.nextPublic query history)) <$> (randomTarget decode query).run before =
      (randomTarget decode query).run (AdaptiveCtxSharedModes.replacePublic before history) := by
  have full := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ hashImpl work).run before.2) (local_public_history decode query before.1 history)
  simp only [simulateQ_map, StateT.run_map, Functor.map_map] at full
  rw [target_run, target_run]
  simpa only [AdaptiveCtxSharedModes.replacePublic, AdaptiveCtxSharedModes.replaceEntryPublic, Prod.map_def, id_eq,
    Functor.map_map] using full

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.seal_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.seal_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.local_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.local_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.target_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.target_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.target_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.target_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomTargetView_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomTargetView_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.runLogged_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.runLogged_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLogged_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomSealOracle_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomSealOracle_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLinked_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomLinked_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.linked_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.run_simulateQ_embed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.run_simulateQ_embed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.linked_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.recordReply_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.recordReply_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.guard_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.guard_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.guard_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.guard_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomView_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomView_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomTargetView_randomView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomTargetView_randomView

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomTarget_keyImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.randomTarget_keyImpl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.replayTarget_keyImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.replayTarget_keyImpl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.replay_random_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.replay_random_target

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.privacyLoss_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.privacyLoss_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.random_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.random_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.target_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.target_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.forward_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.forward_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.forward_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.forward_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.local_public_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.local_public_history

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.public_history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom.public_history_step
