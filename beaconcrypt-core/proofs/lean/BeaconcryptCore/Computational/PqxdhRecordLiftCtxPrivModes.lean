-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxRandom

/-!
# Record-lift CTX privacy: three-mode known calls, the selected challenger in any mode and the per-key hop (items 4 and 5, stage S4)

**Three-mode known calls.** The privacy hybrids put coordinates in replay or random mode, so the one-key reduction of a hop must run other coordinates' records in random mode too, which the real/replay known calls of `PqxdhRecordLiftCtxModes` do not offer. `KnownCall` carries a `PqxdhRecordLiftIdeal.KeyMode`; `knownLocal sample` runs real and replay mode with the call's key (`PqxdhRecordLiftIdeal.keyImpl`) and random mode as `randomWith sample`, which is `PqxdhRecordLiftIdeal.randomImpl` with its body and tag drawn by the byte-string sampler `sample`. With the world's sampler `uniformBytes` (one coin per byte) a known call is exactly `keyImpl` in its mode (`randomWith_uniform`, `knownLocal_uniform`).

**The selected challenger.** `modeTarget selected` is the one-key target of mode `selected` on the shared cache (replay: `AdaptiveCtxSharedModes.targetImpl false`, `modeTarget_replay`; random: `PqxdhRecordLiftCtxRandom.randomTarget`, `modeTarget_random`). As in `AdaptiveCtxDynamicKnownKeys` and `PqxdhRecordLiftCtxModes`, `sourceImpl` is the challenger's source semantics and `reductionImpl` the key-free reduction that forwards known calls' coins and public hashes through the selected target; `selected_step`, `known_step`, `linked_step`, `linked_schedule` and `schedule_interpretation` show that the reduction run against the selected target is the source semantics, and `source_view` that the challenger's game decision is the constructed ordinary one-key client `decisionClient` against the selected target (`modeView`). The replay view is `AdaptiveCtxPrivacyGuard.replayView` (`modeView_replay`) and the random view has the law of `AdaptiveCtxPrivacyGuard.randomView` (`modeView_random`, from `PqxdhRecordLiftCtxRandom.randomTargetView_randomView`).

**Why a second sampler.** A random-mode known seal draws a body of the plaintext's length; with one coin per byte the reduction's coin count would grow with plaintext lengths, which no `Budget` field bounds. `bytesSample` draws a whole byte string with a single coin query (`bytesSample_eq`) and has the uniform law (`bytesSample_evalDist`). `SameLaw` (interchangeable before every Boolean decision) is a congruence for bind and stateful simulation (`sameLaw_bind`, `sameLaw_simulateQ`); the two samplers are interchangeable (`sameLaw_bytes`), hence so are random seals, known calls and the challenger's whole game (`sameLaw_seal`, `sameLaw_known`, `sameLaw_source_step`, `sameLaw_sourceGame`).

**The per-key privacy hop.** With the world's sampler on the challenger's side and the single-coin sampler inside the constructed client, the replay game has the law of the replay one-key view (`replay_game`) and the random game that of the IND$ random experiment (`random_game`), so `hop_advantage`: the two games differ by exactly the ordinary IND$ advantage of `AdaptiveCtxPrivacyGuard.viewReduction` of the constructed client, the per-key term of `PqxdhRecordLiftIdeal.privacyLoss`.

**Contracts.** No theorem of this module has an assumption or contract hypothesis; the contracts of the brief's H-7 list used by each theorem are listed in `doc/impl/record-lift-ctx-priv.md`. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedHash

/-- The uniform byte-string sampler of `PqxdhRecordLiftIdeal.randomSeal`: one coin per byte. -/
noncomputable def uniformBytes (length : Nat) : ProbComp (FixedBytes length) := $ᵗ (FixedBytes length)

/-- The byte-string type of length `length` has `256 ^ length` elements. -/
theorem card_bytes (length : Nat) : Fintype.card (Fin (256 ^ length - 1 + 1)) = Fintype.card (FixedBytes length) := by
  have byte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in rfl
  rw [Fintype.card_fin, card_vector, byte]
  exact Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))

/-- A uniform byte string as one uniform number. -/
noncomputable def bytesEquiv (length : Nat) : Fin (256 ^ length - 1 + 1) ≃ FixedBytes length :=
  Fintype.equivOfCardEq (card_bytes length)

/-- The single-coin uniform sampler. -/
@[reducible] noncomputable def bytesSampleable (length : Nat) : SampleableType (FixedBytes length) :=
  @SampleableType.ofEquiv _ _ (SampleableType.Fin (256 ^ length - 1)) (bytesEquiv length)

/-- A uniform byte string from a single coin query. -/
noncomputable def bytesSample (length : Nat) : ProbComp (FixedBytes length) := (bytesSampleable length).selectElem

/-- `bytesSample` is one coin query mapped through `bytesEquiv`. -/
theorem bytesSample_eq (length : Nat) :
    bytesSample length = bytesEquiv length <$> ($[0..256 ^ length - 1] : ProbComp _) := rfl

/-- `bytesSample` has the uniform law of `uniformBytes`. -/
theorem bytesSample_evalDist (length : Nat) [MeasurableSpace (FixedBytes length)]
    [MeasurableSingletonClass (FixedBytes length)] : 𝒟[bytesSample length] = 𝒟[uniformBytes length] := by
  rw [bytesSample, (bytesSampleable length).evalDist_selectElem_eq_uniform, uniformBytes,
    SampleableType.evalDist_uniformSample]


/-! ### Random mode with a sampler -/

open PqxdhRecordLiftIdeal (KeyMode keyImpl KeyEntry)

/-- A uniform byte-string sampler: `uniformBytes` (the world's) or `bytesSample` (one coin per string). -/
abbrev Sampler := (length : Nat) → ProbComp (FixedBytes length)

/-- `PqxdhRecordLiftIdeal.randomSeal` with its body and tag drawn by `sample`. -/
noncomputable def sealWith (sample : Sampler) (input : CtxSealInput) (entry : KeyEntry) :
    OracleComp HashSpec (Option CtxRomRecord × KeyEntry) :=
  if input.nonce ∈ entry.1.usedNonces then pure (none, entry)
  else do
    let body ← OracleComp.liftComp (sample input.plaintext.length) HashSpec
    let tag ← OracleComp.liftComp (sample 16) HashSpec
    let commitment ← AdaptiveCtxSharedReplay.localPrivate
      (CtxSplitCache.outerSuffix input.nonce input.context tag.toList) entry
    let record : CtxRomRecord := ⟨body.toList, tag.toList, tag.toList_length, commitment.1⟩
    pure (some record, { commitment.2.1 with
      usedNonces := input.nonce :: commitment.2.1.usedNonces
      successfulSeals := ⟨input, record⟩ :: commitment.2.1.successfulSeals }, commitment.2.2)

/-- `PqxdhRecordLiftIdeal.randomImpl` with its seals drawn by `sample`. -/
noncomputable def randomWith (sample : Sampler) (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT KeyEntry (OracleComp HashSpec)) := fun query entry =>
  match query with
  | .inl (.inl coin) => do
      let answer ← HashSpec.query (.inl coin)
      pure (answer, entry)
  | .inl (.inr (.inl hash)) => do
      let answer ← HashSpec.query (.inr hash)
      pure (answer, { entry.1 with publicInputs := hash.2 :: entry.1.publicInputs }, entry.2)
  | .inl (.inr (.inr input)) => sealWith sample input entry
  | .inr raw => AdaptiveCtxSharedReplay.localRaw decode raw entry

/-- With the world's sampler, random mode is `PqxdhRecordLiftIdeal.randomImpl`. -/
theorem randomWith_uniform (decode : RawDecoder) :
    randomWith uniformBytes decode = PqxdhRecordLiftIdeal.randomImpl decode := by
  funext query
  rcases query with (coin | (hash | input)) | raw <;> rfl

/-! ### Three-mode known calls and a selected challenger in any mode -/

/-- A known call carries its own key, decoder, history slot and mode. -/
structure KnownCall extends AdaptiveCtxDynamicKnownKeys.KnownCall where
  mode : KeyMode

abbrev KnownSpec : OracleSpec KnownCall := fun call => ReceiveSpec.Range call.request
abbrev Spec := ReceiveSpec + KnownSpec

/-- The local program of a known call: real and replay mode with its key, random mode with `sample`. -/
noncomputable def knownLocal (sample : Sampler) (crypto : Pqxdh.Crypto) (call : KnownCall) :
    StateT KeyEntry (OracleComp HashSpec) (ReceiveSpec.Range call.request) :=
  match call.mode with
  | .real => keyImpl call.decode crypto call.key .real call.request
  | .replay => keyImpl call.decode crypto call.key .replay call.request
  | .random => randomWith sample call.decode call.request

/-- With the world's sampler, a known call runs `PqxdhRecordLiftIdeal.keyImpl` in its mode. -/
theorem knownLocal_uniform (crypto : Pqxdh.Crypto) (call : KnownCall) :
    knownLocal uniformBytes crypto call = keyImpl call.decode crypto call.key call.mode call.request := by
  unfold knownLocal
  cases call.mode
  · rfl
  · rfl
  · rw [randomWith_uniform]
    rfl

/-- The selected one-key target in a mode, on the shared cache. -/
noncomputable def modeTarget (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT AdaptiveCtxSharedModes.State ProbComp) :=
  (hashImpl.mapStateTBase (keyImpl decode crypto key selected)).flattenStateT

/-- The replay-mode target is the replay one-key target. -/
theorem modeTarget_replay (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    modeTarget .replay decode crypto key = AdaptiveCtxSharedModes.targetImpl false decode crypto key := rfl

/-- The random-mode target is the random one-key target. -/
theorem modeTarget_random (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    modeTarget .random decode crypto key = PqxdhRecordLiftCtxRandom.randomTarget decode := rfl

/-- One request of the selected target. -/
theorem modeTarget_run (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (state : AdaptiveCtxSharedModes.State) :
    (modeTarget selected decode crypto key query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ hashImpl ((keyImpl decode crypto key selected query).run state.1)).run state.2 := rfl

/-- A local request of the selected key is its target request, reassembled. -/
theorem mode_local_from_target (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (entry : KeyEntry) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl ((keyImpl decode crypto key selected query).run entry)).run cache =
      AdaptiveCtxSharedModes.dismantle <$> (modeTarget selected decode crypto key query).run (entry, cache) := by
  rw [modeTarget_run]
  simp only [Functor.map_map, AdaptiveCtxSharedModes.dismantle]
  exact (id_map _).symm

/-- The selected target's public history can be kept separately, in every mode. -/
theorem mode_public_history_step (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (before : AdaptiveCtxSharedModes.State) (history : List Pqxdh.Bytes) :
    Prod.map id (fun after => AdaptiveCtxSharedModes.replacePublic after
        (AdaptiveCtxSharedTarget.nextPublic query history)) <$> (modeTarget selected decode crypto key query).run before =
      (modeTarget selected decode crypto key query).run (AdaptiveCtxSharedModes.replacePublic before history) := by
  cases selected
  · exact AdaptiveCtxSharedModes.public_history_step true decode crypto key query before history
  · exact AdaptiveCtxSharedModes.public_history_step false decode crypto key query before history
  · exact PqxdhRecordLiftCtxRandom.public_history_step decode query before history

/-- Forwarded hash work on the selected target changes only the shared cache and the public history, in every mode. -/
theorem mode_forward_complete (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (before : AdaptiveCtxSharedModes.State) {Result : Type} (work : OracleComp HashSpec Result) :
    (simulateQ (modeTarget selected decode crypto key) (simulateQ AdaptiveCtxSharedTarget.forward work)).run before =
      Prod.map id (AdaptiveCtxSharedModes.replaceShared before) <$>
        (simulateQ AdaptiveCtxSharedTarget.sharedImpl work).run (before.2, before.1.1.publicInputs) := by
  cases selected
  · exact AdaptiveCtxSharedModes.forward_complete true decode crypto key before work
  · exact AdaptiveCtxSharedModes.forward_complete false decode crypto key before work
  · exact PqxdhRecordLiftCtxRandom.forward_complete decode before work


/-! ### The challenger and the key-free reduction -/

open AdaptiveCtxDynamicKnownKeys (SourceState ReductionState project erase initialReduction initialSource)

/-- The challenger's source semantics: the selected key in mode `selected`, every known call locally in its own mode,
all on one shared cache. -/
noncomputable def sourceImpl (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) : QueryImpl Spec (StateT SourceState ProbComp) := fun query state =>
  match query with
  | .inl request => do
      let result ← (simulateQ hashImpl ((keyImpl decode crypto key selected request).run state.selected)).run
        state.cache
      pure (result.1.1, { state with selected := result.1.2, cache := result.2 })
  | .inr known => do
      let result ← (simulateQ hashImpl ((knownLocal sample crypto known).run (state.others known.slot))).run
        state.cache
      pure (result.1.1, { state with others := Function.update state.others known.slot result.1.2, cache := result.2 })

/-- The key-free reduction: selected requests go to the challenger; known calls run locally, their coins and public
hashes forwarded through the challenger's interface. -/
noncomputable def reductionImpl (sample : Sampler) (crypto : Pqxdh.Crypto) :
    QueryImpl Spec (StateT ReductionState (OracleComp ReceiveSpec)) := fun query state =>
  match query with
  | .inl request => do
      let answer ← ReceiveSpec.query request
      pure (answer, { state with selectedPublic := AdaptiveCtxSharedTarget.nextPublic request state.selectedPublic })
  | .inr known => do
      let result ← simulateQ AdaptiveCtxSharedTarget.forward
        ((knownLocal sample crypto known).run (state.others known.slot))
      pure (result.1, { state with others := Function.update state.others known.slot result.2 })

/-- The reduction run against the selected one-key target. -/
noncomputable def linkedImpl (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) :
    QueryImpl Spec (StateT (ReductionState × AdaptiveCtxSharedModes.State) ProbComp) :=
  ((modeTarget selected decode crypto key).mapStateTBase (reductionImpl sample crypto)).flattenStateT

set_option backward.isDefEq.respectTransparency false in
/-- A selected request uses only the challenger. -/
theorem selected_step (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) (query : ReceiveSpec.Domain) (state : ReductionState) (target : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl sample selected decode crypto key (.inl query)).run (state, target) =
      (sourceImpl sample selected decode crypto key (.inl query)).run (project (state, target)) := by
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (modeTarget selected decode crypto key)
      (do let answer ← ReceiveSpec.query query
          pure (answer, { state with
            selectedPublic := AdaptiveCtxSharedTarget.nextPublic query state.selectedPublic }))).run target) = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  change _ = (do
    let result ← (simulateQ hashImpl ((keyImpl decode crypto key selected query).run
      (project (state, target)).selected)).run (project (state, target)).cache
    pure (result.1.1, { project (state, target) with selected := result.1.2, cache := result.2 }))
  rw [mode_local_from_target]
  have entry : ((project (state, target)).selected, (project (state, target)).cache) =
      AdaptiveCtxSharedModes.replacePublic target state.selectedPublic := rfl
  rw [entry, ← mode_public_history_step selected decode crypto key query target state.selectedPublic]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A known call is evaluated locally in its mode and shares the selected challenger's complete hash cache. -/
theorem known_step (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) (known : KnownCall) (state : ReductionState) (target : AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl sample selected decode crypto key (.inr known)).run (state, target) =
      (sourceImpl sample selected decode crypto key (.inr known)).run (project (state, target)) := by
  change Prod.map id project <$> ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (modeTarget selected decode crypto key)
      (do let result ← simulateQ AdaptiveCtxSharedTarget.forward
            ((knownLocal sample crypto known).run (state.others known.slot))
          pure (result.1, { state with others := Function.update state.others known.slot result.2 }))).run target) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [StateT.run_bind]
  simp only [StateT.run_pure, bind_pure_comp, Functor.map_map]
  rw [mode_forward_complete]
  change _ = (do
    let result ← (simulateQ hashImpl
      ((knownLocal sample crypto known).run (state.others known.slot))).run target.2
    pure (result.1.1, { project (state, target) with
      others := Function.update state.others known.slot result.1.2, cache := result.2 }))
  rw [← AdaptiveCtxSharedTarget.cache_schedule _ (target.2, target.1.1.publicInputs)]
  simp only [bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  rfl

/-- Every selected or known request preserves the complete source state. -/
theorem linked_step (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) (query : Spec.Domain) (state : ReductionState × AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (linkedImpl sample selected decode crypto key query).run state =
      (sourceImpl sample selected decode crypto key query).run (project state) := by
  cases query with
  | inl query => exact selected_step sample selected decode crypto key query state.1 state.2
  | inr known => exact known_step sample selected decode crypto key known state.1 state.2

/-- The reduction run against the selected target is the challenger's source semantics, for every program. -/
theorem linked_schedule (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (client : OracleComp Spec Result)
    (state : ReductionState × AdaptiveCtxSharedModes.State) :
    Prod.map id project <$> (simulateQ (linkedImpl sample selected decode crypto key) client).run state =
      (simulateQ (sourceImpl sample selected decode crypto key) client).run (project state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _ (linked_step sample selected decode crypto key) client state

/-- The reduction's ordinary one-key client with its final state. -/
noncomputable def wrapped (sample : Sampler) (crypto : Pqxdh.Crypto) {Result : Type} (client : OracleComp Spec Result)
    (state : ReductionState) : OracleComp ReceiveSpec (Result × ReductionState) :=
  (simulateQ (reductionImpl sample crypto) client).run state

/-- Interpreting the key-free reduction by the selected target gives the whole source execution. -/
theorem schedule_interpretation (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (client : OracleComp Spec Result) (state : ReductionState)
    (target : AdaptiveCtxSharedModes.State) :
    erase <$> (simulateQ (modeTarget selected decode crypto key) (wrapped sample crypto client state)).run target =
      (simulateQ (sourceImpl sample selected decode crypto key) client).run (project (state, target)) := by
  rw [wrapped, simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map]
  exact linked_schedule sample selected decode crypto key client (state, target)

/-- The challenger's game: a uniform selected key, then the client under the source semantics. -/
noncomputable def sourceGame (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp Spec Result) : ProbComp (Result × SourceState) := do
  let key ← $ᵗ CtxKey
  (simulateQ (sourceImpl sample selected decode crypto key) client).run initialSource

/-- The ordinary one-key CTX client built from a three-mode client. -/
noncomputable def decisionClient (sample : Sampler) (crypto : Pqxdh.Crypto) (client : OracleComp Spec Bool) :
    OracleComp ReceiveSpec Bool := Prod.fst <$> wrapped sample crypto client initialReduction

/-- The decision of an ordinary one-key client against the selected target in a mode. -/
noncomputable def modeView (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (client : OracleComp ReceiveSpec Bool) : ProbComp Bool :=
  Prod.fst <$> (do
    let key ← $ᵗ CtxKey
    (simulateQ (modeTarget selected decode crypto key) client).run AdaptiveCtxSharedModes.initialState)

/-- The challenger's game decision is the constructed one-key client against the selected target. -/
theorem source_view (sample : Sampler) (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (client : OracleComp Spec Bool) :
    Prod.fst <$> sourceGame sample selected decode crypto client =
      modeView selected decode crypto (decisionClient sample crypto client) := by
  simp only [sourceGame, modeView, decisionClient, map_bind, simulateQ_map, StateT.run_map, Functor.map_map]
  apply bind_congr
  intro key
  have exactRun := congrArg (fun work => Prod.fst <$> work)
    (schedule_interpretation sample selected decode crypto key client initialReduction
      AdaptiveCtxSharedModes.initialState)
  simpa only [Functor.map_map, erase, initialSource] using exactRun.symm

/-- In replay mode the selected view is the replay one-key view. -/
theorem modeView_replay (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp ReceiveSpec Bool) :
    modeView .replay decode crypto client = AdaptiveCtxPrivacyGuard.replayView decode crypto client := by
  rw [← AdaptiveCtxSharedModes.replay_view_eq]
  rfl

/-- In random mode the selected view has the law of the random one-key view, hence of the IND$ random experiment. -/
theorem modeView_random (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp ReceiveSpec Bool) :
    𝒟[modeView .random decode crypto client] = 𝒟[AdaptiveCtxPrivacyGuard.randomView decode client] := by
  rw [← PqxdhRecordLiftCtxRandom.randomTargetView_randomView, PqxdhRecordLiftCtxRandom.randomTargetView, modeView,
    map_bind]
  exact OracleComp.evalDist_bind_const ($ᵗ CtxKey)
    (Prod.fst <$> (simulateQ (PqxdhRecordLiftCtxRandom.randomTarget decode) client).run
      AdaptiveCtxSharedModes.initialState)


/-! ### Interchangeable samplers -/

/-- Two probabilistic computations are interchangeable before every Boolean decision. -/
def SameLaw {α : Type} (left right : ProbComp α) : Prop :=
  ∀ decision : α → ProbComp Bool, 𝒟[left >>= decision] = 𝒟[right >>= decision]

/-- Every computation is interchangeable with itself. -/
theorem sameLaw_refl {α : Type} (work : ProbComp α) : SameLaw work work := fun _ => rfl

/-- Interchangeable first steps and pointwise interchangeable continuations give interchangeable binds. -/
theorem sameLaw_bind {α β : Type} (left right : ProbComp α) (next other : α → ProbComp β)
    (first : SameLaw left right) (rest : ∀ value, SameLaw (next value) (other value)) :
    SameLaw (left >>= next) (right >>= other) := by
  intro decision
  rw [bind_assoc, bind_assoc]
  calc 𝒟[left >>= fun value => next value >>= decision]
      = 𝒟[left >>= fun value => other value >>= decision] :=
        evalDist_bind_congr _ _ _ (fun value => rest value decision)
    _ = 𝒟[right >>= fun value => other value >>= decision] := first _

/-- The world's sampler and the single-coin sampler are interchangeable. -/
theorem sameLaw_bytes (length : Nat) : SameLaw (uniformBytes length) (bytesSample length) := by
  intro decision
  let _ : MeasurableSpace (FixedBytes length) := ⊤
  have _ : DiscreteMeasurableSpace (FixedBytes length) := ⟨fun _ => trivial⟩
  have _ : MeasurableSingletonClass (FixedBytes length) := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, bytesSample_evalDist]

/-- Interchangeable programs have the same Boolean first component. -/
theorem sameLaw_fst {σ : Type} (left right : ProbComp (Bool × σ)) (same : SameLaw left right) :
    𝒟[Prod.fst <$> left] = 𝒟[Prod.fst <$> right] := by
  simpa only [map_eq_bind_pure_comp] using same (pure ∘ Prod.fst)

/-- Request-wise interchangeable stateful implementations are interchangeable on every program. -/
theorem sameLaw_simulateQ {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (left right : QueryImpl spec (StateT σ ProbComp))
    (step : ∀ query state, SameLaw ((left query).run state) ((right query).run state))
    {α : Type} (program : OracleComp spec α) (state : σ) :
    SameLaw ((simulateQ left program).run state) ((simulateQ right program).run state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => exact sameLaw_refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      exact sameLaw_bind _ _ _ _ (step query state) (fun result => ih result.1 result.2)

/-- The common rest of a random seal after its body and tag. -/
noncomputable def sealRest (input : CtxSealInput) (entry : KeyEntry) (cache : CtxRO.QueryCache)
    (body : FixedBytes input.plaintext.length) (tag : FixedBytes 16) :
    ProbComp ((Option CtxRomRecord × KeyEntry) × CtxRO.QueryCache) :=
  (simulateQ hashImpl (do
    let commitment ← AdaptiveCtxSharedReplay.localPrivate
      (CtxSplitCache.outerSuffix input.nonce input.context tag.toList) entry
    let record : CtxRomRecord := ⟨body.toList, tag.toList, tag.toList_length, commitment.1⟩
    pure (some record, { commitment.2.1 with
      usedNonces := input.nonce :: commitment.2.1.usedNonces
      successfulSeals := ⟨input, record⟩ :: commitment.2.1.successfulSeals }, commitment.2.2) :
      OracleComp HashSpec (Option CtxRomRecord × KeyEntry))).run cache

/-- A random seal on the shared cache draws its body and tag, then runs the common rest. -/
theorem seal_run (sample : Sampler) (input : CtxSealInput) (entry : KeyEntry) (cache : CtxRO.QueryCache) :
    (simulateQ hashImpl (sealWith sample input entry)).run cache =
      if input.nonce ∈ entry.1.usedNonces then pure ((none, entry), cache)
      else sample input.plaintext.length >>= fun body => sample 16 >>= fun tag => sealRest input entry cache body tag := by
  unfold sealWith
  split
  · simp only [simulateQ_pure, StateT.run_pure]
  · simp only [sealRest, simulateQ_bind, StateT.run_bind, AdaptiveCtxSharedReplay.hash_uniform, bind_map_left]

/-- Random seals with the two samplers are interchangeable. -/
theorem sameLaw_seal (input : CtxSealInput) (entry : KeyEntry) (cache : CtxRO.QueryCache) :
    SameLaw ((simulateQ hashImpl (sealWith uniformBytes input entry)).run cache)
      ((simulateQ hashImpl (sealWith bytesSample input entry)).run cache) := by
  rw [seal_run, seal_run]
  split
  · exact sameLaw_refl _
  · exact sameLaw_bind _ _ _ _ (sameLaw_bytes _) (fun body =>
      sameLaw_bind _ _ _ _ (sameLaw_bytes _) (fun tag => sameLaw_refl _))

/-- Known calls with the two samplers are interchangeable. -/
theorem sameLaw_known (crypto : Pqxdh.Crypto) (call : KnownCall) (entry : KeyEntry) (cache : CtxRO.QueryCache) :
    SameLaw ((simulateQ hashImpl ((knownLocal uniformBytes crypto call).run entry)).run cache)
      ((simulateQ hashImpl ((knownLocal bytesSample crypto call).run entry)).run cache) := by
  rcases call with ⟨⟨slot, key, decode, request⟩, mode⟩
  cases mode
  · exact sameLaw_refl _
  · exact sameLaw_refl _
  · rcases request with (coin | (hash | input)) | raw
    · exact sameLaw_refl _
    · exact sameLaw_refl _
    · exact sameLaw_seal input entry cache
    · exact sameLaw_refl _

/-- The challenger's source semantics with the two samplers are interchangeable, request by request. -/
theorem sameLaw_source_step (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : Spec.Domain) (state : SourceState) :
    SameLaw ((sourceImpl uniformBytes selected decode crypto key query).run state)
      ((sourceImpl bytesSample selected decode crypto key query).run state) := by
  cases query with
  | inl request => exact sameLaw_refl _
  | inr known =>
      exact sameLaw_bind _ _ _ _ (sameLaw_known crypto known (state.others known.slot) state.cache)
        (fun result => sameLaw_refl _)

/-- **Sampler swap.** The challenger's game with the world's random sampler and with the single-coin sampler are
interchangeable for every three-mode client and selected mode. -/
theorem sameLaw_sourceGame (selected : KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto) {Result : Type}
    (client : OracleComp Spec Result) :
    SameLaw (sourceGame uniformBytes selected decode crypto client) (sourceGame bytesSample selected decode crypto client) :=
  sameLaw_bind _ _ _ _ (sameLaw_refl _) (fun key =>
    sameLaw_simulateQ _ _ (sameLaw_source_step selected decode crypto key) client initialSource)

/-! ### The per-key privacy hop -/

/-- **Replay side.** With the world's samplers, the replay challenger's game has the law of the replay one-key view of
the constructed client with the single-coin sampler. -/
theorem replay_game (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp Spec Bool) :
    𝒟[Prod.fst <$> sourceGame uniformBytes .replay decode crypto client] =
      𝒟[AdaptiveCtxPrivacyGuard.replayView decode crypto (decisionClient bytesSample crypto client)] := by
  rw [sameLaw_fst _ _ (sameLaw_sourceGame .replay decode crypto client), source_view, modeView_replay]

/-- **Random side.** With the world's samplers, the random challenger's game has the law of the IND$ random experiment
behind `randomView` for the constructed client with the single-coin sampler. -/
theorem random_game (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp Spec Bool) :
    𝒟[Prod.fst <$> sourceGame uniformBytes .random decode crypto client] =
      𝒟[AdaptiveCtxPrivacyGuard.randomView decode (decisionClient bytesSample crypto client)] := by
  rw [sameLaw_fst _ _ (sameLaw_sourceGame .random decode crypto client), source_view, modeView_random]

/-- **The per-key privacy hop.** The replay and random challenger games (world samplers) differ by exactly the ordinary
IND$ advantage of the view reduction of the constructed client. -/
theorem hop_advantage (decode : RawDecoder) (crypto : Pqxdh.Crypto) (client : OracleComp Spec Bool) :
    (Prod.fst <$> sourceGame uniformBytes .replay decode crypto client).boolDistAdvantage
        (Prod.fst <$> sourceGame uniformBytes .random decode crypto client) =
      CtxNonceAeadIndDollarValidation.modifiedNonceAeadINDDollarAdvantage crypto
        (AdaptiveCtxPrivacyGuard.viewReduction decode (decisionClient bytesSample crypto client)) := by
  rw [← AdaptiveCtxPrivacyGuard.replay_random_advantage]
  unfold ProbComp.boolDistAdvantage
  rw [replay_game, random_game]

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.card_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.card_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.bytesSample_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.bytesSample_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.bytesSample_evalDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.bytesSample_evalDist

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.randomWith_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.randomWith_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.knownLocal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.knownLocal_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeTarget_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeTarget_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeTarget_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeTarget_random

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeTarget_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeTarget_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.mode_local_from_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.mode_local_from_target

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.mode_public_history_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.mode_public_history_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.mode_forward_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.mode_forward_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.selected_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.selected_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.known_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.known_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.linked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.linked_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.linked_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.linked_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.schedule_interpretation

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.source_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.source_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeView_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeView_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeView_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.modeView_random

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_simulateQ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_simulateQ

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.seal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.seal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_source_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_sourceGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.sameLaw_sourceGame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.replay_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.replay_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.random_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.random_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.hop_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxPrivModes.hop_advantage
