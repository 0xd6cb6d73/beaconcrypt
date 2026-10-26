-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache

/-! The private-cache observation law for the random-seal endpoint. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive AdaptiveCtxReplayDictionary
open LazyOracleDiscard PqxdhRecordFactsPrivateCache

/-- The existing one-key mode linked to its actual shared hash interpreter. -/
noncomputable def linked (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : PqxdhRecordLiftIdeal.KeyMode) : QueryImpl ReceiveSpec (StateT State ProbComp) :=
  (AdaptiveCtxSharedHash.hashImpl.mapStateTBase
    (PqxdhRecordLiftIdeal.keyImpl decode crypto key mode)).flattenStateT

/-- A probability-program draw preserves all state. -/
noncomputable def draw {α : Type} (work : ProbComp α) : StateT State ProbComp α :=
  fun state => (fun answer => (answer, state)) <$> work

theorem draw_commutes {α : Type} (work : ProbComp α) : Commutes suffixLens (draw work) := by
  apply commutes_frame
  intro state cache
  simp only [draw, StateT.run, Functor.map_map]

/-- The actual random-seal body/tag sampling order followed by the lazy suffix lookup. -/
noncomputable def randomSealing (input : CtxSealInput) : StateT State ProbComp (Option CtxRomRecord) := do
  let before ← localRead
  if input.nonce ∈ before.usedNonces then pure none else do
    let body ← draw ($ᵗ (FixedBytes input.plaintext.length))
    let tag ← draw ($ᵗ (FixedBytes 16))
    let digest ← privateAccess (outerSuffix input.nonce input.context tag.toList)
    let record : CtxRomRecord := ⟨body.toList, tag.toList, tag.toList_length, digest⟩
    localUpdate fun history => { history with
      usedNonces := input.nonce :: history.usedNonces
      successfulSeals := ⟨input, record⟩ :: history.successfulSeals }
    pure (some record)

theorem randomSeal_commutes (input : CtxSealInput) : Commutes suffixLens (randomSealing input) := by
  apply commutes_bind suffixLens localRead_commutes
  intro history; split
  · exact commutes_pure suffixLens none
  · exact commutes_bind suffixLens (draw_commutes _) fun body =>
      commutes_bind suffixLens (draw_commutes _) fun tag =>
        commutes_bind suffixLens (privateAccess_commutes _) fun digest =>
          commutes_bind suffixLens (localUpdate_commutes _) fun _ => commutes_pure suffixLens _

private theorem apply_bind {σ α β : Type} (x : StateT σ ProbComp α)
    (f : α → StateT σ ProbComp β) (state : σ) :
    (x >>= f) state = x state >>= fun r => f r.1 r.2 := rfl

private theorem apply_map {σ α β : Type} (f : α → β) (x : StateT σ ProbComp α)
    (state : σ) : (f <$> x) state = Prod.map f id <$> x state := by
  change (x state >>= fun r => pure (f r.1, r.2)) = _
  simp only [bind_pure_comp]; rfl

private theorem apply_pure {σ α : Type} (a : α) (state : σ) :
    (pure a : StateT σ ProbComp α) state = pure (a, state) := rfl

private theorem hash_uniform_apply {α : Type} (work : ProbComp α) (cache : CtxRO.QueryCache) :
    (simulateQ AdaptiveCtxSharedHash.hashImpl
      (OracleComp.liftComp work AdaptiveCtxSharedHash.HashSpec)) cache =
      (fun answer => (answer, cache)) <$> work := AdaptiveCtxSharedReplay.hash_uniform work cache

/-- Equality with the existing random endpoint, preserving body/tag/query order and complete state. -/
theorem randomSealing_exact (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : State) :
    (randomSealing input).run state = (linked decode crypto key .random (.inl (.inr (.inr input)))).run state := by
  simp only [randomSealing]
  rw [StateT.run_bind]
  simp only [localRead, StateT.run, pure_bind]
  by_cases used : input.nonce ∈ state.1.1.usedNonces
  · simp only [used, ite_true, linked, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      StateT.run, StateT.mk, PqxdhRecordLiftIdeal.keyImpl, PqxdhRecordLiftIdeal.randomImpl,
      PqxdhRecordLiftIdeal.randomSeal, simulateQ_pure]
    rfl
  · simp only [used, ite_false, apply_bind, apply_map, draw, privateAccess, localUpdate,
      StateLens.query, suffixLens, StateLens.comp, StateLens.fst, StateLens.snd,
      bind_map_left, map_pure, bind_pure_comp, Functor.map_map]
    simp only [linked, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk,
      PqxdhRecordLiftIdeal.keyImpl, PqxdhRecordLiftIdeal.randomImpl, PqxdhRecordLiftIdeal.randomSeal,
      used, ite_false, AdaptiveCtxSharedReplay.localPrivate, bind_pure_comp, simulateQ_map,
      simulateQ_bind, apply_bind, apply_map, hash_uniform_apply, Functor.map_map,
      bind_map_left, privateLookup_exact]
    simp only [map_bind, Functor.map_map]
    rfl

/-- Replay mode links to the existing replay endpoint literally. -/
theorem linked_replay (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    linked decode crypto key .replay = AdaptiveCtxSharedReplay.linkedImpl decode crypto key := rfl

/-- The random endpoint's non-raw steps commute with a private cache completion. -/
theorem random_nonraw_commutes (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (q : (unifSpec + CtxAdversarySpec).Domain) :
    Commutes suffixLens (linked decode crypto key .random (.inl q)) := by
  cases q with
  | inl coin => exact linked_nonraw_commutes decode crypto key (.inl coin)
  | inr request =>
      cases request with
      | inl hash => exact linked_nonraw_commutes decode crypto key (.inr (.inl hash))
      | inr input =>
          have eq : linked decode crypto key .random (.inl (.inr (.inr input))) = randomSealing input := by
            funext state
            exact (randomSealing_exact decode crypto key input state).symm
          rw [eq]
          exact randomSeal_commutes input

/-- Common replay/random factorization, marking only discarded raw suffix lookups. -/
noncomputable def modePointed (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : PqxdhRecordLiftIdeal.KeyMode) :
    (q : ReceiveSpec.Domain) → StateT State ProbComp (ReceiveSpec.Range q × Option Pqxdh.Bytes)
  | .inr raw => rawBase decode raw
  | .inl q => (fun answer => (answer, none)) <$> linked decode crypto key mode (.inl q)

/-- The factorization covers replay and random endpoints, preserving the complete step. -/
theorem mode_factor (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : PqxdhRecordLiftIdeal.KeyMode) (supported : mode ≠ .real)
    (q : ReceiveSpec.Domain) (state : State) :
    LawEq ((linked decode crypto key mode q).run state)
      ((modePointed decode crypto key mode q).run state >>= fun r =>
        (r.1.1, ·) <$> suffixLens.completeOpt r.1.2 r.2) := by
  apply LawEq.of_eq
  cases q with
  | inr raw =>
      cases mode with
      | real => exact False.elim (supported rfl)
      | replay => exact raw_factor decode crypto key raw state
      | random => exact raw_factor decode crypto key raw state
  | inl q =>
      simp only [modePointed, StateT.run_map, bind_map_left, StateLens.completeOpt, map_pure]
      simpa only [Prod.map_def, id_eq] using
        (bind_pure ((linked decode crypto key mode (.inl q)).run state)).symm

/-- Every erased step in either supported mode commutes with postponed completion. -/
theorem mode_commutes (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : PqxdhRecordLiftIdeal.KeyMode) (supported : mode ≠ .real) (q : ReceiveSpec.Domain) :
    Commutes suffixLens (Prod.fst <$> modePointed decode crypto key mode q) := by
  cases q with
  | inr raw => exact commutes_map suffixLens Prod.fst (rawBase_commutes decode raw)
  | inl q =>
      apply commutes_map suffixLens Prod.fst
      apply commutes_map suffixLens (fun answer => (answer, none))
      cases mode with
      | real => exact False.elim (supported rfl)
      | replay => exact linked_nonraw_commutes decode crypto key q
      | random => exact random_nonraw_commutes decode crypto key q

/-- Replay or random interpretation with discarded raw cache completions omitted. -/
noncomputable def erased (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : PqxdhRecordLiftIdeal.KeyMode) : QueryImpl ReceiveSpec (StateT State ProbComp) :=
  fun q => Prod.fst <$> modePointed decode crypto key mode q

/-- Full adaptive observation equality for either supported endpoint; it erases only the private suffix dictionary, never shared ROM or local histories. -/
theorem mode_observation (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : PqxdhRecordLiftIdeal.KeyMode) (supported : mode ≠ .real)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (state : State) :
    LawEq (Prod.map id observe <$> (simulateQ (linked decode crypto key mode) client).run state)
      (Prod.map id observe <$> (simulateQ (erased decode crypto key mode) client).run state) := by
  exact discard_erase_proj suffixLens (linked decode crypto key mode)
    (modePointed decode crypto key mode) (mode_factor decode crypto key mode supported)
    (mode_commutes decode crypto key mode supported) observe observe_set client state

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.draw_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.draw_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.randomSeal_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.randomSeal_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.randomSealing_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.randomSealing_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.linked_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.linked_replay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.random_nonraw_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.random_nonraw_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.mode_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.mode_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.mode_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.mode_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.mode_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheRandom.mode_observation
