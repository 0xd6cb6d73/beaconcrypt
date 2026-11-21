-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal
import BeaconcryptCore.Computational.LazyOracleDiscard

/-! Observation laws for discarded private suffix-cache accesses. Public hashing and all local histories remain visible in the compared state. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive AdaptiveCtxReplayDictionary
open LazyOracleDiscard

abbrev Local := AdaptiveCtxSharedHash.Local
abbrev State := AdaptiveCtxSharedReplay.Local × CtxRO.QueryCache

/-- Only the private suffix dictionary is focused; local histories and the shared ROM are outside it. -/
def suffixLens : CacheLens CtxSuffixRO State :=
  (StateLens.fst AdaptiveCtxSharedReplay.Local CtxRO.QueryCache).comp
    (StateLens.snd Local CtxSuffixRO.QueryCache)

/-- All state except the private suffix dictionary. -/
def observe (state : State) : Local × CtxRO.QueryCache := (state.1.1, state.2)

theorem observe_set (state : State) (cache : CtxSuffixRO.QueryCache) :
    observe (suffixLens.set state cache) = observe state := rfl

/-- An update to the retained local history leaves both caches in place. -/
def localUpdate (f : Local → Local) : StateT State ProbComp Unit :=
  fun state => pure ((), ((f state.1.1, state.1.2), state.2))

theorem localUpdate_commutes (f : Local → Local) : Commutes suffixLens (localUpdate f) := by
  apply commutes_frame
  intro state cache; simp only [localUpdate, StateT.run, suffixLens, StateLens.comp, StateLens.fst,
    StateLens.snd, map_pure]

/-- Reading the local histories cannot inspect the private suffix cache. -/
def localRead : StateT State ProbComp Local := fun state => pure (state.1.1, state)

theorem localRead_commutes : Commutes suffixLens localRead := by
  apply commutes_frame
  intro state cache; simp only [localRead, StateT.run, suffixLens, StateLens.comp, StateLens.fst,
    StateLens.snd, map_pure]

/-- Actual lazy lookup with the original private-input instrumentation. -/
noncomputable def privateAccess (suffix : Pqxdh.Bytes) : StateT State ProbComp CtxDigest := do
  let digest ← suffixLens.query suffix
  localUpdate fun history => { history with privateInputs := suffix :: history.privateInputs }
  pure digest

theorem privateAccess_commutes (suffix : Pqxdh.Bytes) : Commutes suffixLens (privateAccess suffix) := by
  exact commutes_bind suffixLens (commutes_query suffixLens suffix) fun digest =>
    commutes_bind suffixLens (localUpdate_commutes _) fun _ => commutes_pure suffixLens digest

theorem privateLookup_exact (suffix : Pqxdh.Bytes) (cache : CtxSuffixRO.QueryCache) :
    AdaptiveCtxSharedReplay.privateLookup suffix cache = (CtxSuffixRO.randomOracle suffix).run cache := by
  rw [randomOracle.run_eq]
  cases h : cache suffix <;> simp only [AdaptiveCtxSharedReplay.privateLookup, h]

/-- Replay sealing expressed using only retained history and the actual lazy suffix query. -/
noncomputable def sealing (crypto : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) :
    StateT State ProbComp (Option CtxRomRecord) := do
  let before ← localRead
  if input.nonce ∈ before.usedNonces then pure none else do
    let base := crypto.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext
    let digest ← privateAccess (outerSuffix input.nonce input.context base.2)
    let record : CtxRomRecord := ⟨base.1, base.2, crypto.aeadSeal_tag_length _ _ _ _, digest⟩
    localUpdate fun history => { history with
      usedNonces := input.nonce :: history.usedNonces
      successfulSeals := ⟨input, record⟩ :: history.successfulSeals }
    pure (some record)

theorem seal_commutes (crypto : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) :
    Commutes suffixLens (sealing crypto key input) := by
  apply commutes_bind suffixLens localRead_commutes
  intro history; split
  · exact commutes_pure suffixLens none
  · exact commutes_bind suffixLens (privateAccess_commutes _) fun digest =>
      commutes_bind suffixLens (localUpdate_commutes _) fun _ => commutes_pure suffixLens _

private theorem apply_bind {σ α β : Type} (x : StateT σ ProbComp α)
    (f : α → StateT σ ProbComp β) (state : σ) :
    (x >>= f) state = x state >>= fun r => f r.1 r.2 := rfl

private theorem apply_pure {σ α : Type} (a : α) (state : σ) :
    (pure a : StateT σ ProbComp α) state = pure (a, state) := rfl

private theorem apply_map {σ α β : Type} (f : α → β) (x : StateT σ ProbComp α)
    (state : σ) : (f <$> x) state = Prod.map f id <$> x state := by
  change (x state >>= fun r => pure (f r.1, r.2)) = _
  simp only [bind_pure_comp]; rfl

private theorem hash_uniform_apply {α : Type} (work : ProbComp α) (cache : CtxRO.QueryCache) :
    (simulateQ AdaptiveCtxSharedHash.hashImpl
      (OracleComp.liftComp work AdaptiveCtxSharedHash.HashSpec)) cache =
      (fun answer => (answer, cache)) <$> work := AdaptiveCtxSharedReplay.hash_uniform work cache

set_option backward.isDefEq.respectTransparency false in
/-- The state-factorized sealing program is the existing linked replay seal. -/
theorem sealing_exact (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (state : State) :
    (sealing crypto key input).run state =
      (AdaptiveCtxSharedReplay.linkedImpl decode crypto key (.inl (.inr (.inr input)))).run state := by
  simp only [sealing]
  rw [StateT.run_bind]
  simp only [localRead, StateT.run, pure_bind]
  by_cases used : input.nonce ∈ state.1.1.usedNonces
  · simp only [used, ite_true]
    simp only [AdaptiveCtxSharedReplay.linkedImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      StateT.run, StateT.mk, AdaptiveCtxSharedReplay.localImpl, AdaptiveCtxSharedReplay.localSeal,
      used, ite_true, simulateQ_pure]
    rfl
  · simp only [used, ite_false]
    simp only [apply_bind, apply_map, privateAccess, localUpdate, StateLens.query,
      suffixLens, StateLens.comp, StateLens.fst, StateLens.snd,
      map_pure, bind_pure_comp, Functor.map_map]
    simp only [AdaptiveCtxSharedReplay.linkedImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
      StateT.run, StateT.mk, AdaptiveCtxSharedReplay.localImpl, AdaptiveCtxSharedReplay.localSeal,
      used, ite_false, AdaptiveCtxSharedReplay.localPrivate, bind_pure_comp, simulateQ_map,
      apply_map, hash_uniform_apply, Functor.map_map, privateLookup_exact]
    rfl

/-- Replay raw receive retains its reply and instrumentation but records the discarded lookup point. -/
noncomputable def rawBase (decode : RawDecoder) (raw : Pqxdh.Bytes) :
    StateT State ProbComp (Option Pqxdh.Bytes × Option Pqxdh.Bytes) := fun state =>
  let before := state.1.1
  let counted := { before with rawAttempts := before.rawAttempts + 1 }
  match decode raw with
  | none => pure ((none, none), ((counted, state.1.2), state.2))
  | some target =>
      let suffix := outerSuffix target.nonce target.context target.record.tag
      pure ((replayPlaintext (AdaptiveCtxSharedReplay.install state.1 ∅).ctx target, some suffix),
        (({ counted with privateInputs := suffix :: counted.privateInputs }, state.1.2), state.2))

/-- Only parsed raw receives mark a discarded lookup; other replies are unchanged. -/
noncomputable def pointed (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    (q : ReceiveSpec.Domain) → StateT State ProbComp (ReceiveSpec.Range q × Option Pqxdh.Bytes)
  | .inr raw => rawBase decode raw
  | .inl q => (fun answer => (answer, none)) <$>
      AdaptiveCtxSharedReplay.linkedImpl decode crypto key (.inl q)

theorem rawBase_commutes (decode : RawDecoder) (raw : Pqxdh.Bytes) :
    Commutes suffixLens (rawBase decode raw) := by
  apply commutes_frame
  intro state cache
  cases parsed : decode raw <;>
    simp only [rawBase, StateT.run, suffixLens, StateLens.comp, StateLens.fst, StateLens.snd,
      parsed, map_pure]
  rfl

/-- Reinstalling the discarded completion gives exactly the existing raw replay step. -/
theorem raw_factor (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (state : State) :
    (AdaptiveCtxSharedReplay.linkedImpl decode crypto key (.inr raw)).run state =
      ((rawBase decode raw).run state >>= fun r =>
        (r.1.1, ·) <$> suffixLens.completeOpt r.1.2 r.2) := by
  cases parsed : decode raw with
  | none =>
      simp only [AdaptiveCtxSharedReplay.linkedImpl, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, StateT.run, StateT.mk, AdaptiveCtxSharedReplay.localImpl,
        AdaptiveCtxSharedReplay.localRaw, parsed, simulateQ_pure, rawBase,
        StateLens.completeOpt, pure_bind, map_pure]
      rfl
  | some target =>
      simp only [AdaptiveCtxSharedReplay.linkedImpl, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, StateT.run, StateT.mk, AdaptiveCtxSharedReplay.localImpl,
        AdaptiveCtxSharedReplay.localRaw, parsed, AdaptiveCtxSharedReplay.localPrivate,
        bind_pure_comp, simulateQ_map, apply_map, hash_uniform_apply, Functor.map_map,
        rawBase, pure_bind, StateLens.completeOpt, StateLens.complete, complete,
        suffixLens, StateLens.comp, StateLens.fst, StateLens.snd, privateLookup_exact]
      rfl

/-- Coins, public hashing, and sealing all commute with a hidden completion of the private suffix cache. -/
theorem linked_nonraw_commutes (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (q : (unifSpec + CtxAdversarySpec).Domain) :
    Commutes suffixLens (AdaptiveCtxSharedReplay.linkedImpl decode crypto key (.inl q)) := by
  cases q with
  | inl coin =>
      apply commutes_frame
      intro state cache
      simp only [AdaptiveCtxSharedReplay.linkedImpl, QueryImpl.flattenStateT,
        QueryImpl.mapStateTBase, StateT.run, StateT.mk, AdaptiveCtxSharedReplay.localImpl,
        simulateQ_map, apply_map,
        bind_pure_comp, Functor.map_map, suffixLens, StateLens.comp, StateLens.fst, StateLens.snd]
      rfl
  | inr request =>
      cases request with
      | inl hash =>
          apply commutes_frame
          intro state cache
          simp only [AdaptiveCtxSharedReplay.linkedImpl, QueryImpl.flattenStateT,
            QueryImpl.mapStateTBase, StateT.run, StateT.mk, AdaptiveCtxSharedReplay.localImpl,
            simulateQ_map, apply_map,
            bind_pure_comp, Functor.map_map, suffixLens, StateLens.comp, StateLens.fst, StateLens.snd]
          rfl
      | inr input =>
          have eq : AdaptiveCtxSharedReplay.linkedImpl decode crypto key (.inl (.inr (.inr input))) =
              sealing crypto key input := by
            funext state
            exact (sealing_exact decode crypto key input state).symm
          rw [eq]
          exact seal_commutes crypto key input

/-- The factorization includes every query kind and preserves exact replies. -/
theorem pointed_factor (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (q : ReceiveSpec.Domain) (state : State) :
    LawEq ((AdaptiveCtxSharedReplay.linkedImpl decode crypto key q).run state)
      ((pointed decode crypto key q).run state >>= fun r =>
        (r.1.1, ·) <$> suffixLens.completeOpt r.1.2 r.2) := by
  apply LawEq.of_eq
  cases q with
  | inr raw => exact raw_factor decode crypto key raw state
  | inl q =>
      simp only [pointed, StateT.run_map, bind_map_left, StateLens.completeOpt, map_pure]
      simpa only [Prod.map_def, id_eq] using
        (bind_pure ((AdaptiveCtxSharedReplay.linkedImpl decode crypto key (.inl q)).run state)).symm

/-- Every erased step commutes with postponed private-cache completion, including later sealing. -/
theorem pointed_commutes (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (q : ReceiveSpec.Domain) : Commutes suffixLens (Prod.fst <$> pointed decode crypto key q) := by
  cases q with
  | inr raw => exact commutes_map suffixLens Prod.fst (rawBase_commutes decode raw)
  | inl q =>
      exact commutes_map suffixLens Prod.fst
        (commutes_map suffixLens (fun answer => (answer, none))
          (linked_nonraw_commutes decode crypto key q))

/-- Replay with discarded raw lookup draws removed; every reply and instrumented input is retained. -/
noncomputable def erasedReplay (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl ReceiveSpec (StateT State ProbComp) :=
  fun q => Prod.fst <$> pointed decode crypto key q

/-- Full adaptive replay equality after forgetting only the private suffix dictionary. The shared public ROM, seal history, nonces, raw-attempt count, and private/public input logs remain observed. -/
theorem replay_observation (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp ReceiveSpec Result) (state : State) :
    LawEq (Prod.map id observe <$>
      (simulateQ (AdaptiveCtxSharedReplay.linkedImpl decode crypto key) client).run state)
      (Prod.map id observe <$> (simulateQ (erasedReplay decode crypto key) client).run state) := by
  exact discard_erase_proj suffixLens (AdaptiveCtxSharedReplay.linkedImpl decode crypto key)
    (pointed decode crypto key) (pointed_factor decode crypto key) (pointed_commutes decode crypto key)
    observe observe_set client state

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.observe_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.observe_set

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.localUpdate_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.localUpdate_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.localRead_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.localRead_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.privateAccess_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.privateAccess_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.privateLookup_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.privateLookup_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.seal_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.seal_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.sealing_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.sealing_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.rawBase_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.rawBase_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.raw_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.raw_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.linked_nonraw_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.linked_nonraw_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.pointed_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.pointed_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.pointed_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.pointed_commutes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.replay_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCache.replay_observation
