-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheCompiler

/-! Cache preservation and exact fresh commitment sampling in the erased endpoints. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh
open CtxRomAuth CtxSplitCache AdaptiveCtxReceive LazyOracleDiscard
open PqxdhRecordFactsPrivateCache
open PqxdhRecordLiftIdeal (KeyMode)

private theorem apply_map {σ α β : Type} (f : α → β) (work : StateT σ ProbComp α)
    (state : σ) : (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun r => pure (f r.1, r.2)) = _
  simp only [bind_pure_comp]; rfl

/-- An erased raw step retains its whole private suffix dictionary regardless of parser success. -/
theorem raw_cache (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (mode : KeyMode)
    (raw : Pqxdh.Bytes) (state : State) :
    (fun result => result.2.1.2) <$>
      (PqxdhRecordFactsPrivateCacheRandom.erased decode crypto key mode (.inr raw)).run state =
      pure state.1.2 := by
  cases parsed : decode raw <;>
    simp only [PqxdhRecordFactsPrivateCacheRandom.erased,
      PqxdhRecordFactsPrivateCacheRandom.modePointed, StateT.run, apply_map, rawBase, parsed, map_pure, Prod.map, id_eq]

private theorem apply_bind {σ α β : Type} (work : StateT σ ProbComp α)
    (next : α → StateT σ ProbComp β) (state : σ) :
    (work >>= next) state = (work state >>= fun result => next result.1 result.2) := rfl

private theorem apply_pure {σ α : Type} (value : α) (state : σ) :
    (pure value : StateT σ ProbComp α) state = pure (value, state) := rfl

/-- A missing private suffix samples one complete uniform digest and preserves the exact input log and all unrelated state. -/
theorem privateAccess_fresh (suffix : Pqxdh.Bytes) (state : State) (missing : state.1.2 suffix = none) :
    (privateAccess suffix).run state =
      (fun digest : CtxDigest => (digest,
        (({ state.1.1 with privateInputs := suffix :: state.1.1.privateInputs },
          state.1.2.cacheQuery suffix digest), state.2))) <$> ($ᵗ CtxDigest) := by
  simp only [privateAccess, StateT.run, apply_bind, apply_pure, localUpdate,
    StateLens.query, suffixLens, StateLens.comp, StateLens.fst, StateLens.snd]
  rw [show CtxSuffixRO.randomOracle suffix state.1.2 = _ from query_of_none missing]
  simp only [bind_pure_comp, Functor.map_map, map_pure]

/-- The literal successful-seal poststate for one ciphertext body, tag and commitment. -/
def sealResult (input : CtxSealInput) (body tag : Pqxdh.Bytes) (width : tag.length = 16)
    (digest : CtxDigest) (state : State) : Option CtxRomRecord × State :=
  let record : CtxRomRecord := ⟨body, tag, width, digest⟩
  let suffix := outerSuffix input.nonce input.context tag
  (some record, (({ state.1.1 with
    usedNonces := input.nonce :: state.1.1.usedNonces
    successfulSeals := ⟨input, record⟩ :: state.1.1.successfulSeals
    privateInputs := suffix :: state.1.1.privateInputs }, state.1.2.cacheQuery suffix digest), state.2))

/-- At a missing suffix and unused nonce, replay sealing samples a complete fresh digest after forming the real ciphertext; its entire poststate is retained. -/
theorem sealing_fresh (crypto : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) (state : State)
    (unused : input.nonce ∉ state.1.1.usedNonces)
    (missing : state.1.2 (outerSuffix input.nonce input.context
      (crypto.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext).2) = none) :
    (sealing crypto key input).run state =
      (fun digest : CtxDigest => sealResult input
        (crypto.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext).1
        (crypto.aeadSeal key.toList input.nonce.toList input.context.ad.bytes input.plaintext).2
        (crypto.aeadSeal_tag_length _ _ _ _) digest state) <$> ($ᵗ CtxDigest) := by
  simp only [sealing, StateT.run, apply_bind, localRead, pure_bind, unused, ite_false]
  rw [show privateAccess _ state = _ from privateAccess_fresh _ state missing]
  simp only [localUpdate, apply_pure, map_pure, bind_pure_comp, Functor.map_map, sealResult]

/-- Random sealing samples body, then tag, then one complete fresh digest; the whole poststate is kept in the same order. -/
theorem randomSealing_fresh (input : CtxSealInput) (state : State)
    (unused : input.nonce ∉ state.1.1.usedNonces)
    (missing : ∀ tag : FixedBytes 16, state.1.2 (outerSuffix input.nonce input.context tag.toList) = none) :
    (PqxdhRecordFactsPrivateCacheRandom.randomSealing input).run state =
      (do
        let body ← $ᵗ (FixedBytes input.plaintext.length)
        let tag ← $ᵗ (FixedBytes 16)
        let digest ← $ᵗ CtxDigest
        pure (sealResult input body.toList tag.toList tag.toList_length digest state)) := by
  simp only [PqxdhRecordFactsPrivateCacheRandom.randomSealing, StateT.run, apply_bind,
    localRead, pure_bind, unused, ite_false, PqxdhRecordFactsPrivateCacheRandom.draw,
    bind_map_left]
  refine bind_congr fun body => ?_
  refine bind_congr fun tag => ?_
  rw [show privateAccess _ state = _ from privateAccess_fresh _ state (missing tag)]
  simp only [localUpdate, apply_pure, map_pure, bind_pure_comp, Functor.map_map, sealResult]

end BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.raw_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.raw_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.privateAccess_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.privateAccess_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.sealing_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.sealing_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.randomSealing_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsPrivateCacheFresh.randomSealing_fresh
