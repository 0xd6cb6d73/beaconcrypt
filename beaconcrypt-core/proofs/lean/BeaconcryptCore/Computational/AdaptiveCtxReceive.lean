import BeaconcryptCore.Computational.AdaptiveRawNonceAead
import BeaconcryptCore.Computational.CtxUnclaimedAcceptance
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# Adaptive CTX receive with a retained private suffix dictionary

The key-free wrapper implements public hash calls, honest CTX seals, and arbitrary raw opening requests. Every well-formed raw request performs its private suffix lookup before testing the commitment. Failed commitment and opening checks retain that lookup's cache effect. The base opening request is the original raw input, parsed by the same public decoder and projected to the unchanged nonce, associated data, body, and tag.

This module begins the adaptive CTX lift in the independent-public-hash world. It does not identify the independent public hash with the canonical shared ROM, discard alias-commitment guesses, or instantiate ratchet state and the native frame decoder.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveCtxReceive

open CtxRomAuth CtxSplitCache CtxIndependentTags CtxNonceAeadIntCtxt
open AdaptiveRawNonceAead

abbrev RawDecoder := Pqxdh.Bytes → Option CtxUnclaimedAcceptance.Target
abbrev ReceiveSpec := (unifSpec + CtxAdversarySpec) + RawOpenSpec

instance : unifSpec ⊂ₒ AdaptiveSpec :=
  SubSpec.trans (inferInstance : unifSpec ⊂ₒ ModifiedNonceAeadAdversarySpec)
    (inferInstance : ModifiedNonceAeadAdversarySpec ⊂ₒ AdaptiveSpec)

/-- Base verification sees the exact parsed ciphertext and never a claimed or secretly recovered plaintext. -/
def baseTarget (target : CtxUnclaimedAcceptance.Target) : ModifiedNonceAeadForgery :=
  ⟨target.nonce, target.context.ad.bytes, CtxNonceAeadIntCtxt.CtxRomRecord.toModifiedNonceAeadCiphertext target.record⟩

def baseDecoder (decode : RawDecoder) : AdaptiveRawNonceAead.RawDecoder :=
  fun raw => (decode raw).map baseTarget

/-- Complete wrapper state, including every raw slot and every attempted private suffix lookup. -/
structure ReceiveState where
  ctx : CtxIndependentTagState
  rawAttempts : ℕ
  privateInputs : List Pqxdh.Bytes

def initialState : ReceiveState := ⟨emptyCtxIndependentTagState, 0, []⟩

/-- Public queries use their complete-input dictionary and preserve all existing histories. -/
noncomputable def publicStep (query : CtxRO.Domain) (state : ReceiveState) :
    OracleComp AdaptiveSpec (CtxDigest × ReceiveState) := do
  let (digest, ctx) ← OracleComp.liftComp ((ctxIndependentPublicOracle query).run state.ctx) AdaptiveSpec
  pure (digest, { state with ctx := ctx })

/-- The private dictionary is addressed by exactly the production suffix, including its repeated sequence/session fields. -/
noncomputable def privateStep (suffix : Pqxdh.Bytes) (state : ReceiveState) :
    OracleComp AdaptiveSpec (CtxDigest × ReceiveState) := do
  let (digest, cache) ← OracleComp.liftComp (ctxKeyFreeSuffixStep suffix state.ctx.cache) AdaptiveSpec
  pure (digest, ⟨{ state.ctx with cache := cache }, state.rawAttempts, suffix :: state.privateInputs⟩)

/-- Ordinary nonce-rejecting encryption supplies the retained body/tag; CTX adds a lookup in the same private dictionary used by raw attempts. -/
noncomputable def sealStep (input : CtxSealInput) (state : ReceiveState) :
    OracleComp AdaptiveSpec (Option CtxRomRecord × ReceiveState) := do
  let base ← AdaptiveSpec.query (.inl (.inr (CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput input)))
  match base with
  | none => pure (none, state)
  | some ciphertext =>
    let (commit, next) ← privateStep (outerSuffix input.nonce input.context ciphertext.tag) state
    let record : CtxRomRecord := ⟨ciphertext.body, ciphertext.tag, ciphertext.tagLength, commit⟩
    pure (some record, { next with ctx := next.ctx.addSeal ⟨input, record⟩ next.ctx.cache })

/-- A rejected commitment still changes the cache. Actual optional plaintext, when requested, is returned directly from the primitive challenger. -/
noncomputable def rawStep (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : ReceiveState) :
    OracleComp AdaptiveSpec (Option Pqxdh.Bytes × ReceiveState) := do
  let counted := { state with rawAttempts := state.rawAttempts + 1 }
  match decode raw with
  | none => pure (none, counted)
  | some target =>
    let (expected, next) ← privateStep (outerSuffix target.nonce target.context target.record.tag) counted
    if target.record.commit = expected then
      let plaintext ← AdaptiveSpec.query (.inr raw)
      pure (plaintext, next)
    else pure (none, next)

/-- The reduction knows no hidden AEAD key and has no native opening operation. -/
noncomputable def reductionImpl (decode : RawDecoder) :
    QueryImpl ReceiveSpec (StateT ReceiveState (OracleComp AdaptiveSpec)) :=
  fun query state => match query with
  | .inl (.inl coin) => do
      let answer ← AdaptiveSpec.query (.inl (.inl coin))
      pure (answer, state)
  | .inl (.inr (.inl query)) => publicStep query state
  | .inl (.inr (.inr input)) => sealStep input state
  | .inr raw => rawStep decode raw state

/-- The full adversary continuation retains the private dictionaries and instrumentation as its output. -/
noncomputable def wrapped {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) : OracleComp AdaptiveSpec (Result × ReceiveState) :=
  (simulateQ (reductionImpl decode) adversary).run initialState

/-- Actual base opening is available only inside the linked challenger. -/
noncomputable def linkedGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (Result × (ReceiveState × (AdaptiveRawNonceAead.ReceiveState × Bool))) :=
  (simulateQ (QueryImpl.Stateful.link (reductionImpl decode) (adaptiveImpl real (baseDecoder decode) c key)) adversary).run
    (initialState, AdaptiveRawNonceAead.initialState, false)

/-- Reassociating the two retained state records discards no private cache, transcript, or instrument. -/
def retainBoth {Result : Type}
    (result : (Result × ReceiveState) × (AdaptiveRawNonceAead.ReceiveState × Bool)) :
    Result × (ReceiveState × (AdaptiveRawNonceAead.ReceiveState × Bool)) :=
  (result.1.1, result.1.2, result.2)

/-- Linking the wrapper preserves the entire evaluated adaptive execution, including both private states. -/
theorem linkedGame_eq (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    linkedGame real decode c key adversary =
      retainBoth <$> adaptiveGame real (baseDecoder decode) c key (wrapped decode adversary) := by
  exact QueryImpl.Stateful.simulateQ_link_run (reductionImpl decode)
    (adaptiveImpl real (baseDecoder decode) c key) adversary initialState
    (AdaptiveRawNonceAead.initialState, false)

/-- Each raw source request has its own counted slot. -/
def IsRawQuery : ReceiveSpec.Domain → Prop
  | .inr _ => True
  | .inl _ => False

instance : DecidablePred IsRawQuery
  | .inr _ => isTrue trivial
  | .inl _ => isFalse id

/-- Sampling a private/public digest makes no raw opening request. -/
theorem liftProbability_no_raw {Result : Type} (work : ProbComp Result) :
    (OracleComp.liftComp work AdaptiveSpec).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := AdaptiveSpec) (p := fun _ => False)
    (hpq := fun query => by simp [AdaptiveRawNonceAead.IsRawQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false work 0)

/-- A private suffix lookup is internal randomness only, including on a cache miss. -/
theorem privateStep_no_raw (suffix : Pqxdh.Bytes) (state : ReceiveState) :
    (privateStep suffix state).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery 0 := by
  simpa only [privateStep, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    liftProbability_no_raw (ctxKeyFreeSuffixStep suffix state.ctx.cache)

/-- Public hash requests never ask the challenger to open a ciphertext. -/
theorem publicStep_no_raw (query : CtxRO.Domain) (state : ReceiveState) :
    (publicStep query state).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery 0 := by
  simpa only [publicStep, bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    liftProbability_no_raw ((ctxIndependentPublicOracle query).run state.ctx)

/-- Honest sealing never asks for a decryption answer; even a reused nonce adds no raw attempt. -/
theorem sealStep_no_raw (input : CtxSealInput) (state : ReceiveState) :
    (sealStep input state).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery 0 := by
  unfold sealStep
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl id, ?_⟩
  intro answer
  cases answer with
  | none => trivial
  | some ciphertext =>
      simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff,
        ite_eq_right (show ¬ AdaptiveRawNonceAead.IsRawQuery (.inl (.inr
          (CtxNonceAeadIntCtxt.CtxSealInput.toModifiedNonceAeadSealInput input))) from id)] using
        privateStep_no_raw (outerSuffix input.nonce input.context ciphertext.tag) state

/-- Every source raw attempt invokes at most one primitive opening, after its complete private hash lookup. -/
theorem rawStep_raw_query_bound (decode : RawDecoder) (raw : Pqxdh.Bytes) (state : ReceiveState) :
    (rawStep decode raw state).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery 1 := by
  cases parsed : decode raw with
  | none => simp [rawStep, parsed]
  | some target =>
      simp only [rawStep, parsed]
      refine OracleComp.isQueryBoundP_bind (n := 0) (m := 1) (privateStep_no_raw _ _) ?_
      rintro ⟨expected, next⟩ _
      split
      · simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
          (OracleComp.isQueryBoundP_query_iff (spec := AdaptiveSpec)
            (p := AdaptiveRawNonceAead.IsRawQuery) (.inr raw) 1).mpr (by intro _; decide)
      · trivial

/-- All source query classes retain their exact raw-opening cost, including forwarded private randomness. -/
theorem reductionImpl_raw_query_bound_step (decode : RawDecoder)
    (query : ReceiveSpec.Domain) (state : ReceiveState) :
    ((reductionImpl decode query).run state).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery
      (if IsRawQuery query then 1 else 0) := by
  cases query with
  | inl query =>
    cases query with
    | inl coin =>
      simp only [reductionImpl, StateT.run, IsRawQuery, if_false,
        bind_pure_comp, OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff (spec := AdaptiveSpec)
        (p := AdaptiveRawNonceAead.IsRawQuery) (.inl (.inl coin)) 0).mpr (by simp [AdaptiveRawNonceAead.IsRawQuery])
    | inr query =>
      cases query with
      | inl publicQuery => exact publicStep_no_raw publicQuery state
      | inr input => exact sealStep_no_raw input state
  | inr raw => exact rawStep_raw_query_bound decode raw state

/-- Counting every source raw slot bounds every delegated opening; malformed and commitment-rejected requests remain counted by the source. -/
theorem wrapped_raw_query_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    (wrapped decode adversary).IsQueryBoundP AdaptiveRawNonceAead.IsRawQuery count :=
  bounded.simulateQ_run_StateT_of_step (reductionImpl_raw_query_bound_step decode) initialState

/-- One independent hidden key is sampled by the challenger, outside the key-free wrapper. -/
noncomputable def uniformLinkedGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    ProbComp (Result × (ReceiveState × (AdaptiveRawNonceAead.ReceiveState × Bool))) := do
  let key ← $ᵗ CtxKey
  linkedGame real decode c key adversary

/-- Uniform-key linking preserves both entire private states, as well as the public result. -/
theorem uniformLinkedGame_eq (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp ReceiveSpec Result) :
    uniformLinkedGame real decode c adversary =
      retainBoth <$> uniformAdaptiveGame real (baseDecoder decode) c (wrapped decode adversary) := by
  simp only [uniformLinkedGame, uniformAdaptiveGame, linkedGame_eq, map_bind]

/-- The adaptive independent-public-hash CTX wrapper can replace actual base openings by exact encryption-log replies at the stated ordinary integrity cost. -/
theorem uniformLinkedGame_distance_le_intctxt_sum (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) {Result : Type}
    (adversary : OracleComp ReceiveSpec Result) (count : ℕ)
    (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    ENNReal.ofReal (tvDist (uniformLinkedGame true decode c adversary)
      (uniformLinkedGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c
          (indexedReduction (baseDecoder decode) fallback (wrapped decode adversary) index) := by
  rw [uniformLinkedGame_eq, uniformLinkedGame_eq]
  exact (ENNReal.ofReal_le_ofReal (tvDist_map_le retainBoth _ _)).trans
    (uniformAdaptiveGame_distance_le_intctxt_sum (baseDecoder decode) c fallback
      (wrapped decode adversary) count (wrapped_raw_query_bound decode adversary count bounded))

end BeaconcryptCore.Computational.AdaptiveCtxReceive

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReceive.linkedGame_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReceive.linkedGame_eq

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxReceive.uniformLinkedGame_distance_le_intctxt_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxReceive.uniformLinkedGame_distance_le_intctxt_sum
