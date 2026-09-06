import BeaconcryptCore.Computational.AdaptiveCtxDirectReplay

/-!
# Complete independent random-source query accounting

The direct source preserves sealing, arbitrary finite uniform-oracle and submitted-plaintext byte budgets. Its complete random sealing interpretation samples ciphertext bodies and tags but no record key. These query caps do not claim a compiled local-runtime bound.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation CtxNonceAeadIndDollar
open AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation AdaptiveCtxDirectReplay
open AdaptiveCtxPlaintextQueryBounds AdaptiveCtxPrivacyQueryBounds NonceAeadRandomQueryBounds

/-- The independent ordinary source forwards the same number of actual sealing requests, with no validation addition. -/
theorem directClient_seal_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qSeal : ℕ)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal) :
    (directClient decode adversary).IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal := by
  rw [← sourceClient_direct decode adversary, OracleComp.isQueryBoundP_map_iff]
  exact sourceClient_seal_bound decode (guardedClient decode adversary) qSeal
    (guardedClient_query_bound decode adversary _ qSeal bounded)

/-- Actual public/private misses each draw sixty-four bytes; every original finite uniform request is also forwarded. -/
theorem directClient_uniform_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (directClient decode adversary).IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery
      (qCoins + 64 * (qHash + qSeal + qRaw)) := by
  rw [← sourceClient_direct decode adversary, OracleComp.isQueryBoundP_map_iff]
  exact sourceClient_uniform_bound decode (guardedClient decode adversary) qCoins qHash qSeal qRaw
    (guardedClient_query_bound decode adversary _ qCoins coinBound)
    (guardedClient_query_bound decode adversary _ qHash hashBound)
    (guardedClient_query_bound decode adversary _ qSeal sealBound)
    (guardedClient_query_bound decode adversary _ qRaw rawBound)

/-- The independent source submits exactly the same bounded plaintext payload, including every adaptive possible continuation. -/
theorem directClient_plaintext_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qBytes : ℕ)
    (bounded : SourcePlaintextBound adversary qBytes) :
    PlaintextBound (directClient decode adversary) qBytes := by
  rw [← sourceClient_direct decode adversary, PlaintextBound, OracleComp.isQueryBound_map_iff]
  exact sourceClient_plaintext_bound decode (guardedClient decode adversary) qBytes
    (guardedClient_plaintext_bound decode adversary qBytes bounded)

/-- The complete independent random source includes all source coins, cache misses and random ciphertext bytes/tags, without generating a record key. -/
theorem directRandomGame_uniform_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qBytes qCoins qHash qSeal qRaw : ℕ)
    (bytesBound : SourcePlaintextBound adversary qBytes)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (directRandomGame decode adversary).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * qSeal) :=
  randomRun_uniform_bound (directClient decode adversary) qBytes qSeal
    (qCoins + 64 * (qHash + qSeal + qRaw))
    (directClient_plaintext_bound decode adversary qBytes bytesBound)
    (directClient_seal_bound decode adversary qSeal sealBound)
    (directClient_uniform_bound decode adversary qCoins qHash qSeal qRaw
      coinBound hashBound sealBound rawBound) emptyModifiedNonceAeadHandlerState

/-- Dropping only the retained private terminal state preserves the complete random-source sampling cap. -/
theorem directRandomView_uniform_bound (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Bool) (qBytes qCoins qHash qSeal qRaw : ℕ)
    (bytesBound : SourcePlaintextBound adversary qBytes)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (directRandomView decode adversary).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * qSeal) := by
  simpa only [directRandomView, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    directRandomGame_uniform_bound decode adversary qBytes qCoins qHash qSeal qRaw
      bytesBound coinBound hashBound sealBound rawBound

end BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directClient_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directClient_seal_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directClient_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directClient_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directClient_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directClient_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directRandomGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directRandomGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directRandomView_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxDirectReplayQueryBounds.directRandomView_uniform_bound
