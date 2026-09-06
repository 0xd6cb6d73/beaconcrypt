import BeaconcryptCore.Computational.AdaptiveCtxPrivacyGuard

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation CtxComputationalSecurity
open AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation
open AdaptiveCtxPlaintextQueryBounds NonceAeadRandomQueryBounds

/-- The ciphertext-view reduction forwards the original sealing cap with no additional validation seal. -/
theorem viewReduction_seal_bound (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool)
    (qSeal : ℕ) (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal) :
    (viewReduction decode adversary).main.IsQueryBoundP IsModifiedNonceAeadSealQuery qSeal := by
  simpa only [viewReduction, OracleComp.isQueryBoundP_map_iff] using
    sourceClient_seal_bound decode (guardedClient decode adversary) qSeal
      (guardedClient_query_bound decode adversary _ qSeal bounded)

/-- Every original uniform request and every actual digest miss remains in the ciphertext-view reduction. -/
theorem viewReduction_uniform_bound (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool)
    (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (viewReduction decode adversary).main.IsQueryBoundP AdaptiveRawNonceAead.IsPrimitiveUniformQuery
      (qCoins + 64 * (qHash + qSeal + qRaw)) := by
  simpa only [viewReduction, OracleComp.isQueryBoundP_map_iff] using
    sourceClient_uniform_bound decode (guardedClient decode adversary) qCoins qHash qSeal qRaw
      (guardedClient_query_bound decode adversary _ qCoins coinBound)
      (guardedClient_query_bound decode adversary _ qHash hashBound)
      (guardedClient_query_bound decode adversary _ qSeal sealBound)
      (guardedClient_query_bound decode adversary _ qRaw rawBound)

/-- The complete ordinary real-view challenger additionally samples its 32-byte record key. -/
theorem viewReal_uniform_bound (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp ReceiveSpec Bool) (qCoins qHash qSeal qRaw : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw) :
    (modifiedNonceAeadINDDollarRealExp c (viewReduction decode adversary)).IsTotalQueryBound
      (32 + (qCoins + 64 * (qHash + qSeal + qRaw))) := by
  unfold modifiedNonceAeadINDDollarRealExp
  apply OracleComp.isTotalQueryBound_bind (uniformFixedBytes_isTotalQueryBound 32)
  intro key
  simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    modifiedNonceAeadINTCTXTImpl_run_total_of_uniform_bound c key (viewReduction decode adversary).main _
      (viewReduction_uniform_bound decode adversary qCoins qHash qSeal qRaw
        coinBound hashBound sealBound rawBound)

/-- Every original request submits exactly its own plaintext cost, even when its raw reply is discarded after execution. -/
theorem guard_plaintext_step (decode : RawDecoder) (query : ReceiveSpec.Domain) (history : PublicHistory) :
    SourcePlaintextBound ((guard decode query).run history) (SourcePlaintextCost query) := by
  cases query <;>
    simp only [AdaptiveCtxPrivacyGuard.guard, StateT.run, bind_pure_comp, SourcePlaintextBound,
      OracleComp.isQueryBound_map_iff, OracleComp.isQueryBound_query_iff]
  all_goals exact Nat.le_refl _

/-- Weighted source plaintext budgets add over arbitrary complete continuations. -/
theorem sourcePlaintext_bind {First Result : Type} (first : OracleComp ReceiveSpec First)
    (next : First → OracleComp ReceiveSpec Result) (firstBytes nextBytes : ℕ)
    (firstBound : SourcePlaintextBound first firstBytes)
    (nextBound : ∀ value, SourcePlaintextBound (next value) nextBytes) :
    SourcePlaintextBound (first >>= next) (firstBytes + nextBytes) := by
  exact OracleComp.isQueryBound_bind Nat.add
    (fun query left right available allowed => by
      change SourcePlaintextCost query ≤ left + available ∧ SourcePlaintextCost query ≤ available + right
      constructor <;> omega)
    (fun query left right available allowed => by
      change left + (available - SourcePlaintextCost query) = left + available - SourcePlaintextCost query ∧
        available + right - SourcePlaintextCost query = (available - SourcePlaintextCost query) + right
      constructor <;> omega)
    firstBound nextBound

/-- Exact public replay guarding preserves the original total submitted plaintext-byte budget from any public history. -/
theorem guardRun_plaintext_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qBytes : ℕ)
    (bounded : SourcePlaintextBound adversary qBytes) (history : PublicHistory) :
    SourcePlaintextBound ((simulateQ (guard decode) adversary).run history) qBytes := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := id)
    (stepBudget := fun query _ => SourcePlaintextCost query)
    (fun firstBound nextBound => sourcePlaintext_bind _ _ _ _ firstBound nextBound)
    (fun query _available state _allowed => guard_plaintext_step decode query state)
    (fun _query _available allowed => by dsimp; omega) history

/-- The exact existing guardedClient inherits its source plaintext-byte budget; discarded raw replies never remove the selected query. -/
theorem guardedClient_plaintext_bound {Result : Type} (decode : RawDecoder)
    (adversary : OracleComp ReceiveSpec Result) (qBytes : ℕ)
    (bounded : SourcePlaintextBound adversary qBytes) :
    SourcePlaintextBound (guardedClient decode adversary) qBytes :=
  guardRun_plaintext_bound decode adversary qBytes bounded []


/-- The exact ordinary ciphertext-view reduction retains all submitted plaintext bytes and adds no encryption request of its own. -/
theorem viewReduction_plaintext_bound (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool)
    (qBytes : ℕ) (bounded : SourcePlaintextBound adversary qBytes) :
    PlaintextBound (viewReduction decode adversary).main qBytes := by
  simpa only [viewReduction, PlaintextBound, OracleComp.isQueryBound_map_iff] using
    sourceClient_plaintext_bound decode (guardedClient decode adversary) qBytes
      (guardedClient_plaintext_bound decode adversary qBytes bounded)

/-- The explicit random-view simulator charges every source coin/digest draw, submitted body byte and sixteen-byte tag. It generates no hidden record key. -/
theorem viewRandom_uniform_bound (decode : RawDecoder) (adversary : OracleComp ReceiveSpec Bool)
    (qCoins qHash qSeal qRaw qBytes : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP IsRawQuery qRaw)
    (bytesBound : SourcePlaintextBound adversary qBytes) :
    (randomView decode adversary).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * qSeal) :=
  randomExperiment_uniform_bound (viewReduction decode adversary) qBytes qSeal
    (qCoins + 64 * (qHash + qSeal + qRaw))
    (viewReduction_plaintext_bound decode adversary qBytes bytesBound)
    (viewReduction_seal_bound decode adversary qSeal sealBound)
    (viewReduction_uniform_bound decode adversary qCoins qHash qSeal qRaw
      coinBound hashBound sealBound rawBound)

end BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReduction_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReduction_seal_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReduction_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReduction_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReal_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReal_uniform_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.guard_plaintext_step' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.guard_plaintext_step

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.sourcePlaintext_bind' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.sourcePlaintext_bind

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.guardRun_plaintext_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.guardRun_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.guardedClient_plaintext_bound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.guardedClient_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReduction_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewReduction_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewRandom_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPrivacyQueryBounds.viewRandom_uniform_bound
