import BeaconcryptCore.Computational.NonceAeadRandomQueryBounds
import BeaconcryptCore.Computational.AdaptiveCtxAliasQueryBounds

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds
open CtxRomAuth CtxNonceAeadIntCtxt CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation
open AdaptiveRawNonceAead AdaptiveCtxLogSimulation AdaptiveCtxPrefixValidation
open NonceAeadRandomQueryBounds

/-- A source seal charges its original submitted plaintext length, whether its nonce is fresh or rejected. Other source operations submit no encryption plaintext. -/
def SourcePlaintextCost : AdaptiveCtxReceive.ReceiveSpec.Domain → ℕ
  | .inl (.inr (.inr input)) => input.plaintext.length
  | _ => 0

/-- Source payload accounting quantifies over every possible adaptive reply and complete continuation. -/
def SourcePlaintextBound {Result : Type}
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (bytes : ℕ) : Prop :=
  adversary.IsQueryBound bytes (fun query available => SourcePlaintextCost query ≤ available)
    (fun query available => available - SourcePlaintextCost query)

/-- The logged client threads the same complete successful history through an arbitrary continuation. -/
theorem runLogged_bind {First Result : Type} (decode : AdaptiveRawNonceAead.RawDecoder)
    (first : OracleComp AdaptiveSpec First) (next : First → OracleComp AdaptiveSpec Result)
    (history : SealHistory) :
    runLogged decode (first >>= next) history = (do
      let result ← runLogged decode first history
      runLogged decode (next result.1) result.2) := by
  induction first using OracleComp.inductionOn generalizing history with
  | pure value => simp
  | query_bind query rest ih =>
    cases query with
    | inl primitive =>
      simp only [bind_assoc, runLogged_primitive]
      congr 1
      funext answer
      exact ih answer _
    | inr raw =>
      simpa only [bind_assoc, runLogged_raw] using ih (simulatedOpen decode history raw) history

/-- A logged computation without sealing contributes no plaintext bytes while retaining all its actual uniform/cache work. -/
theorem runLogged_no_plaintext {Result : Type} (decode : AdaptiveRawNonceAead.RawDecoder)
    (adversary : OracleComp AdaptiveSpec Result) (history : SealHistory)
    (bounded : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.TargetSeal 0) :
    PlaintextBound (runLogged decode adversary history) 0 :=
  no_seal_plaintext_zero _ (runLogged_query_bound decode adversary history
    IsModifiedNonceAeadSealQuery 0 bounded)

/-- The source sealing wrapper forwards the same submitted plaintext exactly once, and its subsequent private commitment lookup submits no further encryption message. -/
theorem sealStep_plaintext_bound (decode : AdaptiveRawNonceAead.RawDecoder)
    (input : CtxSealInput) (state : AdaptiveCtxReceive.ReceiveState) (history : SealHistory) :
    PlaintextBound (runLogged decode (AdaptiveCtxReceive.sealStep input state) history)
      input.plaintext.length := by
  unfold AdaptiveCtxReceive.sealStep
  rw [runLogged_primitive, PlaintextBound, OracleComp.isQueryBound_query_bind_iff]
  refine ⟨by simp [plaintextCost, CtxSealInput.toModifiedNonceAeadSealInput], ?_⟩
  intro answer
  cases answer with
  | none => trivial
  | some ciphertext =>
    simp only [plaintextCost, CtxSealInput.toModifiedNonceAeadSealInput, Nat.sub_self]
    apply runLogged_no_plaintext
    simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
      AdaptiveCtxQueryBounds.privateStep_no_seal
        (CtxSplitCache.outerSuffix input.nonce input.context ciphertext.tag) state

/-- Each complete logged source request forwards exactly its declared plaintext budget; public/private hashing and every raw reply add zero plaintext. -/
theorem sourceStep_plaintext_bound (decode : AdaptiveCtxReceive.RawDecoder)
    (query : AdaptiveCtxReceive.ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (history : SealHistory) :
    PlaintextBound (runLogged (AdaptiveCtxReceive.baseDecoder decode)
      ((AdaptiveCtxReceive.reductionImpl decode query).run state) history) (SourcePlaintextCost query) := by
  cases query with
  | inl request =>
    cases request with
    | inl coin =>
      apply runLogged_no_plaintext
      exact AdaptiveCtxQueryBounds.reductionImpl_seal_step decode (.inl (.inl coin)) state
    | inr operation =>
      cases operation with
      | inl hash =>
        apply runLogged_no_plaintext
        exact AdaptiveCtxQueryBounds.reductionImpl_seal_step decode (.inl (.inr (.inl hash))) state
      | inr input => exact sealStep_plaintext_bound (AdaptiveCtxReceive.baseDecoder decode) input state history
  | inr raw =>
    apply runLogged_no_plaintext
    exact AdaptiveCtxQueryBounds.reductionImpl_seal_step decode (.inr raw) state

/-- Full adaptive source simulation preserves the weighted original plaintext budget and all intermediate source/history states. -/
theorem loggedSource_plaintext_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (qBytes : ℕ)
    (bounded : SourcePlaintextBound adversary qBytes) (state : AdaptiveCtxReceive.ReceiveState)
    (history : SealHistory) :
    PlaintextBound (runLogged (AdaptiveCtxReceive.baseDecoder decode)
      ((simulateQ (AdaptiveCtxReceive.reductionImpl decode) adversary).run state) history) qBytes := by
  induction adversary using OracleComp.inductionOn generalizing qBytes state history with
  | pure value => trivial
  | query_bind query next ih =>
    rw [SourcePlaintextBound, OracleComp.isQueryBound_query_bind_iff] at bounded
    change PlaintextBound (runLogged (AdaptiveCtxReceive.baseDecoder decode)
      ((AdaptiveCtxReceive.reductionImpl decode query).run state >>= fun result =>
        (simulateQ (AdaptiveCtxReceive.reductionImpl decode) (next result.1)).run result.2) history) qBytes
    rw [runLogged_bind]
    have accounted := plaintext_bind _ _ (SourcePlaintextCost query) (qBytes - SourcePlaintextCost query)
      (sourceStep_plaintext_bound decode query state history)
      (fun result => ih result.1.1 _ (bounded.2 result.1.1) result.1.2 result.2)
    simpa only [Nat.add_sub_of_le bounded.1] using accounted

/-- The actual ordinary source client inherits the complete submitted-plaintext-byte cap. -/
theorem sourceClient_plaintext_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result) (qBytes : ℕ)
    (bounded : SourcePlaintextBound adversary qBytes) :
    PlaintextBound (sourceClient decode adversary) qBytes :=
  loggedSource_plaintext_bound decode adversary qBytes bounded AdaptiveCtxReceive.initialState []

/-- The final validation message is empty, so its additional sealing request adds no submitted plaintext bytes. -/
theorem validationSeal_plaintext_zero (nonce : CtxNonce) :
    PlaintextBound (queryModifiedNonceAeadSeal (ctxValidationInput nonce)) 0 := by
  exact (OracleComp.isQueryBound_query_iff (spec := ModifiedNonceAeadAdversarySpec)
    (.inr (ctxValidationInput nonce)) 0
    (fun query available => plaintextCost query ≤ available)
    (fun query available => available - plaintextCost query)).mpr (by simp [plaintextCost, ctxValidationInput])

/-- The exact conventional validation adversary preserves the source byte budget; its finite tag decision and empty-message validation add no payload. -/
theorem validationReduction_plaintext_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qHash qBytes : ℕ) (bounded : SourcePlaintextBound adversary qBytes) :
    PlaintextBound (validationReduction decode c adversary qHash).main qBytes := by
  unfold validationReduction
  simpa only [Nat.add_zero] using plaintext_bind (sourceClient decode adversary) _ qBytes 0
    (sourceClient_plaintext_bound decode adversary qBytes bounded)
    (fun result => by
      simpa only [bind_pure_comp, PlaintextBound, OracleComp.isQueryBound_map_iff] using
        validationSeal_plaintext_zero
          (chooseFreshCtxNonce (result.2.map (fun entry => entry.input.nonce))))

/-- The exact ordinary random validation challenger counts source coins, every digest miss, all submitted body bytes and one sixteen-byte tag per source or validation seal. It generates no hidden encryption key. -/
theorem validationRandom_uniform_bound {Result : Type} (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (adversary : OracleComp AdaptiveCtxReceive.ReceiveSpec Result)
    (qCoins qHash qSeal qRaw qBytes : ℕ)
    (coinBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qCoins)
    (hashBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash)
    (sealBound : adversary.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal qSeal)
    (rawBound : adversary.IsQueryBoundP AdaptiveCtxReceive.IsRawQuery qRaw)
    (bytesBound : SourcePlaintextBound adversary qBytes) :
    (modifiedNonceAeadINDDollarRandomExp (validationReduction decode c adversary qHash)).IsTotalQueryBound
      (qCoins + 64 * (qHash + qSeal + qRaw) + qBytes + 16 * (qSeal + 1)) :=
  randomExperiment_uniform_bound (validationReduction decode c adversary qHash)
    qBytes (qSeal + 1) (qCoins + 64 * (qHash + qSeal + qRaw))
    (validationReduction_plaintext_bound decode c adversary qHash qBytes bytesBound)
    (validationReduction_seal_bound decode c adversary qHash qSeal sealBound)
    (validationReduction_uniform_bound decode c adversary qCoins qHash qSeal qRaw
      coinBound hashBound sealBound rawBound)

end BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.runLogged_bind' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.runLogged_bind

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.runLogged_no_plaintext' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.runLogged_no_plaintext

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.sealStep_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.sealStep_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.sourceStep_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.sourceStep_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.loggedSource_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.loggedSource_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.sourceClient_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.sourceClient_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.validationSeal_plaintext_zero' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.validationSeal_plaintext_zero

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.validationReduction_plaintext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.validationReduction_plaintext_bound

/--
info: 'BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveCtxPlaintextQueryBounds.validationRandom_uniform_bound
