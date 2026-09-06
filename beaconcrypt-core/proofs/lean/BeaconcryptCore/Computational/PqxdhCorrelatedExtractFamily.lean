import BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds

/-!
One ordinary secret-input family has a hidden uniform 32-byte suffix, arbitrary public 128-byte messages, full 64-byte replies, and a final distinguishing bit. Its real function is the actual public-zero-salt HMAC-Extract at the exact 192-byte source input. Its ideal is one consistent private family table; public HKDF evaluation remains the supplied fixed function. The entire correlated KEM/source preparation and private continuation reduce to this family without exposing its secret. The actual source bound adds this explicit unreduced family advantage to joint-use weak-EUF and ordinary IND-CCA. Ordinary HMAC PRF does not discharge this additional cryptographic obligation. No independent-root, multiple-family, pinned-Server or global protocol conclusion is claimed.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily
open PqxdhSecretInputKdf PqxdhHiddenRoot PqxdhJointKdfGame
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Four exact 32-byte coordinates are an ordinary public 128-byte family message. -/
abbrev Message := List.Vector UInt8 128
abbrev ExtractOracle := Message →ₒ HmacBlock
abbrev FamilySpec := unifSpec + ExtractOracle

def coordinates (known : KnownPqxdhRootCoordinates) : Message :=
  ⟨known.dh1.toList ++ known.dh2.toList ++ known.dh3.toList ++ known.dh4.toList, by simp⟩

def familyInput (message : Message) (secret : MlKemSharedSecret) : Pqxdh.Bytes :=
  Pqxdh.padFF32 ++ message.toList ++ secret.toList

/-- A concrete secret-input family; this is not ordinary secret-key HMAC evaluation. -/
def evaluate (hmac : HmacSha512) (secret : MlKemSharedSecret) (message : Message) : HmacBlock :=
  extract hmac (familyInput message secret)

theorem familyInput_source (known : KnownPqxdhRootCoordinates) (secret : MlKemSharedSecret) :
    familyInput (coordinates known) secret = hiddenRootIKM known secret := by
  simp [familyInput, coordinates, hiddenRootIKM, Pqxdh.pqxdhIKM, List.append_assoc]

theorem familyInput_length (message : Message) (secret : MlKemSharedSecret) :
    (familyInput message secret).length = 192 := by
  simp [familyInput, Pqxdh.padFF32]

def realImpl (hmac : HmacSha512) (secret : MlKemSharedSecret) : QueryImpl FamilySpec ProbComp :=
  let primitive : QueryImpl ExtractOracle ProbComp := fun message => pure (evaluate hmac secret message)
  QueryImpl.ofLift unifSpec ProbComp + primitive

noncomputable def randomImpl : QueryImpl FamilySpec (StateT ExtractOracle.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT ExtractOracle.QueryCache ProbComp) +
    ExtractOracle.randomOracle

/-- Ordinary real-family game: the challenger keeps its one uniformly sampled secret. -/
noncomputable def realGame (hmac : HmacSha512) (client : OracleComp FamilySpec Bool) : ProbComp Bool := do
  let secret ← $ᵗ MlKemSharedSecret
  simulateQ (realImpl hmac secret) client

/-- Ordinary random-function game; repeated messages reuse the same full 64-byte answer. -/
noncomputable def randomGame (client : OracleComp FamilySpec Bool) : ProbComp Bool :=
  (simulateQ randomImpl client).run' ∅

/-- Only the ordinary distinguishing bit appears in this endpoint. No protocol acceptance or freshness predicate occurs. -/
noncomputable def advantage (hmac : HmacSha512) (client : OracleComp FamilySpec Bool) : ℝ :=
  (realGame hmac client).boolDistAdvantage (randomGame client)

def root (hmac : HmacSha512) (known : KnownPqxdhRootCoordinates) : OracleComp FamilySpec RootOutput := do
  let prk ← FamilySpec.query (.inr (coordinates known))
  pure (expandRoot hmac prk)

theorem root_real (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (known : KnownPqxdhRootCoordinates) (secret : MlKemSharedSecret) :
    simulateQ (realImpl hmac secret) (root hmac known) = pure (productionHiddenRoot source known secret) := by
  simp only [root, simulateQ_bind, simulateQ_spec_query, realImpl, QueryImpl.add_apply_inr,
    evaluate, familyInput_source, simulateQ_pure]
  change (pure (expandRoot hmac (extract hmac (hiddenRootIKM known secret))) : ProbComp RootOutput) = _
  rw [← sourceRootOutput_eq source hmac correct]
  rfl

def coins {Result : Type} (client : ProbComp Result) : OracleComp FamilySpec Result :=
  OracleComp.liftComp client FamilySpec

theorem coins_real {Result : Type} (hmac : HmacSha512) (secret : MlKemSharedSecret) (client : ProbComp Result) :
    simulateQ (realImpl hmac secret) (coins client) = client := by
  simp [coins, realImpl, QueryImpl.simulateQ_add_liftM_left]

/-- The reduction evaluates permitted CCA and nonmatching private work locally; matching private roots use only the family oracle. -/
noncomputable def post
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secretKey : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (LocalPostSpec baseSpec) (OracleComp FamilySpec)
  | .inl request => coins (simulateQ (kemAmbientImpl baseImpl) (publicImpl kem secretKey challenge request))
  | .inr request =>
      if request.ciphertext = challenge then some <$> root hmac request.coordinates
      else do
        let recovered ← coins (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secretKey request.ciphertext))
        pure (recovered.map (productionHiddenRoot source request.coordinates))

/-- The original correlated source post handler, under its actual shared-secret value. -/
noncomputable def suppliedImpl
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secretKey : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret) :
    QueryImpl (LocalPostSpec baseSpec) ProbComp := fun request =>
  simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (publicImpl kem secretKey challenge) (route source challenge supplied request))

/-- Every exact root, optional rejection and ordinary reply agrees before running any further continuation. -/
theorem post_real
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secretKey : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret) :
    realImpl hmac supplied ∘ₛ post source hmac baseImpl kem secretKey challenge =
      suppliedImpl source baseImpl kem secretKey challenge supplied := by
  funext request
  cases request with
  | inl request =>
      simp only [QueryImpl.compose, post, coins_real, suppliedImpl, route]
      exact congrArg (simulateQ (kemAmbientImpl baseImpl))
        (simulateQ_spec_query (publicImpl kem secretKey challenge) request).symm
  | inr request =>
      by_cases same : request.ciphertext = challenge
      · simp only [QueryImpl.compose, post, same, if_true, simulateQ_map, root_real source hmac correct,
          map_pure, suppliedImpl, route, pure_bind, simulateQ_pure, Option.map_some]
      · simp only [QueryImpl.compose, post, same, if_false, simulateQ_bind, coins_real, simulateQ_pure,
          suppliedImpl, route]
        have reply := congrArg (simulateQ (kemAmbientImpl baseImpl))
          ((simulateQ_spec_query (publicImpl kem secretKey challenge) (.inr request.ciphertext)).trans
            (publicImpl_other kem secretKey challenge request.ciphertext same))
        exact congrArg (fun (computation : ProbComp (Option MlKemSharedSecret)) =>
          computation >>= fun recovered => pure (recovered.map (productionHiddenRoot source request.coordinates))) reply.symm

/-- The exact family simulation retains arbitrary continued output, including private source state. -/
theorem post_complete {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secretKey : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (client : OracleComp (LocalPostSpec baseSpec) Result) :
    simulateQ (realImpl hmac supplied) (simulateQ (post source hmac baseImpl kem secretKey challenge) client) =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem secretKey challenge)
        (simulateQ (route source challenge supplied) client)) := by
  rw [← QueryImpl.simulateQ_compose, post_real source hmac correct]
  simp only [← QueryImpl.simulateQ_compose]
  rfl

/-- The primitive reduction holds its own generated KEM secret, never the family challenge secret. -/
structure Prepared (protocol : Protocol baseSpec) (KemSK : Type) where
  publicKey : MlKem768PublicKey
  secretKey : KemSK
  state : protocol.State
  ciphertext : MlKem768Ciphertext

def prepare (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    ProbComp (Prepared protocol KemSK) := do
  let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let state ← simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl pair.2) (protocol.prepare pair.1))
  let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps pair.1)
  pure ⟨pair.1, pair.2, state, encapsulated.1⟩

noncomputable def resume
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (prepared : Prepared protocol KemSK) : OracleComp FamilySpec Bool := do
  let initial ← match protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
    | none => pure none
    | some known => some <$> root hmac known
  simulateQ (post source hmac baseImpl kem prepared.secretKey prepared.ciphertext)
    (protocol.resume prepared.publicKey prepared.ciphertext prepared.state initial)

/-- One ordinary family client executes the entire original private preparation and continued protocol. -/
noncomputable def reduction
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    OracleComp FamilySpec Bool := do
  let prepared ← coins (prepare baseImpl kem protocol)
  resume source hmac baseImpl kem protocol prepared

/-- Fixed family-key interpretation keeps the same complete continuation and optional initial root. -/
theorem resume_real
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (prepared : Prepared protocol KemSK) (supplied : MlKemSharedSecret) :
    simulateQ (realImpl hmac supplied) (resume source hmac baseImpl kem protocol prepared) =
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem prepared.secretKey prepared.ciphertext)
        (simulateQ (route source prepared.ciphertext supplied)
          (protocol.resume prepared.publicKey prepared.ciphertext prepared.state
            ((protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state).map
              (fun known => productionHiddenRoot source known supplied))))) := by
  unfold resume
  cases initial : protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state with
  | none =>
      simp only [pure_bind, Option.map_none]
      exact post_complete source hmac correct baseImpl kem _ _ _ _
  | some known =>
      simp only [simulateQ_bind, simulateQ_map, root_real source hmac correct, map_pure, pure_bind, Option.map_some]
      exact post_complete source hmac correct baseImpl kem _ _ _ _

/-- The real-family client preserves the entire actual preparation and continued private computation. -/
theorem reduction_real
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (supplied : MlKemSharedSecret) :
    simulateQ (realImpl hmac supplied) (reduction source hmac baseImpl kem protocol) = (do
      let prepared ← prepare baseImpl kem protocol
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem prepared.secretKey prepared.ciphertext)
        (simulateQ (route source prepared.ciphertext supplied)
          (protocol.resume prepared.publicKey prepared.ciphertext prepared.state
            ((protocol.initialCoordinates prepared.publicKey prepared.ciphertext prepared.state).map
              (fun known => productionHiddenRoot source known supplied)))))) := by
  simp only [reduction, simulateQ_bind, coins_real, resume_real source hmac correct]

/-- Moving only the independent family key retains the complete KEM/source prefix and all later matching-secret correlations. -/
theorem real_eq_correlated
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    𝒟[realGame hmac (reduction source hmac baseImpl kem protocol)] =
      𝒟[simulateQ (kemAmbientImpl baseImpl)
        (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)] := by
  simp only [realGame, reduction_real source hmac correct]
  rw [evalDist_sample_comm ($ᵗ MlKemSharedSecret) (prepare baseImpl kem protocol)]
  simp only [prepare, randomMain, runtimeOfImpl_liftProbComp, simulateQ_bind,
    simulateQ_kemAmbient_liftProbComp, bind_assoc, pure_bind]

/-- The extra loss is exactly an ordinary secret-input family advantage, not a protocol-event assumption. -/
theorem correlated_advantage_eq
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    (simulateQ (kemAmbientImpl baseImpl)
      (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).boolDistAdvantage
      (randomGame (reduction source hmac baseImpl kem protocol)) =
      advantage hmac (reduction source hmac baseImpl kem protocol) := by
  simp only [advantage, ProbComp.boolDistAdvantage, probOutput_def, real_eq_correlated source hmac correct]

theorem familyInput_message_injective (secret : MlKemSharedSecret) :
    Function.Injective (fun message => familyInput message secret) := by
  intro left right equal
  apply List.Vector.toList_injective
  have selected := congrArg (fun input => (input.drop 32).take 128) equal
  simpa [familyInput, Pqxdh.padFF32] using selected

/-- Equality of actual 192-byte inputs is exactly repeated family-message equality when the secret is shared. -/
theorem familyInput_eq_iff (left right : Message) (secret : MlKemSharedSecret) :
    familyInput left secret = familyInput right secret ↔ left = right :=
  (familyInput_message_injective secret).eq_iff

set_option backward.isDefEq.respectTransparency false in
/-- The ideal family retains an already installed complete PRK and leaves the entire cache unchanged. -/
theorem random_hit (message : Message) (cache : ExtractOracle.QueryCache) (prk : HmacBlock)
    (hit : cache message = some prk) :
    (randomImpl (.inr message)).run cache = pure (prk, cache) := by
  simp only [randomImpl, QueryImpl.add_apply_inr, randomOracle.apply_eq, StateT.run_bind,
    StateT.run_get, pure_bind, hit, StateT.run_pure]

set_option backward.isDefEq.respectTransparency false in
/-- A new message installs one full 64-byte answer; subsequent equal inputs reuse it. -/
theorem random_miss (message : Message) (cache : ExtractOracle.QueryCache)
    (miss : cache message = none) :
    (randomImpl (.inr message)).run cache = (do
      let prk ← $ᵗ HmacBlock
      pure (prk, cache.cacheQuery message prk)) := by
  simp only [randomImpl, QueryImpl.add_apply_inr, randomOracle.apply_eq, StateT.run_bind,
    StateT.run_get, pure_bind, miss, StateT.run_modifyGet]
  change ((do let value ← $ᵗ HmacBlock; pure (value, cache)) >>= fun pair =>
    pure (pair.1, pair.2.cacheQuery message pair.1)) = _
  simp only [bind_assoc, pure_bind]

open PqxdhEd25519EufCma PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix PqxdhStatefulPhase1EufCma
open PqxdhPrivateRootSource PqxdhCorrelatedRootSource

/-- The actual optional source reaches the consistent random Extract family with three explicit primitive losses. -/
theorem authenticated_family_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect parameters.source hmac)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (observer : CorrelatedObserver setup selector.State) :
    let protocol := rootProtocol kem parameters attachedVerify primitives setup selector observer
    (PqxdhCorrelatedRootSource.actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (randomGame (reduction parameters.source hmac baseImpl kem protocol)) ≤
      (PqxdhJointIdentity.advantage primitives
        (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction parameters.source kem protocol).toINDCCA +
      advantage hmac (reduction parameters.source hmac baseImpl kem protocol) := by
  dsimp only
  have authenticated := authenticated_correlated_bound baseImpl kem parameters compatible functional correct
    attachedVerify primitives adapter setup selector selectorNoSign selectorNoCreate fallback ordinaryFallback observer
  have family := correlated_advantage_eq parameters.source hmac sourceCorrect baseImpl kem
    (rootProtocol kem parameters attachedVerify primitives setup selector observer)
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans
    (add_le_add authenticated (le_of_eq family))

end BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_source' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_source

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_length' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_length

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.root_real' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.root_real

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.coins_real' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.coins_real

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.post_real' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.post_real

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.post_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.post_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.resume_real' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.resume_real

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.reduction_real' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.reduction_real

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.real_eq_correlated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.real_eq_correlated

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.correlated_advantage_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.correlated_advantage_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_message_injective' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_message_injective

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_eq_iff' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.familyInput_eq_iff

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.random_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.random_hit

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.random_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.random_miss

/--
info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.authenticated_family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExtractFamily.authenticated_family_bound
