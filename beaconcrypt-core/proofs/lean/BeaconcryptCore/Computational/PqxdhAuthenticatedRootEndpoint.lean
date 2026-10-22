import BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness
import BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds

/-!
A generic authenticated-root endpoint composes one complete-continuation correctness error with the actual one-key IND-CCA, secret-input Extract-family and indexed ordinary HMAC reductions. The protocol and optional initial coordinates are shared throughout. Root requests use a general finite cap, including continued private requests; no one-root restriction is imported from an earlier scheduler.

The protocol preparation and resumed client take only their original public inputs and permitted private state. Selected key and shared-secret arguments of the mathematical actual continuation remain in the private interpreter. Its supported good-sample equality and the optional authentication hop must be discharged by the consuming source experiment. This module does not itself construct or establish that final source instantiation, joint identity security, or primitive correctness with zero error. Public fixed-source HKDF evaluation remains actual computation rather than a new random-public-function assumption.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhHiddenRoot

variable {ι KemSK : Type} {baseSpec : OracleSpec ι}

/-- The existing ordinary protocol always encapsulates after its complete prechallenge phase. Its private mode may already retain a completed result. -/
def protocolPrefix (protocol : Protocol baseSpec) : PqxdhAuthenticatedRootCorrectness.Prefix baseSpec Bool where
  Context := protocol.State
  prepare := protocol.prepare
  proceed _ _ := true
  abort _ _ := pure false

/-- The ordinary real branch uses the encapsulated shared secret for the initial root and every matching private request. The selected secret key occurs only in its private public-service interpreter. -/
noncomputable def routedAfter (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    PqxdhAuthenticatedRootCorrectness.After protocol.State KemSK Bool :=
  fun publicKey secretKey state ciphertext secret =>
    simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem secretKey ciphertext)
      (simulateQ (route source ciphertext secret)
        (protocol.resume publicKey ciphertext state
          ((protocol.initialCoordinates publicKey ciphertext state).map
            (fun known => productionHiddenRoot source known secret)))))

/-- The real routed execution omits only the unused challenger sample. -/
noncomputable def routedMain (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) : ProbComp Bool :=
  PqxdhAuthenticatedRootCorrectness.main baseImpl kem (protocolPrefix protocol)
    (routedAfter source baseImpl kem protocol)

/-- No recipient-correctness premise is needed to identify the already routed continuation with the ordinary real branch. Only the independent unused challenger sample is erased at the distribution boundary. -/
theorem routed_eq_real (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    𝒟[routedMain source baseImpl kem protocol] =
      oneKeyBranch kem (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction source kem protocol) true := by
  simp only [routedMain, PqxdhAuthenticatedRootCorrectness.main,
    PqxdhAuthenticatedRootCorrectness.prepare, PqxdhAuthenticatedRootCorrectness.after,
    protocolPrefix, routedAfter, ite_true, oneKeyBranch, runtimeOfImpl_evalDist,
    oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, PqxdhChallengeSecretRouting.reduction,
    simulateQ_bind, pure_bind, bind_assoc, runtimeOfImpl_liftProbComp,
    simulateQ_kemAmbient_liftProbComp]
  apply EvalDistEq.evalDist_eq
  refine EvalDistEq.bind_right _ fun keys => ?_
  refine EvalDistEq.bind_right _ fun state => ?_
  refine EvalDistEq.bind_right _ fun pair => ?_
  simp only [publicImpl]
  exact (OracleComp.EvalDistEq.bind_const _ _).symm

/-- The routed real-to-random-secret hop is exactly the constructed ordinary one-key IND-CCA advantage, with no correctness assumption. -/
theorem routed_indCCA (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec) :
    (routedMain source baseImpl kem protocol).boolDistance
      (simulateQ (kemAmbientImpl baseImpl)
        (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)) =
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction source kem protocol).toINDCCA).toReal := by
  rw [ProbComp.boolDistance_eq_toReal_boolDist]
  rw [routed_eq_real, random_eq_branch]
  apply congrArg ENNReal.toReal
  exact (oneKey_indCCAAdvantage_eq_branchDist kem (runtimeOfImpl (kemAmbientImpl baseImpl))
    (PqxdhChallengeSecretRouting.reduction source kem protocol)
    (runtimeOfImpl_evalDist_pure _) (runtimeOfImpl_evalDist_bind _)
    (runtimeOfImpl_evalDist_liftProbComp _) (runtimeOfImpl_noFail_bool _)).symm

/-- A concrete simulation obligation on original supported good samples, not an additional primitive or protocol security assumption. -/
def GoodSimulation (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : Protocol baseSpec) (actual : PqxdhAuthenticatedRootCorrectness.After protocol.State KemSK Bool) : Prop :=
  ∀ keys ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen),
    ∀ state ∈ support (PqxdhAuthenticatedRootCorrectness.prepare baseImpl kem (protocolPrefix protocol) keys.1 keys.2),
    ∀ pair ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps keys.1)),
      functional.result keys.2 pair.1 = some pair.2 →
        actual keys.1 keys.2 state pair.1 pair.2 =
          routedAfter source baseImpl kem protocol keys.1 keys.2 state pair.1 pair.2

/-- The initial root and complete later native continuation share one ordinary correctness-error charge. -/
theorem actual_routed_bound (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : Protocol baseSpec) (actual : PqxdhAuthenticatedRootCorrectness.After protocol.State KemSK Bool)
    (agreement : GoodSimulation source baseImpl kem functional protocol actual) :
    (PqxdhAuthenticatedRootCorrectness.main baseImpl kem (protocolPrefix protocol) actual).boolDistance
      (routedMain source baseImpl kem protocol) ≤
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal := by
  rw [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton,
    ← prEvent_eq_evalDist_singleton]
  exact (abs_prEvent_toReal_sub_le_discreteDistance _ _).trans
    (PqxdhAuthenticatedRootCorrectness.main_bound baseImpl kem functional (protocolPrefix protocol)
      actual (routedAfter source baseImpl kem protocol)
      (fun keys generated state reached _ pair encapsulated good =>
        agreement keys generated state reached pair encapsulated good))

/-- The routed source reaches the consistent uniform-root family through the exact constructed CCA, secret-input Extract and indexed ordinary HMAC reductions. The arbitrary root cap includes repeated requests. -/
theorem routed_uniform_bound (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect source hmac)
    (qRoot : Nat) (rootBound : (rootReduction source baseImpl kem protocol).IsQueryBoundP IsRoot qRoot) :
    (routedMain source baseImpl kem protocol).boolDistance
      (uniformGame (rootReduction source baseImpl kem protocol)) ≤
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction source kem protocol).toINDCCA).toReal +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol) +
      ∑ index ∈ Finset.range qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction source baseImpl kem protocol) index)).boolDistance
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction source baseImpl kem protocol) index)) := by
  have family := PqxdhCorrelatedExtractFamily.correlated_advantage_eq source hmac sourceCorrect baseImpl kem protocol
  rw [reduction_expanded_eq] at family
  have first := (ProbComp.boolDistance_triangle (routedMain source baseImpl kem protocol)
    (simulateQ (kemAmbientImpl baseImpl)
      (randomMain source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol))
    (expandedGame hmac (rootReduction source baseImpl kem protocol))).trans
      (add_le_add (le_of_eq (routed_indCCA source baseImpl kem protocol)) (le_of_eq family))
  exact (ProbComp.boolDistance_triangle _
    (expandedGame hmac (rootReduction source baseImpl kem protocol)) _).trans
      (add_le_add first (expanded_uniform_bound hmac _ qRoot rootBound))

/-- A supported concrete native simulation reaches consistent uniform roots with one ordinary correctness error and the three explicit reduction terms. -/
theorem actual_uniform_bound (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : Protocol baseSpec) (actual : PqxdhAuthenticatedRootCorrectness.After protocol.State KemSK Bool)
    (agreement : GoodSimulation source baseImpl kem functional protocol actual)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect source hmac)
    (qRoot : Nat) (rootBound : (rootReduction source baseImpl kem protocol).IsQueryBoundP IsRoot qRoot) :
    (PqxdhAuthenticatedRootCorrectness.main baseImpl kem (protocolPrefix protocol) actual).boolDistance
      (uniformGame (rootReduction source baseImpl kem protocol)) ≤
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction source kem protocol).toINDCCA).toReal +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol) +
      ∑ index ∈ Finset.range qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction source baseImpl kem protocol) index)).boolDistance
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction source baseImpl kem protocol) index)) := by
  simpa only [add_assoc] using
    (ProbComp.boolDistance_triangle _ (routedMain source baseImpl kem protocol) _).trans
      (add_le_add (actual_routed_bound source baseImpl kem functional protocol actual agreement)
        (routed_uniform_bound source baseImpl kem protocol hmac sourceCorrect qRoot rootBound))

/-- An independently proved authentication comparison composes with the same concrete reductions. This generic wrapper does not supply the source authentication or good-sample simulation proofs. -/
theorem authenticated_uniform_bound (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : Protocol baseSpec) (actual : PqxdhAuthenticatedRootCorrectness.After protocol.State KemSK Bool)
    (agreement : GoodSimulation source baseImpl kem functional protocol actual)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect source hmac)
    (qRoot : Nat) (rootBound : (rootReduction source baseImpl kem protocol).IsQueryBoundP IsRoot qRoot)
    (game : ProbComp Bool) (authenticationLoss : ℝ)
    (authentication : game.boolDistance
      (PqxdhAuthenticatedRootCorrectness.main baseImpl kem (protocolPrefix protocol) actual) ≤ authenticationLoss) :
    game.boolDistance (uniformGame (rootReduction source baseImpl kem protocol)) ≤
      authenticationLoss +
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
      (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction source kem protocol).toINDCCA).toReal +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction source hmac baseImpl kem protocol) +
      ∑ index ∈ Finset.range qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction source baseImpl kem protocol) index)).boolDistance
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction source baseImpl kem protocol) index)) := by
  simpa only [add_assoc] using
    (ProbComp.boolDistance_triangle game
      (PqxdhAuthenticatedRootCorrectness.main baseImpl kem (protocolPrefix protocol) actual) _).trans
      (add_le_add authentication
        (actual_uniform_bound source baseImpl kem functional protocol actual agreement hmac sourceCorrect qRoot rootBound))

/-- The exact root client pays one possible initial root plus every continued private-root attempt. Every indexed HMAC reduction has one challenge call and the complete derived uniform budget, including both ordinary challenger bills. -/
theorem reduction_resources (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (protocol : Protocol baseSpec)
    (hmac : HmacSha512)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost : Nat)
    (bounded : PqxdhChallengeSecretQueryBounds.SamplerBounds baseImpl kem protocol
      qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost privatePost) :
    let client := rootReduction source baseImpl kem protocol
    let qCoins := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) +
      (uPost + qBase * bPost + qDecap * (dPost + privatePost))
    client.IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin qCoins ∧
    client.IsQueryBoundP IsRoot (1 + privatePost) ∧
    ∀ index,
      (indexedReduction hmac client index).IsQueryBoundP PqxdhSecretInputInitializer.IsHmacUniformQuery
        (qCoins + 64 * (1 + privatePost)) ∧
      (indexedReduction hmac client index).IsQueryBoundP PqxdhSecretInputKdf.IsHmacChallengeQuery 1 ∧
      (hmacPrfRealGame hmac (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + qCoins + 64 * (1 + privatePost)) ∧
      (hmacPrfRandomGame (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + qCoins + 64 * (1 + privatePost)) := by
  have caps := PqxdhCorrelatedExpandQueryBounds.reduction_bounds source baseImpl kem protocol
    _ _ _ _ _ _ _ _ _ _ _ bounded
  exact ⟨caps.1, caps.2, fun index =>
    let indexed := PqxdhCorrelatedExpandQueryBounds.indexed_bounds hmac _ index _ _ caps.1 caps.2
    ⟨indexed.1, indexed.2,
      PqxdhCorrelatedExpandQueryBounds.indexed_uniform_ledger hmac _ index _ _ caps.1 caps.2⟩⟩

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.routed_eq_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.routed_eq_real

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.routed_indCCA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.routed_indCCA

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.actual_routed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.actual_routed_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.routed_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.routed_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.actual_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.actual_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.authenticated_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.authenticated_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.reduction_resources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootEndpoint.reduction_resources
