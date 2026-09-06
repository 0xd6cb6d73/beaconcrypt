import BeaconcryptCore.Computational.PqxdhInitializerSecrecy
import BeaconcryptCore.Computational.PqxdhSecretInputKdf
import BeaconcryptCore.Computational.CtxComputationalSecurity

/-!
# Secret-input KDF composition with the challenge-blocked KEM interface

This module closes the one-key KEM-to-secret-input KDF seam. The sampled private interpreter state retains the target key, its secret key, the complete prechallenge continuation, and the challenge ciphertext. Only the interpreter receives the secret key; the protocol observer sees the same public transcript, four DH coordinates, root, and challenge-blocked decapsulation interface in every world. All public HKDF projections continue to use the production function.

The Extract input is exactly `FF^32 || DH1 || DH2 || DH3 || DH4 || uniform32`, with the complete sampled interpreter state as correlated context. Extract pseudorandomness for this joint distribution is an explicit primitive/distribution endpoint. No public-HKDF/random-table advantage or hidden-input guessing interpretation is used.

This is a one-key component composition. The retained Phase-1 classifier and authentication reduction are not instantiated here, so selecting the honest key remains outside this module's claim. The observer can retain arbitrary protocol state in the prechallenge continuation, but actual generator order, joint Ed25519/X25519 use, reveal rules, and source instantiation must be supplied by that later composition.
-/

open OracleSpec OracleComp ENNReal

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhSecretInputInitializer

open PqxdhKemIndCca PqxdhHiddenRoot PqxdhJointKdfGame
open PqxdhInitializerSecrecy PqxdhSecretInputKdf

variable {iota : Type} {baseSpec : OracleSpec iota} {SK : Type}

/-- Exact joint sampler after the KEM hop; the uniform secret is absent from the retained context. -/
noncomputable def secretInputSample
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    ProbComp (InitializerKdfPrefix kem adversary × Pqxdh.Bytes) := do
  let sampled ← initializerKdfPrefixProb baseImpl kem adversary
  let secret ← $ᵗ MlKemSharedSecret
  return (sampled, hiddenRootIKM
    (adversary.knownCoordinates sampled.state sampled.publicKey sampled.ciphertext) secret)

/-- The private KEM key stays in the interpreter; the public observer receives only its declared interface. -/
noncomputable def rootObserver
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    RootObserver (InitializerKdfPrefix kem adversary) := fun sampled root =>
  simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_postChallengeImpl sampled.secretKey sampled.ciphertext)
      (simulateQ (initializerPostRealImpl source kem)
        (adversary.main
          ⟨sampled.publicKey, sampled.ciphertext,
            adversary.publicContext sampled.state sampled.publicKey sampled.ciphertext⟩
          (adversary.knownCoordinates sampled.state sampled.publicKey sampled.ciphertext)
          root)))

/-- The corrected terminal game keeps public KDF and permitted decapsulation answers real. -/
noncomputable def independentInitializerGame
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) : ProbComp Bool :=
  independentRootGame (secretInputSample baseImpl kem adversary)
    (rootObserver source baseImpl kem adversary)

/-- The sampler is the exact false KEM branch, including its private continuation and one ghost sample. -/
theorem sourceRootGame_eq_kemFalseCore
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    sourceRootGame source (secretInputSample baseImpl kem adversary)
        (rootObserver source baseImpl kem adversary) =
      initializerKemFalseCore source baseImpl kem adversary := by
  simp [sourceRootGame, secretInputSample, initializerKdfPrefixProb,
    rootObserver, initializerKemFalseCore, productionHiddenRoot]

/-- The corrected real-to-uniform-secret hop is exactly the existing one-key IND-CCA reduction. -/
theorem real_sourceRoot_advantage_eq_indCCA
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
        (sourceRootGame source (secretInputSample baseImpl kem adversary)
          (rootObserver source baseImpl kem adversary)) =
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (toKemOneKeyAdversary source kem adversary).toINDCCA := by
  have hcca := oneKey_indCCAAdvantage_eq_branchDist kem
    (runtimeOfImpl (kemAmbientImpl baseImpl))
    (toKemOneKeyAdversary source kem adversary)
    (runtimeOfImpl_evalDist_pure (kemAmbientImpl baseImpl))
    (runtimeOfImpl_evalDist_bind (kemAmbientImpl baseImpl))
    (runtimeOfImpl_evalDist_liftProbComp baseImpl)
    (runtimeOfImpl_noFail_bool (kemAmbientImpl baseImpl))
  simpa [oneKeyBranch, runtimeOfImpl_evalDist, initializerRealGame,
    simulateQ_initializerOneKeyFalse_eq_falseCore, sourceRootGame_eq_kemFalseCore,
    ProbComp.boolDistAdvantage, SPMF.boolDistAdvantage, probOutput_def] using hcca.symm

/-- One actual root is replaced with loss-one KEM, Extract, and HMAC reductions while public KDF evaluations stay real. -/
theorem initializerAdvantage_le_kem_add_extract_add_hmac
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) :
    (initializerRealGame source baseImpl kem adversary).boolDistAdvantage
        (independentInitializerGame source baseImpl kem adversary) ≤
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (toKemOneKeyAdversary source kem adversary).toINDCCA +
      (extractRealGame hmac (secretInputSample baseImpl kem adversary)
        (extractReduction hmac (rootObserver source baseImpl kem adversary))).boolDistAdvantage
        (extractUniformGame (secretInputSample baseImpl kem adversary)
          (extractReduction hmac (rootObserver source baseImpl kem adversary))) +
      (hmacPrfRealGame hmac (expandReduction (secretInputSample baseImpl kem adversary)
        (rootObserver source baseImpl kem adversary))).boolDistAdvantage
        (hmacPrfRandomGame (expandReduction (secretInputSample baseImpl kem adversary)
          (rootObserver source baseImpl kem adversary))) := by
  exact (ProbComp.boolDistAdvantage_triangle _
    (sourceRootGame source (secretInputSample baseImpl kem adversary)
      (rootObserver source baseImpl kem adversary)) _).trans
    (by rw [real_sourceRoot_advantage_eq_indCCA, add_assoc]
        exact add_le_add (le_refl _) (sourceRootAdvantage_le_extract_add_hmac source hmac correct
          (secretInputSample baseImpl kem adversary)
          (rootObserver source baseImpl kem adversary)))

/-- The interpreted sampler charges the complete opaque prefix plus the exact 32-byte replacement draw. -/
theorem secretInputSample_uniform_query_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) {qPrefix : ℕ}
    (bound : (initializerKdfPrefixProb baseImpl kem adversary).IsTotalQueryBound qPrefix) :
    (secretInputSample baseImpl kem adversary).IsTotalQueryBound (qPrefix + 32) := by
  exact OracleComp.isTotalQueryBound_bind bound (fun sampled => by
    simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound,
      OracleComp.isQueryBound_map_iff] using
      CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)

/-- The source-root observer's complete interpreted workload is counted; no opaque ambient work is assigned zero cost. -/
theorem sourceRootGame_uniform_query_bound
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) {qPrefix qPost : ℕ}
    (prefixBound : (initializerKdfPrefixProb baseImpl kem adversary).IsTotalQueryBound qPrefix)
    (postBound : ∀ sampled root,
      (rootObserver source baseImpl kem adversary sampled root).IsTotalQueryBound qPost) :
    (sourceRootGame source (secretInputSample baseImpl kem adversary)
      (rootObserver source baseImpl kem adversary)).IsTotalQueryBound
        (qPrefix + 32 + qPost) := by
  exact OracleComp.isTotalQueryBound_bind
    (secretInputSample_uniform_query_bound baseImpl kem adversary prefixBound)
    (fun pair => postBound pair.1 _)

/-- Public coins remain separate from the one secret-key HMAC challenge query. -/
def IsHmacUniformQuery : HmacAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsHmacUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Lifting local probabilistic work preserves its complete public-uniform budget. -/
theorem local_hmac_uniform_query_bound {A : Type} (computation : ProbComp A) {q : ℕ}
    (bound : computation.IsTotalQueryBound q) :
    (OracleComp.liftComp computation HmacAdversarySpec).IsQueryBoundP IsHmacUniformQuery q := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec) (superSpec := HmacAdversarySpec)
    (p := fun _ => True) (q := IsHmacUniformQuery)
    (hpq := fun query => by simp [IsHmacUniformQuery, SubSpec.onQuery])
    ((OracleComp.isQueryBoundP_true_iff computation q).mpr bound)

/-- One HMAC challenge adds no public coins; every sampler and observer coin remains charged. -/
theorem expandReduction_uniform_query_bound {Context : Type}
    (sample : SecretInputSampler Context) (observer : RootObserver Context)
    {qSample qObserver : ℕ}
    (sampleBound : (sample : ProbComp (Context × Pqxdh.Bytes)).IsTotalQueryBound qSample)
    (observerBound : ∀ context root, (observer context root).IsTotalQueryBound qObserver) :
    (expandReduction sample observer).IsQueryBoundP IsHmacUniformQuery (qSample + qObserver) := by
  unfold expandReduction
  refine OracleComp.isQueryBoundP_bind (n := qSample) (m := qObserver)
    (local_hmac_uniform_query_bound sample sampleBound) ?_
  rintro ⟨context, input⟩ _
  rw [OracleComp.isQueryBoundP_query_bind_iff]
  simp only [IsHmacUniformQuery, not_false_eq_true, true_or, true_and]
  exact fun block => local_hmac_uniform_query_bound _ (observerBound context (first32 block))

/-- The actual Expand reduction has one HMAC challenge query and the complete interpreted prefix/post uniform cost. -/
theorem rootHmacReduction_query_bounds
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : InitializerAdversary kem) {qPrefix qPost : ℕ}
    (prefixBound : (initializerKdfPrefixProb baseImpl kem adversary).IsTotalQueryBound qPrefix)
    (postBound : ∀ sampled root,
      (rootObserver source baseImpl kem adversary sampled root).IsTotalQueryBound qPost) :
    (expandReduction (secretInputSample baseImpl kem adversary)
      (rootObserver source baseImpl kem adversary)).IsQueryBoundP
        IsHmacUniformQuery (qPrefix + 32 + qPost) ∧
    (expandReduction (secretInputSample baseImpl kem adversary)
      (rootObserver source baseImpl kem adversary)).IsQueryBoundP IsHmacChallengeQuery 1 := by
  exact ⟨expandReduction_uniform_query_bound _ _
      (secretInputSample_uniform_query_bound baseImpl kem adversary prefixBound) postBound,
    expandReduction_hmac_query_bound _ _⟩

/--
info: 'BeaconcryptCore.Computational.PqxdhSecretInputInitializer.initializerAdvantage_le_kem_add_extract_add_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms initializerAdvantage_le_kem_add_extract_add_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhSecretInputInitializer.rootHmacReduction_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rootHmacReduction_query_bounds

end BeaconcryptCore.Computational.PqxdhSecretInputInitializer
