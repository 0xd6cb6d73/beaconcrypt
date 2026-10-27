import BeaconcryptCore.Computational.PqxdhInitialCurrentBudgets

/-!
The actual all-candidate authenticated-root experiment and its actual first initializer share one complete adaptive continuation. This module composes their already constructed reductions, deriving the root and initializer counts from the same source certificate. The endpoint supplies one shared uniform64 response to the selected initializer coordinate; the value-consistent variant additionally pays the derived initializer alias term. These statements preserve the existing final decision and do not yet identify the later published-record freshness event.
-/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedInitialComposition
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf PqxdhFullSecretInputKdf

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

noncomputable def rootLoss (hmac : HmacSha512)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (qRoot : Nat) : ℝ :=
  let p := protocol env kem attachedVerify primitives program post
  (PqxdhJointIdentity.advantage primitives
    (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
      (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
  Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
  (kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
    (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA).toReal +
  PqxdhCorrelatedExtractFamily.advantage hmac
    (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
  ∑ index ∈ Finset.range qRoot,
    (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistance
      (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))

noncomputable def initialLoss (hmac : HmacSha512) : ℝ :=
  let joint := PqxdhInitialCurrentSecrecy.joint env baseImpl kem attachedVerify primitives program post
  let observer := PqxdhInitialCurrentSecrecy.observer env baseImpl kem attachedVerify primitives program post
  (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observer)).boolDistance
    (extractUniformGame joint (fullExtractReduction hmac .ratchet observer)) +
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observer)).boolDistance
    (hmacPrfRandomGame (fullExpandReduction .ratchet joint observer))

/-- The actual generated source reaches its shared uniform64 initializer endpoint with the concrete authenticated-root and initial-expansion reductions. Both hops use the same complete post client; the root-query cap comes from its source certificate. -/
theorem authenticated_initial_bound
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (rootCorrect : SourceRootCorrect env.source hmac)
    (fullCorrect : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistance
      (PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post) ≤
      rootLoss env baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback c.qRoot +
      initialLoss env baseImpl kem attachedVerify primitives program post hmac := by
  exact (ProbComp.boolDistance_triangle _
    (uniformGame (rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post))) _).trans
    (add_le_add
      (PqxdhAuthenticatedRootComposition.authenticated_root_bound env baseImpl kem attachedVerify primitives program post
        compatible adapter functional hmac rootCorrect c.noSign c.noCreate fallback ordinaryFallback c.qRoot
        (PqxdhAuthenticatedRootBudgets.root_reduction_bounds env baseImpl kem attachedVerify primitives program post c).2)
      (PqxdhInitialCurrentSecrecy.primitive_bound env baseImpl kem attachedVerify primitives program post hmac fullCorrect))

/-- Routing equal-byte initializer roots consistently adds the actual source-derived alias probability, including rejected and repeated initializer attempts. Public HKDF evaluations remain real. -/
theorem authenticated_consistent_initial_bound
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (rootCorrect : SourceRootCorrect env.source hmac)
    (fullCorrect : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistance
      (PqxdhInitialCurrentAliases.consistentRandom env baseImpl kem attachedVerify primitives program post) ≤
      (rootLoss env baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback c.qRoot +
      initialLoss env baseImpl kem attachedVerify primitives program post hmac) +
      (((1 + c.privatePost : Nat) : ENNReal) / (2 ^ 256 : ENNReal)).toReal := by
  exact (ProbComp.boolDistance_triangle _
    (PqxdhInitialCurrentSecrecy.random env baseImpl kem attachedVerify primitives program post) _).trans
    (add_le_add
      (authenticated_initial_bound env baseImpl kem attachedVerify primitives program post c compatible adapter functional
        hmac rootCorrect fullCorrect fallback ordinaryFallback)
      (PqxdhInitialCurrentAliases.random_bound env baseImpl kem attachedVerify primitives program post (1 + c.privatePost)
        (PqxdhInitialCurrentBudgets.client_initial env baseImpl kem attachedVerify primitives program post c)))

end BeaconcryptCore.Computational.PqxdhAuthenticatedInitialComposition

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedInitialComposition.authenticated_initial_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedInitialComposition.authenticated_initial_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedInitialComposition.authenticated_consistent_initial_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedInitialComposition.authenticated_consistent_initial_bound
