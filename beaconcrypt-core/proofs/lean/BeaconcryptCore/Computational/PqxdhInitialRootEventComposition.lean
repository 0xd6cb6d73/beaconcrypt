import BeaconcryptCore.Computational.PqxdhInitialRootEventGoodSimulation

/-!
The actual generated-source experiment reaches the consistent uniform-root family with explicit joint identity, ordinary KEM correctness-error, one-key IND-CCA, secret-input Extract and indexed ordinary HMAC terms. The source authentication and concrete native good-sample simulation obligations are discharged by their checked consumers, rather than assumed at this endpoint. The same complete all-candidate source program and all postchallenge native effects are retained.

The root-query cap is stated for the actual compiled root client and must include the initial root and all later private attempts. Primitive source/interface contracts and caller query restrictions remain explicit; no earlier one-root theorem, perfect correctness assumption or ideal public HKDF service is substituted. Identification of the experiment's selected Server with native acceptance additionally uses the initial RootFields representation relation and its preserved-state boundary. This authenticated-root result does not claim evolving-chain security or a global raw-record origin theorem.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootEventComposition
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhInitialRootEventExperiment PqxdhPrivateAcceptedRoot
open PqxdhAuthenticatedRootExperiment (Post)
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (accepted : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State → Ready → OracleComp (LocalPostSpec baseSpec) Bool)

/-- The source bridge and endpoint use the same literal native program, with no sampled-order or state projection change. -/
theorem nativeMain_eq_endpointMain :
    PqxdhInitialRootEventSource.nativeMain env baseImpl kem attachedVerify primitives program post accepted =
      PqxdhAuthenticatedRootCorrectness.main baseImpl kem
        (PqxdhAuthenticatedRootEndpoint.protocolPrefix (protocol env kem attachedVerify primitives program post accepted))
        (nativeAfter env baseImpl kem attachedVerify primitives program post accepted) := by
  rfl

/-- The actual all-candidate generated native experiment has the explicit five-term authenticated-root bound. Both authentication filtering and the supported good-sample simulation are derived, with no abstract hop or honest-candidate premise. -/
theorem authenticated_root_bound
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec)
        PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (qRoot : Nat) (rootBound :
      (rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post accepted)).IsQueryBoundP IsRoot qRoot) :
    let p := protocol env kem attachedVerify primitives program post accepted
    (actual env baseImpl kem attachedVerify primitives program post accepted).boolDistance
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
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
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)) := by
  have auth := PqxdhInitialRootEventSource.authentication_hop env baseImpl kem attachedVerify primitives program post accepted
    compatible adapter noSign noCreate fallback ordinaryFallback
  rw [nativeMain_eq_endpointMain] at auth
  exact PqxdhAuthenticatedRootEndpoint.authenticated_uniform_bound env.source baseImpl kem functional
    (protocol env kem attachedVerify primitives program post accepted)
    (nativeAfter env baseImpl kem attachedVerify primitives program post accepted)
    (PqxdhInitialRootEventGoodSimulation.goodSimulation env baseImpl kem attachedVerify primitives program post accepted functional)
    hmac sourceCorrect qRoot rootBound (actual env baseImpl kem attachedVerify primitives program post accepted) _ auth

end BeaconcryptCore.Computational.PqxdhInitialRootEventComposition

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventComposition.nativeMain_eq_endpointMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventComposition.nativeMain_eq_endpointMain

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootEventComposition.authenticated_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootEventComposition.authenticated_root_bound
