import BeaconcryptCore.Computational.PqxdhAuthenticatedRootSource
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootGoodSimulation
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootBoundary

/-!
The actual generated-source experiment reaches the consistent uniform-root family with explicit joint identity, ordinary KEM correctness-error, one-key IND-CCA, secret-input Extract and indexed ordinary HMAC terms. The source authentication and concrete native good-sample simulation obligations are discharged by their checked consumers, rather than assumed at this endpoint. The same complete all-candidate source program and all postchallenge native effects are retained.

The root-query cap is stated for the actual compiled root client and must include the initial root and all later private attempts. Primitive source/interface contracts and caller query restrictions remain explicit; no earlier one-root theorem, perfect correctness assumption or ideal public HKDF service is substituted. Identification of the experiment's selected Server with native acceptance additionally uses the initial RootFields representation relation and its preserved-state boundary. This authenticated-root result does not claim evolving-chain security or a global raw-record origin theorem.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhJointKdfGame PqxdhChallengeSecretRouting
open PqxdhStatefulPhase1EufCma PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateRootSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf

variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- The source bridge and endpoint use the same literal native program, with no sampled-order or state projection change. -/
theorem nativeMain_eq_endpointMain :
    PqxdhAuthenticatedRootSource.nativeMain env baseImpl kem attachedVerify primitives program post =
      PqxdhAuthenticatedRootCorrectness.main baseImpl kem
        (PqxdhAuthenticatedRootEndpoint.protocolPrefix (protocol env kem attachedVerify primitives program post))
        (nativeAfter env baseImpl kem attachedVerify primitives program post) := by
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
      (rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post)).IsQueryBoundP IsRoot qRoot) :
    let p := protocol env kem attachedVerify primitives program post
    (actual env baseImpl kem attachedVerify primitives program post).boolDistance
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
  have auth := PqxdhAuthenticatedRootSource.authentication_hop env baseImpl kem attachedVerify primitives program post
    compatible adapter noSign noCreate fallback ordinaryFallback
  rw [nativeMain_eq_endpointMain] at auth
  exact PqxdhAuthenticatedRootEndpoint.authenticated_uniform_bound env.source baseImpl kem functional
    (protocol env kem attachedVerify primitives program post)
    (nativeAfter env baseImpl kem attachedVerify primitives program post)
    (PqxdhAuthenticatedRootGoodSimulation.goodSimulation env baseImpl kem attachedVerify primitives program post functional)
    hmac sourceCorrect qRoot rootBound (actual env baseImpl kem attachedVerify primitives program post) _ auth

/-- The same generated prefix used by the authentication reduction makes at most three signing calls and one identity-creation call under the actual caller restrictions. This counts the prefix through selection, not the arbitrary later native continuation. -/
theorem prefix_source_caps
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec)
        PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating) 0) :
    let work := PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program)
    work.IsQueryBoundP (fun query => PqxdhJointPhase1AcceptanceComposition.IsSigning
      (PqxdhPrivateSourceCoins.translated query)) 3 ∧
    work.IsQueryBoundP (fun query => PqxdhPrivatePhase1Prefix.Creating
      (PqxdhPrivateSourceCoins.translated query)) 1 := by
  exact PqxdhPhase2GeneratedDriverBounds.program_source_caps env.toDriverEnvironment program baseImpl kem noSign noCreate

/-- The same security bound is paired with the derived reached Server representation on every actual supported generated prefix. The initial representation relation is consumed, while changing peer maps and the full native state remain retained. -/
theorem authenticated_native_root_bound
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
      (rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post)).IsQueryBoundP IsRoot qRoot)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((actual env baseImpl kem attachedVerify primitives program post).boolDistance
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
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    ∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2 := by
  exact ⟨authenticated_root_bound env baseImpl kem attachedVerify primitives program post
      compatible adapter functional hmac sourceCorrect noSign noCreate fallback ordinaryFallback qRoot rootBound,
    fun result present => PqxdhAuthenticatedRootBoundary.reached_root_fields env baseImpl kem attachedVerify primitives
      program secretIdentity initialMatch result present⟩

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.nativeMain_eq_endpointMain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.nativeMain_eq_endpointMain

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.authenticated_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.authenticated_root_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.prefix_source_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.prefix_source_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.authenticated_native_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition.authenticated_native_root_bound
