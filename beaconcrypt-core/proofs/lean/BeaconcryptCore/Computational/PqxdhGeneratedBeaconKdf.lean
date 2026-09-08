import BeaconcryptCore.Computational.PqxdhGeneratedBeaconQueryBounds
import BeaconcryptCore.Computational.PqxdhCorrelatedExpandQueryBounds

/-!
The actual generated/native source execution reaches the consistent private root family through the existing ordinary joint-use authentication, KEM CCA, exact secret-input Extract-family and ordered HMAC reductions. Every repeated root retains its family address, and all public fixed-HKDF evaluations remain real. The Extract-family advantage is an additional explicit primitive endpoint, not inferred from ordinary HMAC PRF. This root hop does not establish evolving record-key secrecy or the pending Phase2/reveal and live symbolic simulations.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhGeneratedBeaconSelector PqxdhGeneratedBeaconExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K A : Type} {S B : Nat}

/-- The actual generated owner and reached native continuation use the exact secret-input family reduction, with unchanged public evaluations. -/
theorem authenticated_family_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhGeneratedBeaconExperiment.Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : PqxdhKemIndCca.MlKem768RecipientCorrectness kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (sourceCorrect : PqxdhSecretInputKdf.SourceRootCorrect env.source hmac)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (program : Program baseSpec setup.Context S (B + 1))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning)) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating)) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (post : Post program.Selection S (B + 1)) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (PqxdhCorrelatedExtractFamily.randomGame
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem
          (protocol env kem attachedVerify primitives program post))) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
        (driver env.toEnvironment program) fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem
          (protocol env kem attachedVerify primitives program post)).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem
          (protocol env kem attachedVerify primitives program post)) := by
  have authenticated := authenticated_bound env baseImpl kem compatible functional correct
    attachedVerify primitives adapter program noSign noCreate fallback ordinaryFallback post
  have extracted := PqxdhCorrelatedExtractFamily.correlated_advantage_eq env.source hmac sourceCorrect
    baseImpl kem (protocol env kem attachedVerify primitives program post)
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans
    (add_le_add authenticated (le_of_eq extracted))

/-- Every original root position pays its constructed ordinary HMAC reduction; repeated addresses retain the same complete root. -/
theorem authenticated_uniform_roots_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhGeneratedBeaconExperiment.Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : PqxdhKemIndCca.MlKem768RecipientCorrectness kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (sourceCorrect : PqxdhSecretInputKdf.SourceRootCorrect env.source hmac)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (program : Program baseSpec setup.Context S (B + 1))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning)) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating)) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (post : Post program.Selection S (B + 1)) (q : Nat)
    (rootBound : (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post)).IsQueryBoundP
        PqxdhCorrelatedExpandHybrid.IsRoot q) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (PqxdhCorrelatedExpandHybrid.uniformGame
        (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
          (protocol env kem attachedVerify primitives program post))) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
        (driver env.toEnvironment program) fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem
          (protocol env kem attachedVerify primitives program post)).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem
          (protocol env kem attachedVerify primitives program post)) +
      ∑ index ∈ Finset.range q,
        (PqxdhSecretInputKdf.hmacPrfRealGame hmac
          (PqxdhCorrelatedExpandHybrid.indexedReduction hmac
            (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
              (protocol env kem attachedVerify primitives program post)) index)).boolDistAdvantage
          (PqxdhSecretInputKdf.hmacPrfRandomGame
            (PqxdhCorrelatedExpandHybrid.indexedReduction hmac
              (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
                (protocol env kem attachedVerify primitives program post)) index)) := by
  have family := authenticated_family_bound env baseImpl kem compatible functional correct hmac sourceCorrect
    attachedVerify primitives adapter program noSign noCreate fallback ordinaryFallback post
  have expanded := PqxdhCorrelatedExpandHybrid.expanded_uniform_bound hmac
    (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post)) q rootBound
  rw [← PqxdhCorrelatedExpand.reduction_expanded_eq env.source hmac baseImpl kem] at expanded
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add family expanded)

/-- The current native continuation makes no further private roots, so its actual reduction uses at most one family address. This does not make its local computations free. -/
theorem native_root_query_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhGeneratedBeaconExperiment.Environment setup M P I K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (budget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) budget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux) :
    (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post)).IsQueryBoundP
        PqxdhCorrelatedExpandHybrid.IsRoot 1 := by
  have resumed := PqxdhGeneratedRootQueryBounds.rootProtocol_resume_bounds kem env.parameters
    attachedVerify primitives setup (driver env.toEnvironment program) (observer env program post)
    0 0 ((64 + 5 * qAux) + (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))) 0 0 0
    (PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds env program post budget postBound qAux auxBound)
  unfold PqxdhCorrelatedExpand.rootReduction
  simpa only [Nat.zero_add] using isQueryBoundP_bind
    (PqxdhCorrelatedExpandQueryBounds.rootCoins_roots
      (PqxdhCorrelatedExtractFamily.prepare baseImpl kem
        (protocol env kem attachedVerify primitives program post))) (fun prepared _ => by
      unfold PqxdhCorrelatedExpand.rootResume
      cases initial : (protocol env kem attachedVerify primitives program post).initialCoordinates
        prepared.publicKey prepared.ciphertext prepared.state with
      | none =>
          simp only [pure_bind]
          exact (PqxdhCorrelatedExpandQueryBounds.post_root_bound env.source baseImpl kem _ _ _ _
            (resumed prepared.publicKey prepared.ciphertext prepared.state none).privateRoots).mono (by omega)
      | some known =>
          have one := (isQueryBoundP_map_iff _ some 1).mpr
            (PqxdhCorrelatedExpandQueryBounds.query_bounds
              (PqxdhCorrelatedExtractFamily.coordinates known)).2
          exact isQueryBoundP_bind one (fun answer _ =>
            PqxdhCorrelatedExpandQueryBounds.post_root_bound env.source baseImpl kem _ _ _ _
              (resumed prepared.publicKey prepared.ciphertext prepared.state answer).privateRoots))

/-- The actual one-generated-Beacon native root execution has four named primitive terms and one HMAC reduction, without an honest-selected-key premise. -/
theorem authenticated_native_root_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhGeneratedBeaconExperiment.Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : PqxdhKemIndCca.MlKem768RecipientCorrectness kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (sourceCorrect : PqxdhSecretInputKdf.SourceRootCorrect env.source hmac)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (program : Program baseSpec setup.Context S (B + 1))
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning)) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (PqxdhProtocolSelector.SelectorClass (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating)) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (post : Post program.Selection S (B + 1)) (budget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) budget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux) :
    (actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (PqxdhCorrelatedExpandHybrid.uniformGame
        (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
          (protocol env kem attachedVerify primitives program post))) ≤
      (advantage primitives (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
        (driver env.toEnvironment program) fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem
          (protocol env kem attachedVerify primitives program post)).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem
          (protocol env kem attachedVerify primitives program post)) +
        (PqxdhSecretInputKdf.hmacPrfRealGame hmac
          (PqxdhCorrelatedExpandHybrid.indexedReduction hmac
            (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
              (protocol env kem attachedVerify primitives program post)) 0)).boolDistAdvantage
          (PqxdhSecretInputKdf.hmacPrfRandomGame
            (PqxdhCorrelatedExpandHybrid.indexedReduction hmac
              (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
                (protocol env kem attachedVerify primitives program post)) 0)) := by
  simpa only [Finset.sum_range_one] using authenticated_uniform_roots_bound env baseImpl kem compatible
    functional correct hmac sourceCorrect attachedVerify primitives adapter program noSign noCreate
    fallback ordinaryFallback post 1
    (native_root_query_bound env baseImpl kem attachedVerify primitives program post budget postBound qAux auxBound)

end BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.authenticated_family_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.authenticated_family_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.authenticated_uniform_roots_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.authenticated_uniform_roots_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.native_root_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.native_root_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.authenticated_native_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf.authenticated_native_root_bound
