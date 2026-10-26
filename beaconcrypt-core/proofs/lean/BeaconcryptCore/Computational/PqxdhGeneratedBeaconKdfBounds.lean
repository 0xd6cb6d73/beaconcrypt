import BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdf

/-!
The generated/native root reductions retain the actual source query ledger. This module counts every private writer and native continuation draw before instantiating the existing Extract-family and HMAC challengers. Selective query bounds exclude other work only from that particular count; primitive evaluation and local source work remain computation.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhGeneratedBeaconExperiment
open PqxdhGeneratedBeaconSelector (Program driver driver_source_bound driver_class_bound driver_total)
open PqxdhProtocolQueryBounds PqxdhPrivateRootQueryBounds PqxdhPrivateKemQueryBounds
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix
open PqxdhProtocolSelector (SelectorClass)
open PqxdhInitializerSecrecy PqxdhPrivateRootSource

variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K A : Type} {S B : Nat}

/-- The ordinary borrowed prefix counts the actual identity/prekey/one-time source and optional writer before all public requests. -/
theorem borrowed_uniform_bound {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (budget : Budget) (bounded : ∀ reply, Bounded (program.main reply) budget)
    (qPrekey qOneTime qSource qWrite : Nat)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP IsMlKemUniformQuery qPrekey)
    (oneTimeBound : ∀ identity before target,
      (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP IsMlKemUniformQuery qOneTime)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) Creating)) 0)
    (sourceCoins : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) SourceUniform)) qSource)
    (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (target : TargetKemPublicKey) :
    (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup
      (driver env.toEnvironment program) target).IsQueryBoundP IsMlKemUniformQuery
        (32 + (qPrekey + (qOneTime + (qSource + (qWrite + compilerBill budget))))) := by
  apply PqxdhGeneratedRootQueryBounds.borrowedPrefix_bound attachedVerify primitives setup
    (driver env.toEnvironment program) IsMlKemUniformQuery 32 qPrekey qOneTime
      (qSource + (qWrite + compilerBill budget))
  · exact ccaCoins_uniform _ _ sampleSeed_uniform_bound
  · exact prekeyBound
  · exact oneTimeBound
  · intro index identity generated transcript state
    simpa only [Nat.mul_zero, Nat.zero_add] using PqxdhPrivateRootQueryBounds.borrowed_uniform_bound
      attachedVerify primitives 1 ((driver env.toEnvironment program).main index identity generated transcript)
      0 qSource (qWrite + compilerBill budget)
      (driver_source_bound env.toEnvironment program Creating 0 noCreate index identity generated transcript)
      (driver_source_bound env.toEnvironment program SourceUniform qSource sourceCoins index identity generated transcript)
      (driver_total env.toEnvironment program qWrite writerBound budget bounded index identity generated transcript).isQueryBoundP state

/-- Every non-uniform CCA class retains actual generation requests and the same public scheduler allowance; the separately charged writer adds no such request. -/
theorem borrowed_class_bound {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin)))
    (qPrekey qOneTime qDriver : Nat)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP predicate qPrekey)
    (oneTimeBound : ∀ identity before target,
      (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP predicate qOneTime)
    (bounded : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) predicate)) qDriver)
    (target : TargetKemPublicKey) :
    (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup
      (driver env.toEnvironment program) target).IsQueryBoundP predicate (qPrekey + (qOneTime + qDriver)) := by
  simpa only [Nat.zero_add] using PqxdhGeneratedRootQueryBounds.borrowedPrefix_bound attachedVerify primitives
    setup (driver env.toEnvironment program) predicate 0 qPrekey qOneTime qDriver
    (ccaCoins_excluded _ predicate excluded) prekeyBound oneTimeBound
    (fun index identity generated transcript state => PqxdhPrivateRootQueryBounds.borrowed_class_bound
      attachedVerify primitives 1 ((driver env.toEnvironment program).main index identity generated transcript)
      predicate excluded qDriver
      (driver_class_bound env.toEnvironment program (SelectorCCA (baseSpec := baseSpec) predicate)
        (by intro coin; exact excluded coin) qDriver bounded index identity generated transcript) state) target

/-- The whole ordinary preparation charges original generation, optional writer, native or ordinary encapsulation, and the completed native continuation on every candidate branch. -/
theorem prepare_uniform_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (prefixBudget : Budget) (postBudget : RawCtxRevealBudgets.Budget)
    (prefixBound : ∀ reply, Bounded (program.main reply) prefixBudget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qPrekey qOneTime qSource qWrite qAux uEphemeral uNative uTotal : Nat)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP IsMlKemUniformQuery qPrekey)
    (oneTimeBound : ∀ identity before target,
      (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP IsMlKemUniformQuery qOneTime)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) Creating)) 0)
    (sourceCoins : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) SourceUniform)) qSource)
    (writerBound : ∀ fields primitive, ((env.phase1Writer fields).run primitive).IsTotalQueryBound qWrite)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (ephemeralBound : (ccaAmbient env.ephemeralGen).IsQueryBoundP IsMlKemUniformQuery uEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (env.native.encaps target)).IsQueryBoundP IsMlKemUniformQuery uNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP IsMlKemUniformQuery uTotal)
    (target : TargetKemPublicKey) :
    ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemUniformQuery
      ((32 + (qPrekey + (qOneTime + (qSource + (qWrite + compilerBill prefixBudget))))) +
        (uEphemeral + (max uNative uTotal + ((64 + 5 * qAux) +
          (postBudget.1 .coin + 64 * (postBudget.1 .send + postBudget.1 .raw + postBudget.1 .hash)))))) := by
  apply PqxdhGeneratedRootQueryBounds.rootProtocol_prefix_bound kem env.parameters attachedVerify primitives setup
    (driver env.toEnvironment program) (observer env program post) IsMlKemUniformQuery
  · exact borrowed_uniform_bound env attachedVerify primitives program prefixBudget prefixBound
      qPrekey qOneTime qSource qWrite prekeyBound oneTimeBound noCreate sourceCoins writerBound
  · exact ephemeralBound
  · exact nativeBound
  · exact totalBound
  · intro challenge output execution state
    simpa only [Environment.parameters, Nat.mul_zero, Nat.zero_add] using
      (PqxdhPrivateAcceptedRootBounds.observe_bounds env.source challenge attachedVerify primitives 1 setup
        (observer env program post) output execution state 0 0 _ 0 0 0
        (PqxdhGeneratedBeaconQueryBounds.completed_observer_bounds env program post postBudget postBound qAux output execution)).1
  · intro challenge output execution state
    simpa only [Environment.parameters, Nat.mul_zero, Nat.zero_add] using
      (PqxdhPrivateAcceptedRootBounds.acceptedObserve_bounds env.source challenge attachedVerify primitives 1 setup
        (observer env program post) output execution state 0 0 _ 0 0 0
        (PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds env program post postBudget postBound qAux auxBound output execution)).1

/-- Base and logical-decapsulation counts include every original generation and encapsulation request; the concrete native observer performs only its separately charged local work. -/
theorem prepare_class_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [predicateDecidable : DecidablePred predicate]
    (classChoice : predicate = IsMlKemBaseQuery ∨ predicate = IsMlKemLogicalDecapsulationQuery)
    (qPrekey qOneTime qDriver qEphemeral qNative qTotal : Nat)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP predicate qPrekey)
    (oneTimeBound : ∀ identity before target,
      (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP predicate qOneTime)
    (driverBound : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) predicate)) qDriver)
    (ephemeralBound : (ccaAmbient env.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (env.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (postBudget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (target : TargetKemPublicKey) :
    ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP predicate
      ((qPrekey + (qOneTime + qDriver)) + (qEphemeral + max qNative qTotal)) := by
  have excluded : ∀ coin, ¬ predicate (.inl (.inl coin)) := by
    rcases classChoice with rfl | rfl <;> simp [IsMlKemBaseQuery, IsMlKemLogicalDecapsulationQuery]
  have first := borrowed_class_bound env attachedVerify primitives program predicate excluded
    qPrekey qOneTime qDriver prekeyBound oneTimeBound driverBound
  have completed : ∀ challenge output execution state,
      (PqxdhPrivateAcceptedRoot.observe env.parameters.source challenge attachedVerify primitives 1 setup
        (observer env program post) output execution state).IsQueryBoundP predicate 0 := by
    intro challenge output execution state
    have bounded := PqxdhPrivateAcceptedRootBounds.observe_bounds env.parameters.source challenge
      attachedVerify primitives 1 setup (observer env program post) output execution state 0 0 _ 0 0 0
      (PqxdhGeneratedBeaconQueryBounds.completed_observer_bounds env program post postBudget postBound qAux output execution)
    rcases classChoice with rfl | rfl
    · cases Subsingleton.elim predicateDecidable instDecidablePredIsMlKemBaseQuery
      exact bounded.2.1
    · cases Subsingleton.elim predicateDecidable instDecidablePredIsMlKemLogicalDecapsulationQuery
      simpa only [Nat.zero_add] using bounded.2.2
  have accepted : ∀ challenge output execution state,
      (PqxdhPrivateAcceptedRoot.acceptedObserve env.parameters.source challenge attachedVerify primitives 1 setup
        (observer env program post) output execution state).IsQueryBoundP predicate 0 := by
    intro challenge output execution state
    have bounded := PqxdhPrivateAcceptedRootBounds.acceptedObserve_bounds env.parameters.source challenge
      attachedVerify primitives 1 setup (observer env program post) output execution state 0 0 _ 0 0 0
      (PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds env program post postBudget postBound qAux auxBound output execution)
    rcases classChoice with rfl | rfl
    · cases Subsingleton.elim predicateDecidable instDecidablePredIsMlKemBaseQuery
      exact bounded.2.1
    · cases Subsingleton.elim predicateDecidable instDecidablePredIsMlKemLogicalDecapsulationQuery
      simpa only [Nat.zero_add] using bounded.2.2
  simpa only [protocol, Nat.add_zero] using PqxdhGeneratedRootQueryBounds.rootProtocol_prefix_bound kem env.parameters
    attachedVerify primitives setup (driver env.toEnvironment program) (observer env program post) predicate
    (qPrekey + (qOneTime + qDriver)) qEphemeral qNative qTotal 0 first ephemeralBound nativeBound totalBound completed accepted target

/-- The actual accepted native callback pays the builder and complete post-schedule on both response outcomes. -/
def nativePostBill (budget : RawCtxRevealBudgets.Budget) (qAux : Nat) : Nat :=
  (64 + 5 * qAux) + (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))

/-- All sampler premises refer to actual primitive implementations and the reached source preparation; the native post bounds are derived here. -/
theorem native_sampler_bounds {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (qKeygen qEncap qBase qDecap uPre bPre dPre : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemUniformQuery uPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemBaseQuery bPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre)
    (postBudget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux) :
    PqxdhChallengeSecretQueryBounds.SamplerBounds baseImpl kem
      (protocol env kem attachedVerify primitives program post)
      qKeygen qEncap qBase qDecap uPre bPre dPre (nativePostBill postBudget qAux) 0 0 0 := by
  simpa only [protocol, nativePostBill, Nat.mul_zero, Nat.zero_add] using
    PqxdhGeneratedRootQueryBounds.rootProtocol_sampler_bounds baseImpl kem env.parameters attachedVerify primitives setup
      (driver env.toEnvironment program) (observer env program post)
      qKeygen qEncap qBase qDecap uPre bPre dPre 0 0 (nativePostBill postBudget qAux) 0 0 0
      keygenBound encapBound baseBound decapBound prepareBound
      (PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds env program post postBudget postBound qAux auxBound)

/-- The same concrete reductions have one Extract call and one HMAC challenge call, with every source-local draw retained in the client allowance. -/
theorem reduction_query_ledger {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (qKeygen qEncap qBase qDecap uPre bPre dPre : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemUniformQuery uPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemBaseQuery bPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre)
    (postBudget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux) :
    let p := protocol env kem attachedVerify primitives program post
    let extractClient := PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p
    let rootClient := PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem p
    let Q := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) + nativePostBill postBudget qAux
    extractClient.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsCoin Q ∧
    extractClient.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsFamily 1 ∧
    rootClient.IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin Q ∧
    rootClient.IsQueryBoundP PqxdhCorrelatedExpandHybrid.IsRoot 1 ∧
    ∀ index,
      (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index).IsQueryBoundP
        PqxdhSecretInputInitializer.IsHmacUniformQuery (Q + 64) ∧
      (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index).IsQueryBoundP
        PqxdhSecretInputKdf.IsHmacChallengeQuery 1 := by
  dsimp only
  have bounded := native_sampler_bounds env baseImpl kem attachedVerify primitives program post
    qKeygen qEncap qBase qDecap uPre bPre dPre keygenBound encapBound baseBound decapBound prepareBound
    postBudget postBound qAux auxBound
  have extracted := PqxdhCorrelatedExtractQueryBounds.reduction_bounds env.source hmac baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded
  have roots := PqxdhCorrelatedExpandQueryBounds.reduction_bounds env.source baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded
  simp only [Nat.mul_zero, Nat.add_zero] at extracted roots
  refine ⟨extracted.1, extracted.2, roots.1, roots.2, ?_⟩
  intro index
  simpa only [Nat.mul_one] using PqxdhCorrelatedExpandQueryBounds.indexed_bounds hmac
    (PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem
      (protocol env kem attachedVerify primitives program post)) index _ 1 roots.1 roots.2

/-- Complete real and random challengers retain their own sampled keys or answers, including draws unused by a completed client. -/
theorem reduction_sampler_ledger {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (hmac : PqxdhSecretInputKdf.HmacSha512)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (qKeygen qEncap qBase qDecap uPre bPre dPre : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemUniformQuery uPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemBaseQuery bPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre)
    (postBudget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux) :
    let p := protocol env kem attachedVerify primitives program post
    let extractClient := PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p
    let rootClient := PqxdhCorrelatedExpand.rootReduction env.source baseImpl kem p
    let Q := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) + nativePostBill postBudget qAux
    (PqxdhCorrelatedExtractFamily.realGame hmac extractClient).IsTotalQueryBound (32 + Q) ∧
    (PqxdhCorrelatedExtractFamily.randomGame extractClient).IsTotalQueryBound (Q + 64) ∧
    (PqxdhCorrelatedExpand.expandedGame hmac rootClient).IsTotalQueryBound (Q + 64) ∧
    (PqxdhCorrelatedExpandHybrid.uniformGame rootClient).IsTotalQueryBound (Q + 32) ∧
    ∀ index,
      (PqxdhSecretInputKdf.hmacPrfRealGame hmac
        (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index)).IsTotalQueryBound (64 + Q + 64) ∧
      (PqxdhSecretInputKdf.hmacPrfRandomGame
        (PqxdhCorrelatedExpandHybrid.indexedReduction hmac rootClient index)).IsTotalQueryBound (64 + Q + 64) := by
  dsimp only
  have bounded := native_sampler_bounds env baseImpl kem attachedVerify primitives program post
    qKeygen qEncap qBase qDecap uPre bPre dPre keygenBound encapBound baseBound decapBound prepareBound
    postBudget postBound qAux auxBound
  have extracted := PqxdhCorrelatedExtractQueryBounds.reduction_uniform_ledger env.source hmac baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded
  have expanded := PqxdhCorrelatedExpandQueryBounds.source_uniform_ledger env.source hmac baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded
  dsimp only at extracted expanded
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at extracted expanded
  exact ⟨extracted.1, extracted.2, expanded.2.1, expanded.2.2.1, expanded.2.2.2⟩

/-- The unchanged ordinary KEM reduction retains each pre/post class and every native or fair challenger draw, including unused completion-branch sampling. -/
theorem ordinary_kem_ledger {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (qKeygen qEncap qBase qDecap uPre bPre dPre : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemUniformQuery uPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemBaseQuery bPre ∧
      ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dPre)
    (postBudget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux) :
    let p := protocol env kem attachedVerify primitives program post
    let Q := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap) + nativePostBill postBudget qAux
    (PqxdhChallengeSecretRouting.reduction env.source kem p).MakesAtMostQueries
      uPre bPre dPre (nativePostBill postBudget qAux) 0 0 ∧
    (simulateQ (kemAmbientImpl baseImpl) (PqxdhChallengeSecretRouting.sourceMain env.source kem p)).IsTotalQueryBound Q ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (PqxdhChallengeSecretRouting.randomMain env.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) p)).IsTotalQueryBound (Q + 32) ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (PqxdhChallengeSecretRouting.nativeMain env.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) p)).IsTotalQueryBound (Q + 32) ∧
    (PqxdhPrivateRootGameBudgets.oneKeyFairProgram baseImpl kem
      (PqxdhChallengeSecretRouting.reduction env.source kem p)).IsTotalQueryBound (Q + 33) := by
  dsimp only
  have bounded := native_sampler_bounds env baseImpl kem attachedVerify primitives program post
    qKeygen qEncap qBase qDecap uPre bPre dPre keygenBound encapBound baseBound decapBound prepareBound
    postBudget postBound qAux auxBound
  have calls := PqxdhGeneratedRootQueryBounds.rootProtocol_reduction_bounds kem env.parameters attachedVerify primitives
    setup (driver env.toEnvironment program) (observer env program post) uPre bPre dPre
    0 0 (nativePostBill postBudget qAux) 0 0 0 prepareBound
    (PqxdhGeneratedBeaconQueryBounds.accepted_observer_bounds env program post postBudget postBound qAux auxBound)
  have samplers := PqxdhGeneratedRootQueryBounds.correlated_world_ledger baseImpl kem env.parameters
    attachedVerify primitives setup (driver env.toEnvironment program) (observer env program post)
    qKeygen qEncap qBase qDecap uPre bPre dPre 0 0 (nativePostBill postBudget qAux) 0 0 0 (by simpa only [protocol, Nat.mul_zero, Nat.zero_add] using bounded)
  refine ⟨?_, ?_⟩
  · simpa only [protocol, Environment.parameters, Nat.mul_zero, Nat.zero_add] using calls
  · simpa only [protocol, Environment.parameters, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using samplers

/-- Actual source generation and both encapsulation interfaces cannot issue logical decapsulation requests, so the ordinary preparation retains at most the selector allowance qD. -/
theorem prepare_decapsulation_bound {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K A S B)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post program.Selection S (B + 1))
    (qD : Nat)
    (driverBound : ∀ reply, (program.main reply).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)) qD)
    (postBudget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qAux : Nat)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (target : TargetKemPublicKey) :
    ((protocol env kem attachedVerify primitives program post).prepare target).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qD := by
  simpa only [Nat.zero_add, Nat.add_zero, Nat.max_self] using prepare_class_bound env kem attachedVerify primitives
    program post IsMlKemLogicalDecapsulationQuery (Or.inr rfl) 0 0 qD 0 0 0
    (fun identity => PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap (setup.prekey identity))
    (fun identity before target => PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap (setup.oneTime identity before target))
    driverBound (PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap env.ephemeralGen)
    (fun target => PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap (env.native.encaps target))
    (fun target => PqxdhCorrelatedRootQueryBounds.ccaAmbient_no_decap (kem.encaps target))
    postBudget postBound qAux auxBound target

end BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.borrowed_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.borrowed_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.borrowed_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.borrowed_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.prepare_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.prepare_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.prepare_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.prepare_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.native_sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.native_sampler_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.reduction_query_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.reduction_query_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.reduction_sampler_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.reduction_sampler_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.ordinary_kem_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.ordinary_kem_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.prepare_decapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconKdfBounds.prepare_decapsulation_bound
