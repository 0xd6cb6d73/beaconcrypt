import BeaconcryptCore.Computational.PqxdhGeneratedRootSource
import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds

/-!
Generated-driver resource transport preserves actual source ordering and every private continuation. Source identity generation, actual prekey/KEM/one-time sampling, all declared source/CCA classes and complete native root continuations are charged before any evaluated generator interchange. Concrete Phase1 serialization must appear in the driver's uniform allowance; it is excluded only from predicates that explicitly omit those coins. Ordinary preparation/completion and real/random/fair challenger draws have their own checked ledgers. Uniform requests count as calls, not arbitrary entropy bits or free local runtime. Native Phase2 routing, evolving distributions and reveal freshness remain separate interpretation obligations.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhJointPhase1AcceptanceComposition
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhPrivateRootSource (Parameters Prepared targetEligible borrowedPrefix continuedSource Mode blockChallenge)
open PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhDynamicIdentityRouting PqxdhPrivateRootQueryBounds
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhCorrelatedRootQueryBounds
open PqxdhPrivateAcceptedRoot
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

open PqxdhPrivateSourceCoins PqxdhStatefulPhase1EufCma
open PqxdhPrivateRootGameBudgets PqxdhPrivateAcceptedRootBounds
open PqxdhGeneratedPhase1Prefix PqxdhGeneratedRootSource

/-- The source-generated prefix pays for its actual identity, prekey, one-time and full adaptive selector work; signing is separately charged as three local operations. -/
theorem borrowedPrefix_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qSeed qPrekey qOneTime qDriver : Nat)
    (seedBound : (ccaCoins (baseSpec := baseSpec) sampleSeed).IsQueryBoundP predicate qSeed)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP predicate qPrekey)
    (oneTimeBound : ∀ identity before target, (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP predicate qOneTime)
    (driverBound : ∀ index publicIdentity generated transcript state,
      ((simulateQ (borrowedSelector attachedVerify primitives 1) (driver.main index publicIdentity generated transcript)).run state).IsQueryBoundP predicate qDriver)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) :
    (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup driver target).IsQueryBoundP predicate
      (qSeed + (qPrekey + (qOneTime + qDriver))) := by
  unfold PqxdhGeneratedRootSource.borrowedPrefix
  apply isQueryBoundP_bind seedBound
  intro seed _
  apply isQueryBoundP_bind (prekeyBound _)
  intro before _
  apply isQueryBoundP_bind (oneTimeBound _ _ _)
  intro after _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using driverBound 0 (primitives.publicKeys seed) ⟨before, target, (), after⟩ _ _

/-- The actual private source prefix charges its identity seed and complete generation/driver executions in their original order. -/
theorem program_uniform_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (qGeneration qDriver : Nat)
    (generationBound : ∀ identity, (generate baseImpl kem setup identity).IsTotalQueryBound qGeneration)
    (driverBound : ∀ index publicIdentity generated secret publicTranscript state,
      ((simulateQ (privateImpl attachedVerify primitives count)
        (simulateQ (localSelector baseImpl kem secret) (driver.main index publicIdentity generated publicTranscript))).run state).IsTotalQueryBound qDriver) :
    (privateRun attachedVerify primitives count (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)).IsTotalQueryBound
      (32 + (qGeneration + qDriver)) := by
  rw [PqxdhGeneratedPhase1Prefix.program_complete]
  apply isTotalQueryBound_bind sampleSeed_uniform_bound
  intro seed
  apply isTotalQueryBound_bind (generationBound _)
  intro generated
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    driverBound 0 (primitives.publicKeys seed) (PqxdhPrivateRootSource.eraseGenerated generated) generated.secret _ _

/-- Full source execution is bounded before any evaluated generator reordering, so sampling costs are not inferred from marginal equality. -/
theorem continuedSource_uniform_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (next : Prepared setup driver.State → OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (fallback : Result) (qPrefix qNext : Nat)
    (prefixBound : (privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)).IsTotalQueryBound qPrefix)
    (nextBound : ∀ secret prepared,
      (evalKem baseImpl kem secret (next prepared)).IsTotalQueryBound qNext) :
    (PqxdhGeneratedRootSource.continuedSource attachedVerify primitives baseImpl kem setup driver next fallback).IsTotalQueryBound
      (qPrefix + qNext) := by
  unfold PqxdhGeneratedRootSource.continuedSource
  apply isTotalQueryBound_bind prefixBound
  rintro ⟨output, state⟩
  cases output with
  | none => trivial
  | some output => exact nextBound output.context.generated.secret (PqxdhPrivateRootSource.eraseOutput output, state)

/-- Concrete private source generation and adaptive driver budgets combine without an unexpanded protocol-prefix allowance. -/
theorem program_uniform_from_calls
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (driver : Driver setup)
    (qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (creates : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls) :
    (privateRun attachedVerify primitives count (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)).IsTotalQueryBound
      (32 + ((qPrekey + (qKeygen + qOneTime)) +
        (32 * qCreate + qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls))) := by
  apply program_uniform_bound attachedVerify primitives count baseImpl kem setup driver
  · exact generate_uniform_bound baseImpl kem setup qPrekey qKeygen qOneTime prekeyBound keygenBound oneTimeBound
  · intro index publicIdentity generated secret transcript state
    exact localSelector_uniform_bound attachedVerify primitives count baseImpl kem secret qBase qDecap
      baseBound (decapBound secret) (driver.main index publicIdentity generated transcript) _ _ _ _ _
      (creates index publicIdentity generated transcript) (sourceCoins index publicIdentity generated transcript)
      (ccaCoinsBound index publicIdentity generated transcript) (bases index publicIdentity generated transcript)
      (decaps index publicIdentity generated transcript) state

/-- The ordinary preparation includes the full generated driver, ephemeral/native or total encapsulation attempts and every completed or accepted continuation. -/
theorem rootProtocol_prefix_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (driver : Driver setup) (observer : Continuation setup driver.State)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qPrefix qEphemeral qNative qTotal qObserver : Nat)
    (prefixBound : ∀ target, (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup driver target).IsQueryBoundP predicate qPrefix)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) :
    ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP predicate
      (qPrefix + (qEphemeral + (max qNative qTotal + qObserver))) :=
  isQueryBoundP_bind (prefixBound target) (fun prepared _ => dispatch_bound kem parameters attachedVerify primitives
    setup observer predicate qEphemeral qNative qTotal qObserver ephemeralBound nativeBound totalBound observerBound acceptedBound prepared)


/-- All postchallenge source classes and matching private root attempts remain charged in the retained generated context. -/
theorem rootProtocol_resume_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) (ciphertext : MlKem768Ciphertext)
    (mode : Mode setup driver.State) (initial : Option PqxdhSecretInputKdf.RootOutput) :
    PostBounds ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).resume
      target ciphertext mode initial) (32 * creates + sourceCoins + uniforms) bases decaps roots := by
  cases mode with
  | completed decision => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
  | pending prepared ephemeral =>
      cases initial with
      | none => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
      | some root =>
          exact localAccepted_bounds parameters.source attachedVerify primitives 1 setup observer _ _ prepared.2
            creates sourceCoins uniforms bases decaps roots (bounded _ _)


/-- The concrete ordinary IND-CCA reduction preserves the full pre/post class bounds and charges private root attempts as logical decapsulations. -/
theorem rootProtocol_reduction_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State)
    (uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (prepareBound : ∀ target,
      ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP
        IsMlKemUniformQuery uPre ∧
      ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP
        IsMlKemBaseQuery bPre ∧
      ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery dPre)
    (bounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots) :
    (reduction parameters.source kem (PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer)).MakesAtMostQueries
      uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases (decaps + roots) :=
  reduction_bounds parameters.source kem _ _ _ _ _ _ _ _ prepareBound
    (rootProtocol_resume_bounds kem parameters attachedVerify primitives setup driver observer
      creates sourceCoins uniforms bases decaps roots bounded)


/-- The original optional source program pays its own prefix and expanded native continuation costs, without using evaluated distribution equality to infer work. -/
theorem actualGame_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State)
    (qPrefix qBase qDecap qUniform qBaseCalls qDecapCalls : Nat)
    (prefixBound : (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup driver)).IsTotalQueryBound qPrefix)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (uniforms : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery qUniform)
    (bases : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery qBaseCalls)
    (decaps : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (PqxdhGeneratedRootSource.actualGame baseImpl kem parameters attachedVerify primitives setup driver observer).IsTotalQueryBound
      (qPrefix + (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls)) := by
  apply continuedSource_uniform_bound attachedVerify primitives baseImpl kem setup driver _ false _ _ prefixBound
  intro secret prepared
  exact PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret) _ _ _ _
    (uniforms prepared) (bases prepared) (decaps prepared)



/-- Actual generated keys and every driver/continuation query class yield a direct full source sampling ledger. -/
theorem actualGame_uniform_from_calls
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State)
    (qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls
      uNext bNext dNext : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (creates : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : ∀ index publicIdentity generated transcript,
      (driver.main index publicIdentity generated transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls)
    (uniformsNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery uNext)
    (basesNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery bNext)
    (decapsNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery dNext) :
    (PqxdhGeneratedRootSource.actualGame baseImpl kem parameters attachedVerify primitives setup driver observer).IsTotalQueryBound
      ((32 + ((qPrekey + (qKeygen + qOneTime)) +
        (32 * qCreate + qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls))) +
        (uNext + qBase * bNext + qDecap * dNext)) :=
  actualGame_uniform_bound baseImpl kem parameters attachedVerify primitives setup driver observer
    _ _ _ _ _ _
    (program_uniform_from_calls attachedVerify primitives 1 baseImpl kem setup driver
      qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls
      prekeyBound keygenBound oneTimeBound baseBound decapBound creates sourceCoins ccaCoinsBound bases decaps)
    baseBound decapBound uniformsNext basesNext decapsNext


/-- The generated root protocol retains actual key generation, encapsulation and all base/decapsulation sampling costs. -/
theorem rootProtocol_sampler_bounds
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State)
    (qKeygen qEncap qBase qDecap uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP
        IsMlKemUniformQuery uPre ∧
      ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP
        IsMlKemBaseQuery bPre ∧
      ((PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer).prepare target).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery dPre)
    (bounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots) :
    SamplerBounds baseImpl kem (PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer)
      qKeygen qEncap qBase qDecap uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases decaps roots :=
  ⟨keygenBound, encapBound, baseBound, decapBound, prepareBound,
    rootProtocol_resume_bounds kem parameters attachedVerify primitives setup driver observer
      creates sourceCoins uniforms bases decaps roots bounded⟩


/-- Source, shared-secret random, native and fair challengers each retain their actual sampler order and unused draws. -/
theorem correlated_world_ledger
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (driver : Driver setup)
    (observer : Continuation setup driver.State)
    (qKeygen qEncap qBase qDecap uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : SamplerBounds baseImpl kem (PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer)
      qKeygen qEncap qBase qDecap uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases decaps roots) :
    let protocol := PqxdhGeneratedRootSource.rootProtocol kem parameters attachedVerify primitives setup driver observer
    let before := qKeygen + (uPre + qBase * bPre + qDecap * dPre) + qEncap
    let after := (32 * creates + sourceCoins + uniforms) + qBase * bases + qDecap * (decaps + roots)
    (simulateQ (kemAmbientImpl baseImpl) (sourceMain parameters.source kem protocol)).IsTotalQueryBound
      (before + after) ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (randomMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).IsTotalQueryBound
      (before + 32 + after) ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (nativeMain parameters.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) protocol)).IsTotalQueryBound
      (before + 32 + after) ∧
    (PqxdhPrivateRootGameBudgets.oneKeyFairProgram baseImpl kem
      (reduction parameters.source kem protocol)).IsTotalQueryBound (before + 33 + after) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using source_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded
  · rw [randomMain_eq_branchMain]
    simpa only [Nat.add_assoc] using fixed_world_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded.keygen bounded.encaps bounded.base bounded.decaps bounded.prepare bounded.resume false
  · simpa only [Nat.add_assoc] using native_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded
  · exact (fair_uniform_bound parameters.source baseImpl kem _
      _ _ _ _ _ _ _ _ _ _ _ bounded).mono (by omega)


end BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.borrowedPrefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.borrowedPrefix_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.program_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.program_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.continuedSource_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.continuedSource_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.program_uniform_from_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.program_uniform_from_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_prefix_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_resume_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_resume_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.actualGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.actualGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.actualGame_uniform_from_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.actualGame_uniform_from_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.rootProtocol_sampler_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.correlated_world_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedRootQueryBounds.correlated_world_ledger
