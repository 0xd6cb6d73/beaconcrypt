import BeaconcryptCore.Computational.PqxdhPrivateAcceptedRoot
import BeaconcryptCore.Computational.PqxdhCorrelatedRootQueryBounds
import BeaconcryptCore.Computational.PqxdhChallengeSecretQueryBounds

/-!
Logical and interpreted resource bounds for both actual continuation branches: completed source executions and accepted roots before publication. Every source creation/coin, public CCA class and private root attempt remains counted through all possible replies. Direct source costs are proved on the original program; complete source-shaped, random, native and fair CCA programs separately retain encapsulation and unused challenger draws. Root output replacement does not transfer marginal distributions into query costs. Native callback internal costs are supplied by the concrete builder's separate weighted ledger; local signing, DH, verification, fixed HKDF, byte and state work remain actual computation.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds
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

private theorem localSource_eq
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) :
    localSourceImpl (baseSpec := baseSpec) source attachedVerify primitives count =
      PqxdhCorrelatedRootSource.localSourceImpl source attachedVerify primitives count := rfl

theorem localObserve_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    {Selection : Type} (observer : Continuation setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState count)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ObserverBounds (observer.completed output execution) creates sourceCoins uniforms bases decaps roots) :
    PostBounds (localObserve source attachedVerify primitives count setup observer output execution state)
      (32 * creates + sourceCoins + uniforms) bases decaps roots := by
  constructor
  · simpa only [localObserve, localSource_eq, isQueryBoundP_map_iff] using
      localSource_uniform_bound source attachedVerify primitives count (observer.completed output execution)
        creates sourceCoins uniforms bounded.createBound bounded.sourceCoinBound bounded.uniformBound state
  · simpa only [localObserve, localSource_eq, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.completed output execution) _
        (fun _ => by simp [PublicClass, IsMlKemBaseQuery]) bases bounded.baseBound state
  · simpa only [localObserve, localSource_eq, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.completed output execution) _
        (fun _ => by simp [PublicClass, IsMlKemLogicalDecapsulationQuery]) decaps bounded.decapBound state
  · simpa only [localObserve, localSource_eq, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.completed output execution) _
        (fun _ => by simp [IsPrivateRoot]) roots bounded.rootBound state

theorem observe_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    {Selection : Type} (observer : Continuation setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState count)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ObserverBounds (observer.completed output execution) creates sourceCoins uniforms bases decaps roots) :
    let client := observe source challenge attachedVerify primitives count setup observer output execution state
    client.IsQueryBoundP IsMlKemUniformQuery (32 * creates + sourceCoins + uniforms) ∧
    client.IsQueryBoundP IsMlKemBaseQuery bases ∧
    client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (decaps + roots) := by
  have localBound := localObserve_bounds source attachedVerify primitives count setup observer output execution state
    creates sourceCoins uniforms bases decaps roots bounded
  exact ⟨sourcePost_public_bound source challenge _ (fun _ => by simp [IsMlKemUniformQuery]) _ _ localBound.uniforms,
    sourcePost_public_bound source challenge _ (fun _ => by simp [IsMlKemBaseQuery]) _ _ localBound.bases,
    sourcePost_decapsulation_bound source challenge _ _ _ localBound.decaps localBound.privateRoots⟩

theorem localAccepted_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    {Selection : Type} (observer : Continuation setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : Ready) (state : BareState count)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ObserverBounds (observer.accepted output execution) creates sourceCoins uniforms bases decaps roots) :
    PostBounds (localAccepted source attachedVerify primitives count setup observer output execution state)
      (32 * creates + sourceCoins + uniforms) bases decaps roots := by
  constructor
  · simpa only [localAccepted, localSource_eq, isQueryBoundP_map_iff] using
      localSource_uniform_bound source attachedVerify primitives count (observer.accepted output execution)
        creates sourceCoins uniforms bounded.createBound bounded.sourceCoinBound bounded.uniformBound state
  · simpa only [localAccepted, localSource_eq, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.accepted output execution) _
        (fun _ => by simp [PublicClass, IsMlKemBaseQuery]) bases bounded.baseBound state
  · simpa only [localAccepted, localSource_eq, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.accepted output execution) _
        (fun _ => by simp [PublicClass, IsMlKemLogicalDecapsulationQuery]) decaps bounded.decapBound state
  · simpa only [localAccepted, localSource_eq, isQueryBoundP_map_iff] using
      localSource_class_bound source attachedVerify primitives count (observer.accepted output execution) _
        (fun _ => by simp [IsPrivateRoot]) roots bounded.rootBound state

theorem acceptedObserve_bounds
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (challenge : Option MlKem768Ciphertext)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    {Selection : Type} (observer : Continuation setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : Ready) (state : BareState count)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ObserverBounds (observer.accepted output execution) creates sourceCoins uniforms bases decaps roots) :
    let client := acceptedObserve source challenge attachedVerify primitives count setup observer output execution state
    client.IsQueryBoundP IsMlKemUniformQuery (32 * creates + sourceCoins + uniforms) ∧
    client.IsQueryBoundP IsMlKemBaseQuery bases ∧
    client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (decaps + roots) := by
  have localBound := localAccepted_bounds source attachedVerify primitives count setup observer output execution state
    creates sourceCoins uniforms bases decaps roots bounded
  exact ⟨sourcePost_public_bound source challenge _ (fun _ => by simp [IsMlKemUniformQuery]) _ _ localBound.uniforms,
    sourcePost_public_bound source challenge _ (fun _ => by simp [IsMlKemBaseQuery]) _ _ localBound.bases,
    sourcePost_decapsulation_bound source challenge _ _ _ localBound.decaps localBound.privateRoots⟩



theorem acceptedCommon_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (state : BareState 1) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    (acceptedCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer output state
      parameters.server parameters.application parameters.ephemeralGen identity keys).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold acceptedCommon
  split
  · exact (observerBound _ _ _ _).mono (by omega)
  · apply isQueryBoundP_bind (by simpa only [ccaAmbient_eq_lift] using ephemeralBound)
    intro ephemeral _
    apply isQueryBoundP_bind (by simpa only [ccaAmbient_eq_lift] using nativeBound keys.pqKey)
    intro encapsulated _
    cases encapsulated with
    | none => exact observerBound _ _ _ _
    | some value =>
      rcases value with ⟨ciphertext, secret⟩
      dsimp only
      split
      · exact observerBound _ _ _ _
      · exact acceptedBound _ _ _ _


theorem allCandidateCommon_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (state : BareState 1) :
    (allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer output state
      parameters.server parameters.application parameters.ephemeralGen).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold allCandidateCommon
  cases output.bind (·.accepted) with
  | none => exact (observerBound _ _ _ _).mono (by omega)
  | some selected =>
      exact acceptedCommon_bound kem parameters attachedVerify primitives setup observer predicate
        qEphemeral qNative qObserver ephemeralBound nativeBound observerBound acceptedBound output state selected.1 selected.2


theorem targetAfterEncapsulation_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qObserver : Nat)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    (targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral encapsulated).IsQueryBoundP
      predicate qObserver := by
  unfold targetAfterEncapsulation
  cases encapsulated with
  | none => exact observerBound _ _ _ _
  | some pair =>
      rcases pair with ⟨ciphertext, secret⟩
      dsimp only
      split
      · exact observerBound _ _ _ _
      · exact acceptedBound _ _ _ _


theorem nativeNext_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) :
    (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold nativeNext
  split
  · unfold nativeTargetContinuation
    apply isQueryBoundP_bind ephemeralBound
    intro ephemeral _
    apply isQueryBoundP_bind (nativeBound _)
    intro encapsulated _
    exact targetAfterEncapsulation_bound kem parameters attachedVerify primitives setup observer predicate qObserver
      observerBound acceptedBound prepared ephemeral encapsulated
  · exact allCandidateCommon_bound kem parameters attachedVerify primitives setup observer predicate
      qEphemeral qNative qObserver ephemeralBound nativeBound observerBound acceptedBound _ _




theorem dispatch_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qTotal qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) :
    (dispatch kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP predicate
      (qEphemeral + (max qNative qTotal + qObserver)) := by
  unfold dispatch
  split
  · simp
  · split
    · apply isQueryBoundP_bind ephemeralBound
      intro ephemeral _
      split
      · simp
      · apply isQueryBoundP_bind ((totalBound _).mono (Nat.le_max_right _ _))
        intro encapsulated _
        simpa only [bind_pure_comp, isQueryBoundP_map_iff] using observerBound _ _ _ _
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        (allCandidateCommon_bound kem parameters attachedVerify primitives setup observer predicate
          qEphemeral qNative qObserver ephemeralBound nativeBound observerBound acceptedBound _ _).mono
          (by omega)


theorem rootProtocol_prefix_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (observer : Continuation setup selector.State)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qPrefix qEphemeral qNative qTotal qObserver : Nat)
    (prefixBound : ∀ target, (borrowedPrefix attachedVerify primitives setup selector target).IsQueryBoundP predicate qPrefix)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ challenge output execution state,
      (observe parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (acceptedBound : ∀ challenge output execution state,
      (acceptedObserve parameters.source challenge attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) :
    ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP predicate
      (qPrefix + (qEphemeral + (max qNative qTotal + qObserver))) :=
  isQueryBoundP_bind (prefixBound target) (fun prepared _ => dispatch_bound kem parameters attachedVerify primitives
    setup observer predicate qEphemeral qNative qTotal qObserver ephemeralBound nativeBound totalBound observerBound acceptedBound prepared)


theorem rootProtocol_resume_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State)
    (creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) (ciphertext : MlKem768Ciphertext)
    (mode : Mode setup selector.State) (initial : Option PqxdhSecretInputKdf.RootOutput) :
    PostBounds ((rootProtocol kem parameters attachedVerify primitives setup selector observer).resume
      target ciphertext mode initial) (32 * creates + sourceCoins + uniforms) bases decaps roots := by
  cases mode with
  | completed decision => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
  | pending prepared ephemeral =>
      cases initial with
      | none => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
      | some root =>
          exact localAccepted_bounds parameters.source attachedVerify primitives 1 setup observer _ _ prepared.2
            creates sourceCoins uniforms bases decaps roots (bounded _ _)


theorem rootProtocol_reduction_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State)
    (uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (prepareBound : ∀ target,
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemUniformQuery uPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemBaseQuery bPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery dPre)
    (bounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots) :
    (reduction parameters.source kem (rootProtocol kem parameters attachedVerify primitives setup selector observer)).MakesAtMostQueries
      uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases (decaps + roots) :=
  reduction_bounds parameters.source kem _ _ _ _ _ _ _ _ prepareBound
    (rootProtocol_resume_bounds kem parameters attachedVerify primitives setup selector observer
      creates sourceCoins uniforms bases decaps roots bounded)


theorem actualGame_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State)
    (qPrefix qBase qDecap qUniform qBaseCalls qDecapCalls : Nat)
    (prefixBound : (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (program baseImpl kem setup selector)).IsTotalQueryBound qPrefix)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (uniforms : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery qUniform)
    (bases : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery qBaseCalls)
    (decaps : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).IsTotalQueryBound
      (qPrefix + (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls)) := by
  apply PqxdhPrivateRootGameBudgets.continuedSource_uniform_bound attachedVerify primitives baseImpl kem setup selector _ false _ _ prefixBound
  intro secret prepared
  exact PqxdhPrivateRootGameBudgets.evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret) _ _ _ _
    (uniforms prepared) (bases prepared) (decaps prepared)



theorem actualGame_uniform_from_calls
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State)
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
    (creates : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls)
    (uniformsNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery uNext)
    (basesNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery bNext)
    (decapsNext : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery dNext) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).IsTotalQueryBound
      ((32 + ((qPrekey + (qKeygen + qOneTime)) +
        (32 * qCreate + qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls))) +
        (uNext + qBase * bNext + qDecap * dNext)) :=
  actualGame_uniform_bound baseImpl kem parameters attachedVerify primitives setup selector observer
    _ _ _ _ _ _
    (PqxdhPrivateRootGameBudgets.program_uniform_from_calls attachedVerify primitives 1 baseImpl kem setup selector
      qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls
      prekeyBound keygenBound oneTimeBound baseBound decapBound creates sourceCoins ccaCoinsBound bases decaps)
    baseBound decapBound uniformsNext basesNext decapsNext


theorem rootProtocol_sampler_bounds
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State)
    (qKeygen qEncap qBase qDecap uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (prepareBound : ∀ target,
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemUniformQuery uPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemBaseQuery bPre ∧
      ((rootProtocol kem parameters attachedVerify primitives setup selector observer).prepare target).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery dPre)
    (bounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots) :
    SamplerBounds baseImpl kem (rootProtocol kem parameters attachedVerify primitives setup selector observer)
      qKeygen qEncap qBase qDecap uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases decaps roots :=
  ⟨keygenBound, encapBound, baseBound, decapBound, prepareBound,
    rootProtocol_resume_bounds kem parameters attachedVerify primitives setup selector observer
      creates sourceCoins uniforms bases decaps roots bounded⟩


theorem correlated_world_ledger
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Continuation setup selector.State)
    (qKeygen qEncap qBase qDecap uPre bPre dPre creates sourceCoins uniforms bases decaps roots : Nat)
    (bounded : SamplerBounds baseImpl kem (rootProtocol kem parameters attachedVerify primitives setup selector observer)
      qKeygen qEncap qBase qDecap uPre bPre dPre (32 * creates + sourceCoins + uniforms) bases decaps roots) :
    let protocol := rootProtocol kem parameters attachedVerify primitives setup selector observer
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


theorem nativeNext_observer_bounds
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Continuation setup Selection)
    (uEphemeral uNative bEphemeral bNative creates sourceCoins uniforms bases decaps roots : Nat)
    (ephemeralUniform : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP IsMlKemUniformQuery uEphemeral)
    (nativeUniform : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP IsMlKemUniformQuery uNative)
    (ephemeralBase : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP IsMlKemBaseQuery bEphemeral)
    (nativeBase : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP IsMlKemBaseQuery bNative)
    (bounded : ∀ output execution, ObserverBounds (observer.completed output execution)
      creates sourceCoins uniforms bases decaps roots)
    (acceptedBounded : ∀ output execution, ObserverBounds (observer.accepted output execution)
      creates sourceCoins uniforms bases decaps roots)
    (prepared : Prepared setup Selection) :
    let client := nativeNext kem parameters attachedVerify primitives setup observer prepared
    client.IsQueryBoundP IsMlKemUniformQuery (uEphemeral + (uNative + (32 * creates + sourceCoins + uniforms))) ∧
    client.IsQueryBoundP IsMlKemBaseQuery (bEphemeral + (bNative + bases)) ∧
    client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (decaps + roots) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nativeNext_bound kem parameters attachedVerify primitives setup observer IsMlKemUniformQuery
      _ _ _ ephemeralUniform nativeUniform
      (fun challenge output execution state => (observe_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (bounded _ _)).1)
      (fun challenge output execution state => (acceptedObserve_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (acceptedBounded _ _)).1) prepared
  · exact nativeNext_bound kem parameters attachedVerify primitives setup observer IsMlKemBaseQuery
      _ _ _ ephemeralBase nativeBase
      (fun challenge output execution state => (observe_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (bounded _ _)).2.1)
      (fun challenge output execution state => (acceptedObserve_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (acceptedBounded _ _)).2.1) prepared
  · simpa only [Nat.zero_add] using nativeNext_bound kem parameters attachedVerify primitives setup observer
      IsMlKemLogicalDecapsulationQuery 0 0 (decaps + roots) (ccaAmbient_no_decap parameters.ephemeralGen)
      (fun target => ccaAmbient_no_decap (parameters.native.encaps target))
      (fun challenge output execution state => (observe_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (bounded _ _)).2.2)
      (fun challenge output execution state => (acceptedObserve_bounds parameters.source challenge attachedVerify primitives 1
        setup observer output execution state creates sourceCoins uniforms bases decaps roots (acceptedBounded _ _)).2.2) prepared

end BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.localObserve_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.localObserve_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.observe_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.observe_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.localAccepted_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.localAccepted_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.acceptedObserve_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.acceptedObserve_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.acceptedCommon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.acceptedCommon_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.allCandidateCommon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.allCandidateCommon_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.targetAfterEncapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.targetAfterEncapsulation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.nativeNext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.nativeNext_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.dispatch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.dispatch_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_prefix_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_resume_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_resume_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.actualGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.actualGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.actualGame_uniform_from_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.actualGame_uniform_from_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.rootProtocol_sampler_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.correlated_world_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.correlated_world_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.nativeNext_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateAcceptedRootBounds.nativeNext_observer_bounds
