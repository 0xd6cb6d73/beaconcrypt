import BeaconcryptCore.Computational.PqxdhAuthenticatedRootCommonBounds

/-!
The ordinary preparation ledger includes the actual generated source prefix, every common/rejected post-registration schedule and the additional encapsulation on an eligible root-failure branch. The outer ordinary challenger encapsulation remains a separate charge. Primitive and generator contracts below are only resource bounds on their actual oracle programs; they do not replace authentication, source fidelity or any computational security endpoint.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhGeneratedBeaconState PqxdhAuthenticatedRootExperiment
open PqxdhPrivateAcceptedRoot PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhCorrelatedRootQueryBounds PqxdhChallengeSecretQueryBounds PqxdhPrivateAcceptedRootBounds
open PqxdhPhase2SourceSchedulerBounds PqxdhAuthenticatedRootCommonBounds
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A KemSK : Type} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (qLocal : Nat) (localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal)
    (budget : Budget) (postBound : ∀ choice response, Bounded (post choice response) budget)
    (qAux : Nat) (auxBound : ∀ query state, ((env.aux query).run state).IsTotalQueryBound qAux)

/-- Resource caps at the exact ordinary CCA query interface, covering every possible reply. -/
structure Caps {Result : Type} (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (uniform base decapsulation : Nat) : Prop where
  uniforms : client.IsQueryBoundP IsMlKemUniformQuery uniform
  bases : client.IsQueryBoundP IsMlKemBaseQuery base
  decaps : client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery decapsulation

include localBound postBound in
/-- All rejected/common completed executions pay actual source identity creation and both coin channels before ordinary CCA interpretation. -/
theorem observe_caps
    (challenge : Option MlKem768Ciphertext)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : PqxdhPhase1AcceptanceOracle.BareState 1) :
    let total := commonBill qLocal qAux budget
    Caps (PqxdhPrivateAcceptedRoot.observe env.source challenge attachedVerify primitives 1 setup
      (commonObserver env program post) output execution state) (34 * total) total total := by
  have caps := PqxdhPrivateAcceptedRootBounds.observe_bounds env.source challenge attachedVerify primitives 1 setup
    (commonObserver env program post) output execution state
    _ _ _ _ _ _ (completed_bounds env program post qLocal localBound budget postBound qAux output execution)
  refine ⟨?_, caps.2.1, ?_⟩
  · exact caps.1.mono (by omega)
  · simpa only [Nat.add_zero] using caps.2.2

include localBound postBound auxBound in
/-- Accepted common candidates include the complete builder and source scheduler, without inserting target-root requests. -/
theorem acceptedObserve_caps
    (challenge : Option MlKem768Ciphertext)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome
      (PqxdhPrivatePhase1Prefix.Retained setup Unit (driver env.toDriverEnvironment program).State)))
    (execution : Ready) (state : PqxdhPhase1AcceptanceOracle.BareState 1) :
    let total := commonBill qLocal qAux budget
    Caps (PqxdhPrivateAcceptedRoot.acceptedObserve env.source challenge attachedVerify primitives 1 setup
      (commonObserver env program post) output execution state) (34 * total) total total := by
  have caps := PqxdhPrivateAcceptedRootBounds.acceptedObserve_bounds env.source challenge attachedVerify primitives 1 setup
    (commonObserver env program post) output execution state
    _ _ _ _ _ _ (accepted_bounds env program post qLocal localBound budget postBound qAux auxBound output execution)
  refine ⟨?_, caps.2.1, ?_⟩
  · exact caps.1.mono (by omega)
  · simpa only [Nat.add_zero] using caps.2.2

include localBound postBound auxBound in
/-- Actual dispatch counts every common source continuation and either optional native or total failure-branch encapsulation. The outer ordinary challenger is a separate later charge. -/
theorem dispatch_caps
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (uEp bEp dEp uNative bNative dNative uTotal bTotal dTotal : Nat)
    (ephemeralBound : Caps (ccaAmbient env.ephemeralGen) uEp bEp dEp)
    (nativeBound : ∀ key, Caps (ccaAmbient (env.native.encaps key)) uNative bNative dNative)
    (totalBound : ∀ key, Caps (ccaAmbient (kem.encaps key)) uTotal bTotal dTotal)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State) :
    let total := commonBill qLocal qAux budget
    Caps (PqxdhPrivateAcceptedRoot.dispatch kem env.parameters attachedVerify primitives setup
      (commonObserver env program post) prepared)
      (uEp + (max uNative uTotal + 34 * total))
      (bEp + (max bNative bTotal + total))
      (dEp + (max dNative dTotal + total)) := by
  let rejected := observe_caps env program post attachedVerify primitives qLocal localBound budget postBound qAux
  let accepted := acceptedObserve_caps env program post attachedVerify primitives qLocal localBound budget postBound qAux auxBound
  refine ⟨?_, ?_, ?_⟩
  · exact PqxdhPrivateAcceptedRootBounds.dispatch_bound kem env.parameters attachedVerify primitives setup
      (commonObserver env program post) IsMlKemUniformQuery _ _ _ _ ephemeralBound.uniforms
      (fun key => (nativeBound key).uniforms) (fun key => (totalBound key).uniforms)
      (fun challenge output execution state => (rejected challenge output execution state).uniforms)
      (fun challenge output execution state => (accepted challenge output execution state).uniforms) prepared
  · exact PqxdhPrivateAcceptedRootBounds.dispatch_bound kem env.parameters attachedVerify primitives setup
      (commonObserver env program post) IsMlKemBaseQuery _ _ _ _ ephemeralBound.bases
      (fun key => (nativeBound key).bases) (fun key => (totalBound key).bases)
      (fun challenge output execution state => (rejected challenge output execution state).bases)
      (fun challenge output execution state => (accepted challenge output execution state).bases) prepared
  · exact PqxdhPrivateAcceptedRootBounds.dispatch_bound kem env.parameters attachedVerify primitives setup
      (commonObserver env program post) IsMlKemLogicalDecapsulationQuery _ _ _ _ ephemeralBound.decaps
      (fun key => (nativeBound key).decaps) (fun key => (totalBound key).decaps)
      (fun challenge output execution state => (rejected challenge output execution state).decaps)
      (fun challenge output execution state => (accepted challenge output execution state).decaps) prepared

include localBound in
/-- Non-uniform classes of the actual borrowed prefix include both source samplers and the complete driver; its identity seed makes no such calls. -/
theorem prefix_class
    (qWrite : Nat) (writerBound : ∀ fields state, ((env.phase1Writer fields).run state).IsTotalQueryBound qWrite)
    (preBudget : Budget) (preBound : ∀ reply, Bounded (program.main reply) preBudget)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin)))
    (qPrekey qOneTime : Nat)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP predicate qPrekey)
    (oneTimeBound : ∀ identity before key, (ccaAmbient (setup.oneTime identity before key)).IsQueryBoundP predicate qOneTime)
    (key : TargetKemPublicKey) :
    (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup (driver env.toDriverEnvironment program) key).IsQueryBoundP
      predicate (qPrekey + (qOneTime + (qWrite + bill qLocal preBudget))) := by
  simpa only [Nat.zero_add] using PqxdhGeneratedRootQueryBounds.borrowedPrefix_bound attachedVerify primitives setup
    (driver env.toDriverEnvironment program) predicate 0 qPrekey qOneTime (qWrite + bill qLocal preBudget)
    (PqxdhPrivateRootQueryBounds.ccaCoins_excluded PqxdhJointIdentity.sampleSeed predicate excluded)
    prekeyBound oneTimeBound
    (fun index identity generated transcript state => PqxdhPhase2GeneratedDriverResources.driver_class env.toDriverEnvironment program
      attachedVerify primitives 1 qWrite writerBound qLocal localBound preBudget preBound predicate excluded
      index identity generated transcript state) key

include localBound in
/-- The original generated prefix has explicit uniform, base and logical-decapsulation caps, including both actual prekey and one-time samplers. -/
theorem prefix_caps
    (qWrite : Nat) (writerBound : ∀ fields state, ((env.phase1Writer fields).run state).IsTotalQueryBound qWrite)
    (preBudget : Budget) (preBound : ∀ reply, Bounded (program.main reply) preBudget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (ForwardedSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (ForwardedSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating) 0)
    (uPrekey bPrekey dPrekey uOneTime bOneTime dOneTime : Nat)
    (prekeyBound : ∀ identity, Caps (ccaAmbient (setup.prekey identity)) uPrekey bPrekey dPrekey)
    (oneTimeBound : ∀ identity before key, Caps (ccaAmbient (setup.oneTime identity before key)) uOneTime bOneTime dOneTime)
    (key : TargetKemPublicKey) :
    let driverCost := qWrite + bill qLocal preBudget
    Caps (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup (driver env.toDriverEnvironment program) key)
      (32 + (uPrekey + (uOneTime + 2 * driverCost)))
      (bPrekey + (bOneTime + driverCost)) (dPrekey + (dOneTime + driverCost)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact PqxdhPhase2GeneratedDriverResources.prefix_uniform env.toDriverEnvironment program attachedVerify primitives
      uPrekey uOneTime (fun identity => (prekeyBound identity).uniforms)
      (fun identity before target => (oneTimeBound identity before target).uniforms)
      qWrite writerBound qLocal localBound preBudget preBound noSign noCreate key
  · exact prefix_class env program attachedVerify primitives qLocal localBound qWrite writerBound preBudget preBound
      IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) bPrekey bOneTime
      (fun identity => (prekeyBound identity).bases) (fun identity before target => (oneTimeBound identity before target).bases) key
  · exact prefix_class env program attachedVerify primitives qLocal localBound qWrite writerBound preBudget preBound
      IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) dPrekey dOneTime
      (fun identity => (prekeyBound identity).decaps) (fun identity before target => (oneTimeBound identity before target).decaps) key

include localBound postBound auxBound in
/-- The exact executable protocol preparation pays the original generated prefix and every common or rejected source continuation, including the failure-branch encapsulation. -/
theorem prepare_caps
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (qWrite : Nat) (writerBound : ∀ fields state, ((env.phase1Writer fields).run state).IsTotalQueryBound qWrite)
    (preBudget : Budget) (preBound : ∀ reply, Bounded (program.main reply) preBudget)
    (noSign : ∀ reply, (program.main reply).IsQueryBoundP
      (ForwardedSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (noCreate : ∀ reply, (program.main reply).IsQueryBoundP
      (ForwardedSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating) 0)
    (uPrekey bPrekey dPrekey uOneTime bOneTime dOneTime : Nat)
    (prekeyBound : ∀ identity, Caps (ccaAmbient (setup.prekey identity)) uPrekey bPrekey dPrekey)
    (oneTimeBound : ∀ identity before key, Caps (ccaAmbient (setup.oneTime identity before key)) uOneTime bOneTime dOneTime)
    (uEp bEp dEp uNative bNative dNative uTotal bTotal dTotal : Nat)
    (ephemeralBound : Caps (ccaAmbient env.ephemeralGen) uEp bEp dEp)
    (nativeBound : ∀ key, Caps (ccaAmbient (env.native.encaps key)) uNative bNative dNative)
    (totalBound : ∀ key, Caps (ccaAmbient (kem.encaps key)) uTotal bTotal dTotal)
    (key : TargetKemPublicKey) :
    let driverCost := qWrite + bill qLocal preBudget
    let commonCost := commonBill qLocal qAux budget
    Caps ((protocol env kem attachedVerify primitives program post).prepare key)
      ((32 + (uPrekey + (uOneTime + 2 * driverCost))) + (uEp + (max uNative uTotal + 34 * commonCost)))
      ((bPrekey + (bOneTime + driverCost)) + (bEp + (max bNative bTotal + commonCost)))
      ((dPrekey + (dOneTime + driverCost)) + (dEp + (max dNative dTotal + commonCost))) := by
  let prefixCaps := prefix_caps env program attachedVerify primitives qLocal localBound qWrite writerBound preBudget preBound
    noSign noCreate uPrekey bPrekey dPrekey uOneTime bOneTime dOneTime prekeyBound oneTimeBound key
  let dispatch := dispatch_caps env program post attachedVerify primitives qLocal localBound budget postBound qAux auxBound kem
    uEp bEp dEp uNative bNative dNative uTotal bTotal dTotal ephemeralBound nativeBound totalBound
  exact ⟨isQueryBoundP_bind prefixCaps.uniforms (fun prepared _ => (dispatch prepared).uniforms),
    isQueryBoundP_bind prefixCaps.bases (fun prepared _ => (dispatch prepared).bases),
    isQueryBoundP_bind prefixCaps.decaps (fun prepared _ => (dispatch prepared).decaps)⟩

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.observe_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.observe_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.acceptedObserve_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.acceptedObserve_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.dispatch_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.dispatch_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.prefix_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.prefix_class

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.prefix_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.prefix_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.prepare_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds.prepare_caps
