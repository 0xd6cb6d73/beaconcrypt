-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile
import BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment
/-! Concrete related-root and key-schedule reductions retain terminal CTX-cache, produced-frame and raw-counter observations of the actual initialized dynamic runtime. This is still the full-material private compiler hop; the public opaque-slot record experiment remains a separate interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → RegistrationNativePlatformPublicWorldObservation.RecordView → Bool)

noncomputable def rootClient (previous : Platform) (publicValue : PqxdhJointGapDh.PublicChallenge) :
    OracleComp RegistrationNativeRelatedRoot.RootSpec Bool :=
  Prod.fst <$> RegistrationNativePlatformPublicRecordProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous

noncomputable def phaseClient (previous : Platform) (publicValue : PqxdhJointGapDh.PublicChallenge) :
    OracleComp RegistrationNativeRetainedService.Spec Bool :=
  Prod.fst <$> RegistrationNativePlatformPublicRetainedRecordProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous

noncomputable def entryClient (previous : Platform) : OracleComp RegistrationNativeKeyHybrid.Spec Bool := do
  let seed ← simulateQ RegistrationNativeKeyCompiler.coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ RegistrationNativeKeyCompiler.coins PqxdhJointGapDh.sampleScalar
  RegistrationNativeKeyCompiler.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeRetainedService.client
      (phaseClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)))
    RegistrationNativeKeyPhases.emptyMeta

omit primitive in
private theorem indexed_coins {Result : Type} (sampler : Nat → ProbComp PqxdhServerAuthKeySchedule.Output)
    (work : ProbComp Result)
    (before : PqxdhRegistrationJointKemSecondEntry.IState Pqxdh.Bytes PqxdhServerAuthKeySchedule.Output) :
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.indexedImpl sampler)
      (simulateQ RegistrationNativeKeyCompiler.coins work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : PqxdhRegistrationJointKemSecondEntry.indexedImpl sampler ∘ₛ RegistrationNativeKeyCompiler.coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (PqxdhRegistrationJointKemSecondEntry.IState Pqxdh.Bytes PqxdhServerAuthKeySchedule.Output) ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self, StateT.run_liftM, bind_pure_comp]

/-- The literal initialized corrected ideal-root decision equals the zero key-schedule hybrid of this actual whole-runtime client. -/
theorem hybrid_zero (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac) (previous : Platform) :
    RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) =ᵈ
      RegistrationNativeKeyHybrid.hybrid setup.source setup.hmac
        (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous) 0 := by
  rw [RegistrationNativeRootCacheProjection.game_project setup.source setup.hmac correct]
  unfold RegistrationNativeKeyHybrid.hybrid entryClient
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, indexed_coins, bind_map_left, map_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  rw [← StateT.run'_eq]
  have relocated := RegistrationNativePlatformPublicRetainedRecordProfile.client_source (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) seed scalar previous
  have decisionOnly := congrArg (Functor.map Prod.fst) relocated
  have related : (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run' ∅ =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (phaseClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run'
          RegistrationNativeRetainedSource.initial := by
    simpa only [rootClient, phaseClient, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] using decisionOnly
  rw [related, RegistrationNativeRetainedSource.source_phase]
  exact EvalDistEq.of_evalDist_eq (RegistrationNativeKeyServiceBound.g1_hybrid setup.source setup.hmac _ _ _)
/-- The original initialized dynamic runtime decision pays exactly the ordinary related-input advantage of its concrete source client. -/
theorem family_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac) (previous : Platform) :
    (Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1)
        (RegistrationNativePlatformPublicWorldObservation.recordView (RegistrationNativePlatformPublicWorldObservation.world result.2.2)))).run previous).boolDistance
      (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
        (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous)) =
      RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
        (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
          (rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous publicValue)) := by
  have original := RegistrationNativePlatformPublicRecordProfile.decision_source (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct previous
  unfold ProbComp.boolDistance
  rw [original.evalDist_eq]
  exact RegistrationNativeRelatedRoot.advantage_exact setup.source setup.hmac correct setup.joint setup.dh _

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment.hybrid_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment.hybrid_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment.family_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordKeyExperiment.family_distance
