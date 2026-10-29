-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDecisionKeyBill
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBound

/-! One concrete key-schedule adversary samples the independent source identity/prekey challenges internally, then runs the complete native reference frontend and its original secrecy ledger. Thus the five-loss telescope is stated for ordinary whole-experiment distinguishers, rather than an average of startup-conditioned advantages. Uniform entries are still keyed by the entire literal source input; hidden-install alias and target-origin proofs remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKeyHybrid (Spec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def entryClient (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) : OracleComp Spec Bool := do
  let seed ← simulateQ RegistrationNativeKeyCompiler.coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ RegistrationNativeKeyCompiler.coins PqxdhJointGapDh.sampleScalar
  RegistrationNativeKeyCompiler.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeRetainedService.client
      (RegistrationNativeDecisionRetainedStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)))
    RegistrationNativeKeyPhases.emptyMeta

private theorem coin_free {Result : Type} (work : ProbComp Result) :
    (simulateQ RegistrationNativeKeyCompiler.coins work).IsQueryBoundP
      (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeKeyCompiler.coins, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]

/-- The whole sampled native client has the original build-plus-finish protected material bill. Startup and selected challenge generation add zero material requests. -/
theorem entry_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision).IsQueryBoundP
      (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) (budget.cap 4 + budget.cap 5) := by
  unfold entryClient
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (coin_free _) ?_).mono (by omega)
  intro seed _seed
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (coin_free _) ?_).mono (by omega)
  intro scalar _scalar
  apply RegistrationNativeKeyBounds.client_bound
  exact RegistrationNativeRetainedService.client_bound _ _
    (RegistrationNativeDecisionKeyBill.client_bound setup checks wire route source ensureInit identityIndex serverKeyId
      selectedOwner selectedAccept bounds mode adversary decision budget bounded _)

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

/-- The zero indexed-key hybrid is exactly the correlated ideal-root native execution after its proved retained-root erasure and prepare-time deferral. -/
theorem hybrid_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision) =ᵈ
      RegistrationNativeKeyHybrid.hybrid setup.source setup.hmac
        (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision) 0 := by
  rw [RegistrationNativeRootCacheProjection.game_project setup.source setup.hmac correct]
  unfold RegistrationNativeKeyHybrid.hybrid entryClient
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, indexed_coins, bind_map_left, map_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  rw [← StateT.run'_eq]
  rw [RegistrationNativeDecisionRetainedStartup.client_source, RegistrationNativeRetainedSource.source_phase]
  exact EvalDistEq.of_evalDist_eq (RegistrationNativeKeyServiceBound.g1_hybrid setup.source setup.hmac _ _ _)

/-- The actual complete native ideal-root client incurs the five standard primitive losses through one explicit global entry client with the derived original command bill. -/
theorem key_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
      (RegistrationNativePublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision)).boolDistance
      (RegistrationNativeKeyHybrid.uniform
        (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision)) ≤
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
          (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision) index) := by
  have first := hybrid_zero (n := n) setup checks wire route source correct.root ensureInit identityIndex serverKeyId
    selectedOwner selectedAccept bounds mode adversary decision
  unfold ProbComp.boolDistance
  rw [first.evalDist_eq]
  exact RegistrationNativeKeyHybrid.bound setup.source setup.hmac correct _ _
    (entry_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary decision budget bounded)

end BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment.entry_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment.entry_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment.hybrid_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment.hybrid_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionKeyExperiment.key_bound
