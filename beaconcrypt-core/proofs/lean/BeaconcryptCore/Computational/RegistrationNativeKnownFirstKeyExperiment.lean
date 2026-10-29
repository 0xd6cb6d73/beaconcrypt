-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource

/-! The actual chronological known-first observation has one global five-hop key experiment. Its independent source challenges are sampled inside the executable key adversary before the dependent native frontend; the final internal matching decision never changes the public candidate prefix. All query bills come from the original public budget. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
open RegistrationNativeKnownFirstKeySource (client observe matched)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def g1 (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
    (matched setup seed scalar <$> RegistrationNativeRootCandidates.rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))).run' ∅

noncomputable def entryClient (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) : OracleComp RegistrationNativeKeyHybrid.Spec Bool := do
  let seed ← simulateQ RegistrationNativeKeyCompiler.coins PqxdhJointIdentity.sampleSeed
  let scalar ← simulateQ RegistrationNativeKeyCompiler.coins PqxdhJointGapDh.sampleScalar
  RegistrationNativeKeyCompiler.client setup.source
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
    (RegistrationNativeRetainedService.client (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary seed scalar
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar))) RegistrationNativeKeyPhases.emptyMeta

theorem client_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge) :
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary seed scalar publicValue).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand (budget.cap 4 + budget.cap 5) := by
  unfold client
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
    intro coin
    simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]
  · intro initialized _reached
    cases initialized.1 with
    | none => trivial
    | some started =>
        apply RegistrationNativePublicCaps.retained_bound
        rw [isQueryBoundP_map_iff]
        unfold RegistrationNativeG2Trace.program
        apply RegistrationNativeG2Trace.program_bound
        exact RegistrationNativePublicCaps.run_bound setup checks wire source
          (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey serverKeyId bounds mode
          (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) started.frontend

private theorem coin_free {Result : Type} (work : ProbComp Result) :
    (simulateQ RegistrationNativeKeyCompiler.coins work).IsQueryBoundP
      (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeKeyCompiler.coins, PqxdhRegistrationJointKemSecondEntry.IsValue, isQueryBoundP_query_iff]

theorem entry_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary).IsQueryBoundP
      (PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := PqxdhServerAuthKeySchedule.Output))
      (budget.cap 4 + budget.cap 5) := by
  unfold entryClient
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (coin_free _) ?_).mono (by omega)
  intro seed _seed
  refine (isQueryBoundP_bind (n := 0) (m := budget.cap 4 + budget.cap 5) (coin_free _) ?_).mono (by omega)
  intro scalar _scalar
  apply RegistrationNativeKeyBounds.client_bound
  exact RegistrationNativeRetainedService.client_bound _ _
    (client_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded seed scalar _)

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

theorem hybrid_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    g1 (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary =ᵈ
      RegistrationNativeKeyHybrid.hybrid setup.source setup.hmac (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) 0 := by
  unfold g1 RegistrationNativeKeyHybrid.hybrid entryClient
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, indexed_coins, bind_map_left, map_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  rw [← StateT.run'_eq, RegistrationNativeKnownFirstKeySource.root_source,
    RegistrationNativeRetainedSource.source_phase]
  exact EvalDistEq.of_evalDist_eq (RegistrationNativeKeyServiceBound.g1_hybrid setup.source setup.hmac _ _ _)

attribute [local irreducible] entryClient g1 RegistrationNativeG2Observer.nativeClient
  RegistrationNativeKnownFirstKeySource.client

theorem normal_eq (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
      (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (observe setup)) =
      RegistrationNativeKeyHybrid.uniform (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) := by
  unfold RegistrationNativeG2Observer.nativeClient
  rw [RegistrationNativeOpenKeyKemSource.normal_source]
  apply congrArg (fun work => (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl work).run' ∅)
  unfold RegistrationNativeG2Observer.client entryClient
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind,
    RegistrationNativeOpenKeyStartupSource.coins_close, bind_map_left, map_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [← StateT.run'_eq, RegistrationNativeOpenKeyClosure.key_close,
    RegistrationNativeKnownFirstKeySource.retained_real]

theorem key_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue)) :
    (g1 (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary).boolDistance
      (RegistrationNativeOpenKeyKemGame.normal setup.baseImpl setup.kem
        (RegistrationNativeG2Observer.nativeClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary (observe setup))) ≤
      ∑ index ∈ Finset.range (budget.cap 4 + budget.cap 5), RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
        (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac (entryClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary) index) := by
  rw [normal_eq]
  have first := hybrid_zero (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary
  unfold ProbComp.boolDistance
  rw [first.evalDist_eq]
  exact RegistrationNativeKeyHybrid.bound setup.source setup.hmac correct _ _
    (entry_bound setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary budget bounded)

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.client_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.entry_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.entry_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.hybrid_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.hybrid_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.normal_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.normal_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyExperiment.key_bound
