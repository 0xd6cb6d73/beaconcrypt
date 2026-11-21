-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordProfile
import BeaconcryptCore.Computational.RegistrationNativeDecisionRetainedStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySeedProfile
/-! Actual generated startup and the terminal cache/produced/raw observation compile into the private retained material service. Common platform outcomes and every source failure remain literal. The intermediate compiler still owns full material and its local World; this is not an opaque-client World-read capability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile
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

noncomputable def observed (publicValue : PqxdhJointGapDh.PublicChallenge)
    (started : RegistrationNativePublicStartup.Started source) (previous : Platform) :=
  RegistrationNativePlatformPublicFrontend.run (n := n) setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
    selectedOwner selectedAccept publicValue.prekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) (started.frontend, previous)

noncomputable def client (publicValue : PqxdhJointGapDh.PublicChallenge) (previous : Platform) :
    OracleComp RegistrationNativeRetainedService.Spec (Bool × Platform) := do
  let initialized ← simulateQ RegistrationNativePublicRetained.coins
    ((RegistrationNativePublicStartupFrame.startup (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
      PqxdhRecordLiftWorld.initial)
  match initialized.1 with
  | none => pure (false, previous)
  | some started =>
    (fun result => (decision result.1.1 result.2, result.1.2.2)) <$>
      RegistrationNativePlatformPublicRetainedRecord.client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
        (RegistrationNativeMldsa.owned source started.credential)
        (observed setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary publicValue started previous)
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 }

/-- The complete initialized record-data decision retains its source cache/produced/raw fields and P when the actual root memo is relocated to the private material service. -/
theorem client_source (publicValue : PqxdhJointGapDh.PublicChallenge)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (previous : Platform) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      (RegistrationNativePlatformPublicRecordProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous)).run' ∅ =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous)).run'
          RegistrationNativeRetainedSource.initial := by
  simp only [RegistrationNativePlatformPublicRecordProfile.client, client, StateT.run'_eq, simulateQ_bind,
    StateT.run_bind, map_bind]
  rw [RegistrationNativeDecisionRetainedStartup.start_root]
  simp only [bind_map_left]
  delta RegistrationNativePublicRetained.coins
  rw [RegistrationNativePublicRootCoins.retained_coins]
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro initialized _reached
  cases initialized.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | some started =>
    have compared := RegistrationNativePlatformPublicRetainedRecord.client_source setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
      (RegistrationNativeMldsa.owned source started.credential) seed scalar
      (observed (n := n) setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary publicValue started previous)
      { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 } ∅
    have mapped := congrArg (fun action => (fun result => (decision result.1.1 result.2, result.1.2.2)) <$> action) compared
    simp only [RegistrationNativePlatformPublicSourceFull.run, observed, StateT.run'_eq, simulateQ_map,
      bind_pure_comp,
      StateT.run_map, Functor.map_map, RegistrationNativePublicInterpreter.initial,
      RegistrationNativeRetainedSource.initial] at mapped ⊢
    convert mapped using 1; rfl
omit primitive in
private theorem retained_bound (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {A : Type} (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A)
    (before : RegistrationNativePublicInterpreter.State n KemSK) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicMaterialCaps.IsDemand (n := n) (KemSK := KemSK)) count) :
    (RegistrationNativePlatformPublicRetainedRecord.client setup wire route sign work before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand count := by
  have same := RegistrationNativePlatformPublicRetainedCaps.retained_bound setup wire route sign work before count bounded
  simpa only [RegistrationNativePlatformPublicRetained.client, RegistrationNativePlatformPublicRetainedRecord.client,
    StateT.run'_eq, isQueryBoundP_map_iff] using same

/-- Terminal record-data analysis introduces no request: the complete actual initialized material service retains exactly the original build-plus-finish allowance. -/
theorem client_bound (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicValue, RegistrationNativeInterface.Respects budget (adversary publicValue))
    (publicValue : PqxdhJointGapDh.PublicChallenge) (previous : Platform) :
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous).IsQueryBoundP
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
      rw [isQueryBoundP_map_iff]
      apply retained_bound
      exact RegistrationNativePlatformPublicMaterialCaps.run_bound setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicValue.prekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) budget (bounded _) (started.frontend, previous)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedRecordProfile.client_bound
