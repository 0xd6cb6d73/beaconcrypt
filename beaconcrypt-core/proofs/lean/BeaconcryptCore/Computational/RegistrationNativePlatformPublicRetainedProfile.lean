-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained
import BeaconcryptCore.Computational.RegistrationNativeDecisionRetainedStartup
/-! Literal generated startup and the corrected full raw frontend form a retained prepare/material client. The private service owns root and PRK bookkeeping; source values, all ledger decisions and persistent platform outcomes are preserved. Full material replies are still exposed at this intermediate key-schedule interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedProfile
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
    (decision : Value × RegistrationNativeLedger.State → Bool)

noncomputable def observed (publicValue : PqxdhJointGapDh.PublicChallenge)
    (started : RegistrationNativePublicStartup.Started source) (previous : Platform) :
    OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (Bool × Platform) :=
  (fun result => (decision result.1, result.2.2)) <$>
    RegistrationNativePlatformPublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source started.credential)
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
      RegistrationNativePlatformPublicRetained.client setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
        (RegistrationNativeMldsa.owned source started.credential)
        (observed setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue started previous)
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 }

/-- Actual startup and every subsequent source callback retain the same decision and P while root bookkeeping moves to the private service. -/
theorem client_source (publicValue : PqxdhJointGapDh.PublicChallenge)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (previous : Platform) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      (RegistrationNativePlatformPublicSourceProfile.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous)).run' ∅ =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous)).run'
          RegistrationNativeRetainedSource.initial := by
  simp only [RegistrationNativePlatformPublicSourceProfile.client, client, StateT.run'_eq, simulateQ_bind,
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
      have comparison := RegistrationNativePlatformPublicRetained.client_source setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route
        (RegistrationNativeMldsa.owned source started.credential) seed scalar
        (observed (n := n) setup checks wire source serverKeyId selectedOwner selectedAccept view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue started previous)
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 } ∅
      simp only [RegistrationNativePlatformPublicSourceFull.run, observed, StateT.run'_eq, simulateQ_map,
        StateT.run_map, bind_pure_comp, Functor.map_map, RegistrationNativePublicInterpreter.initial,
        RegistrationNativeRetainedSource.initial] at comparison ⊢
      convert comparison using 1; rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedProfile.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetainedProfile.client_source
