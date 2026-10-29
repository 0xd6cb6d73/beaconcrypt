-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRootCandidatesFamily
import BeaconcryptCore.Computational.RegistrationNativeKnownInputBatchBound
import BeaconcryptCore.Computational.RegistrationNativeOpenG2Bound

/-! The concrete chronological supplied-first observation has its actual closed retained client. Selected secrets occur only in the final internal analysis decision and in key-game challenge generation. The executable candidate prefix receives only the public challenge. Startup, the complete original ledger, shared World and all failed branches remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def observe (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (outcome : RegistrationNativeG2Observer.Outcome Value) : Bool := by
  classical
  exact decide (RegistrationNativeKnownInputBatchBound.Matches setup.joint setup.dh seed scalar
    (RegistrationNativeG2Candidates.candidates outcome.2))

noncomputable def matched (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidates : List PqxdhJointIdentity.DhOutput) : Bool := by
  classical
  exact decide (RegistrationNativeKnownInputBatchBound.Matches setup.joint setup.dh seed scalar candidates)

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (seed : IdentitySeed) (scalar : ScalarBytes)
    (publicValue : PublicChallenge) : OracleComp RegistrationNativeRetainedService.Spec Bool := do
  let initialized ← simulateQ RegistrationNativePublicRetained.coins
    ((RegistrationNativePublicStartupFrame.startup (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
      PqxdhRecordLiftWorld.initial)
  match initialized.1 with
  | none => pure false
  | some started =>
      RegistrationNativePublicRetained.client setup wire route
        (RegistrationNativeMldsa.owned source started.credential)
        ((fun result => observe setup seed scalar (result.1.1, result.2)) <$>
          RegistrationNativeG2Trace.program (RegistrationNativeRootCandidates.work setup checks wire source
            selectedOwner selectedAccept publicValue serverKeyId bounds mode adversary started))
        { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 }

theorem root_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      (matched setup seed scalar <$> RegistrationNativeRootCandidates.rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary publicValue)).run' ∅ =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary seed scalar publicValue)).run'
          RegistrationNativeRetainedSource.initial := by
  simp only [RegistrationNativeRootCandidates.rootClient, client, map_bind, StateT.run'_eq,
    simulateQ_bind, simulateQ_map, StateT.run_bind]
  rw [RegistrationNativePublicRetainedStartup.start_root]
  simp only [bind_map_left]
  delta RegistrationNativePublicRetained.coins
  rw [RegistrationNativePublicRootCoins.retained_coins]
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro initialized _reached
  cases initialized.1 with
  | none => simp [simulateQ_pure, StateT.run_pure, matched, RegistrationNativeKnownInputBatchBound.Matches]
  | some started =>
      have comparison := RegistrationNativePublicRetained.client_source setup wire route
        (RegistrationNativeMldsa.owned source started.credential) seed scalar
          ((fun result => observe setup seed scalar (result.1.1, result.2)) <$>
          RegistrationNativeG2Trace.program (RegistrationNativeRootCandidates.work setup checks wire source
            selectedOwner selectedAccept publicValue serverKeyId bounds mode adversary started))
          { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 } ∅
      simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
        RegistrationNativePublicInterpreter.initial, RegistrationNativeRetainedSource.initial,
        observe, matched] at comparison ⊢
      convert comparison using 1 <;> rfl

theorem retained_real (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge) :
    (simulateQ (RegistrationNativeOpenRetainedSource.close (RegistrationNativeOpenRetainedReal.provider setup))
      (RegistrationNativeG2Observer.retained (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary
        (observe setup seed scalar) publicValue)).run' (PqxdhLiveKemBirth.empty, ()) =
      client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary seed scalar publicValue := by
  unfold RegistrationNativeG2Observer.retained client
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind,
    RegistrationNativeOpenRetainedStartupSource.start_real, bind_map_left, map_bind]
  apply bind_congr
  intro initialized
  cases initialized.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | some started =>
      simp only []
      rw [← StateT.run'_eq]
      exact RegistrationNativeOpenRetainedReal.client_real setup wire route _ _ _

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource.root_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource.retained_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource.retained_real
