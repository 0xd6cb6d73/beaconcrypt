-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedReal
import BeaconcryptCore.Computational.RegistrationNativeOpenRetainedStartup
import BeaconcryptCore.Computational.RegistrationNativeDecisionRetainedStartup

/-! Closing the complete generated open client with the literal real KEM provider gives the existing actual retained experiment. Constructor, ML, pin hash and optional failures occur at their original positions, with one shared World/cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- The complete actual startup draw leaves the external key pool untouched. -/
theorem start_real (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : PqxdhLiveKemBirth.Pool KemSK × Unit) :
    (simulateQ (RegistrationNativeOpenRetainedSource.close (RegistrationNativeOpenRetainedReal.provider setup))
      (RegistrationNativeOpenRetainedStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity)).run before =
      (fun result => (result, before)) <$> simulateQ RegistrationNativePublicRetained.coins
        ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run
          (PqxdhRecordLiftWorld.initial (n := n))) := by
  unfold RegistrationNativeOpenRetainedStartup.start RegistrationNativeOpenRetainedStartup.coins
  rw [QueryImpl.simulateQ_compose]
  exact RegistrationNativeOpenRetainedSource.base_program _ _ before

/-- The full raw/secrecy open experiment preserves every literal original-ledger decision through the actual retained client, without a startup or source-game equality premise. -/
theorem client_real (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)
    (publicValue : PqxdhJointGapDh.PublicChallenge) :
    (simulateQ (RegistrationNativeOpenRetainedSource.close (RegistrationNativeOpenRetainedReal.provider setup))
      (RegistrationNativeOpenRetainedStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision publicValue)).run' (PqxdhLiveKemBirth.empty, ()) =
      RegistrationNativeDecisionRetainedStartup.client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId
        selectedOwner selectedAccept bounds mode adversary decision publicValue := by
  unfold RegistrationNativeOpenRetainedStartup.client RegistrationNativeDecisionRetainedStartup.client
  simp only [StateT.run'_eq, simulateQ_bind, StateT.run_bind, start_real, bind_map_left, map_bind]
  apply bind_congr
  intro initialized
  cases initialized.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | some started =>
      simp only []
      rw [← StateT.run'_eq]
      change (simulateQ (RegistrationNativeOpenRetainedSource.close (RegistrationNativeOpenRetainedReal.provider setup))
        (RegistrationNativeOpenRetained.client setup wire route (RegistrationNativeMldsa.owned source started.credential)
          (RegistrationNativeDecisionRetainedStartup.observed setup checks wire source selectedOwner selectedAccept publicValue
            serverKeyId bounds mode adversary decision started)
          { (RegistrationNativePublicInterpreter.initial (n := n) (KemSK := KemSK)) with world := initialized.2 })).run'
            (PqxdhLiveKemBirth.empty, ()) = _
      exact RegistrationNativeOpenRetainedReal.client_real setup wire route _ _ _

end BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource.start_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource.start_real
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource.client_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecisionOpenRetainedSource.client_real
