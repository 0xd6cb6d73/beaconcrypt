-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconContinuation
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAgreement

/-! Actual public collection, private root preparation and corrected source completion compose on one reached native World. The entire local environment, including all prior record markers, is retained; no empty-ledger assumption or restoration of captured primitive state is required. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPhase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def phase (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (owner : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
      mlSource (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated)
  RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner result

/-- The full post-authentication public program is the actual native agreement controller followed by its actual terminal/open/install continuation. -/
theorem phase_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (env : EnvState RegistrationServerRoleBackend.State)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (erased : Std.Array U8 227#usize) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((phase setup wire (eraseOwner owner) oneTime authenticated).run (eraseOwner current)).run env)).run before = (do
      let reached ← (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar
        (eraseOwner owner) oneTime) (RegistrationAgreementExecutor.beacon authenticated)).run (env, before.2.2)
      Prod.map RegistrationNativePlatformBeaconContinuation.view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((RegistrationNativePlatformBeaconContinuation.sourceAfter setup wire owner reached.1 :
            RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2) := by
  let continueSource := fun reached : RustM agreement.AgreementEffect ×
      RegistrationBeaconReferenceNativeStage.Local n KemSK mlSource =>
    Prod.map RegistrationNativePlatformBeaconContinuation.view id <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationNativePlatformBeaconContinuation.sourceAfter setup wire owner reached.1 :
          RegistrationNativePlatformBeaconOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
            (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2
  have combined := congrArg (fun script => script >>= continueSource)
    (RegistrationBeaconReferenceNativeAgreement.agreement_source setup checks wire representation created scalar credential
      (eraseOwner owner) oneTime authenticated coherent env before)
  simp only [bind_map_left] at combined
  change _ = _ >>= continueSource
  rw [← combined]
  simp only [phase, StateT.run_bind, StateT.run_lift, bind_pure_comp, simulateQ_bind,
    map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨⟨result, afterEnv⟩, afterPrivate⟩
  simpa only [continueSource] using
    RegistrationNativePlatformBeaconContinuation.continuation_source setup checks wire representation created scalar credential
      owner current afterEnv authenticated result erased afterPrivate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPhase.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPhase.phase_source

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPhase
