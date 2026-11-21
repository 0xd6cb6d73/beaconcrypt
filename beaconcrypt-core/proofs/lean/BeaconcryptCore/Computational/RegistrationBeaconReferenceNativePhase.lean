-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation
import BeaconcryptCore.Computational.RegistrationBeaconReferenceAgreementScope
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger

/-! Actual public collection, private root preparation and the complete finishing continuation compose on one reached native World. The record-request ledger is an analysis field initialized empty in the public compiler; its preservation is derived from the concrete preparation callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeInterpreter (State implementation)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

noncomputable def phase (setup : Setup base KemSK) (owner : SelectedOwner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State)
      mlSource (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated)
  RegistrationBeaconReferenceNativeContinuation.afterPrepared setup.source owner result

/-- The full post-authentication public program is the actual native agreement controller followed by its actual terminal/open/install continuation. -/
theorem phase_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (env : EnvState RegistrationServerRoleBackend.State) (empty : env.recordRequests = [])
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (erased : Std.Array U8 227#usize) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((phase setup (eraseOwner owner) oneTime authenticated).run (eraseOwner current)).run env)).run before = (do
      let reached ← (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar
        (eraseOwner owner) oneTime) (RegistrationAgreementExecutor.beacon authenticated)).run (env, before.2.2)
      Prod.map RegistrationBeaconReferenceNativeContinuation.view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((RegistrationBeaconReferenceNativeContinuation.sourceAfter setup wire owner reached.1 :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2) := by
  let continueSource := fun reached : RustM agreement.AgreementEffect ×
      RegistrationBeaconReferenceNativeStage.Local n KemSK mlSource =>
    Prod.map RegistrationBeaconReferenceNativeContinuation.view id <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationBeaconReferenceNativeContinuation.sourceAfter setup wire owner reached.1 :
          RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
            (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2
  have combined := congrArg (fun script => script >>= continueSource)
    (RegistrationBeaconReferenceNativeAgreement.agreement_source setup checks wire representation created scalar credential
      (eraseOwner owner) oneTime authenticated coherent env before)
  simp only [bind_map_left] at combined
  change _ = _ >>= continueSource
  rw [← combined]
  simp only [phase, StateT.run_bind, StateT.run_lift, bind_pure_comp, simulateQ_bind,
    map_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨result, afterEnv⟩, afterPrivate⟩ supported
  have raw : (result, afterEnv) ∈ support
      ((RegistrationBeaconReferenceCompiler.agreement (n := n) setup (eraseOwner owner) oneTime authenticated).run env) := by
    apply OracleComp.support_simulateQ_run'_subset
      (implementation setup checks wire representation created scalar credential)
      ((RegistrationBeaconReferenceCompiler.agreement (n := n) setup (eraseOwner owner) oneTime authenticated).run env) before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have kept := RegistrationBeaconReferenceAgreementScope.agreement_keeps setup (eraseOwner owner) oneTime authenticated
    env afterEnv result raw
  have emptyAfter : afterEnv.recordRequests = [] := kept.trans empty
  have erasedAfter : RegistrationBeaconReferenceNativeRecord.erase afterEnv = afterEnv := by
    cases afterEnv
    simp_all only [RegistrationBeaconReferenceNativeRecord.erase]
  have actual := RegistrationBeaconReferenceNativeContinuation.continuation_source setup checks wire representation created scalar credential
    owner current afterEnv authenticated result erased afterPrivate
  simpa only [erasedAfter, continueSource] using actual

/-- Prior native record requests remain in the actual source run but do not affect the entire finishing phase after the explicit analysis projection. -/
theorem phase_full_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner current : Owner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (env : EnvState RegistrationServerRoleBackend.State) (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (erased : Std.Array U8 227#usize) (before : State n KemSK mlSource) :
    RegistrationBeaconReferenceNativeCompletion.drop <$>
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (((phase setup (eraseOwner owner) oneTime authenticated).run (eraseOwner current)).run
          (RegistrationBeaconReferenceNativeRecord.erase env))).run before = (do
      let reached ← (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar
        (eraseOwner owner) oneTime) (RegistrationAgreementExecutor.beacon authenticated)).run (env, before.2.2)
      Prod.map RegistrationBeaconReferenceNativeContinuation.view id <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
          (((RegistrationBeaconReferenceNativeContinuation.sourceAfter setup wire owner reached.1 :
            RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
              (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2) := by
  rw [phase_source setup checks wire representation created scalar credential owner current oneTime
    (RegistrationBeaconReferenceNativeRecord.erase env) rfl authenticated coherent erased before]
  let continueSource := fun reached : RustM agreement.AgreementEffect ×
      RegistrationBeaconReferenceNativeStage.Local n KemSK mlSource =>
    Prod.map RegistrationBeaconReferenceNativeContinuation.view id <$>
      (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource)
        (((RegistrationBeaconReferenceNativeContinuation.sourceAfter setup wire owner reached.1 :
          RegistrationBeaconReferenceNativeOwner.M n KemSK RegistrationServerRoleBackend.State mlSource
            (RustM (Option Pqxdh.Bytes))).run current).run reached.2.1)).run reached.2.2
  have normalized := congrArg (fun script => script >>= continueSource)
    (RegistrationBeaconReferenceNativeLedger.native_program setup checks representation created scalar
      (eraseOwner owner) oneTime (RegistrationAgreementExecutor.beacon authenticated) env before.2.2)
  simp only [bind_map_left] at normalized
  change _ >>= continueSource = _ >>= continueSource
  rw [← normalized]
  apply bind_congr
  rintro ⟨result, afterEnv, afterNative⟩
  have same := congrArg (fun script =>
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) script).run afterNative)
    (RegistrationBeaconReferenceNativeAfterInput.source_after_input setup wire owner current result afterEnv)
  simpa only [continueSource, simulateQ_map, StateT.run_map, Prod.map_def, id_eq] using same.symm

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase.phase_source
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase.phase_full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePhase.phase_full_source
