-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginRun
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The complete current dynamic-writer native profile is interpreted by one executable ordinary joint-Ed client. Startup constructs the independent Server/ML/KEM auxiliary state internally; the challenged Beacon Ed seed is supplied only by its generated indexed service. Every constructor/API failure and full shared P poststate is retained. This is source correspondence, not yet a publication-security reduction or restricted-root confidentiality client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginPrepare
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainOwned (Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformIdentityOriginObserved (Observed)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
local notation "cfgClient" => RegistrationNativePlatformIdentityOriginObserved.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- The literal current initialized source run supplies its own synchronized, unrevealed reporting snapshot. -/
theorem client_prepared (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (count : Nat) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))) :
    ∃ reached,
      ((),after) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) observed.1.2.transcript observed.2.1.beacons))).run reached) ∧
      RegistrationNativeIdentityReportMonitor.Consistent setup.joint reached ∧
      RegistrationNativeIdentityHistoryInvariant.Holds setup.joint (privatePool reached) observed.2.1.beacons ∧
      reached.1.snapshot.history.reveals = [] := by
  obtain ⟨initial,starting,reached,started,ran,reported⟩ := RegistrationNativePlatformIdentityOriginRun.client_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  have initialConsistent := RegistrationNativeIdentityReportMonitor.program_consistent setup.joint count _ _ _
    (RegistrationNativeIdentityReportMonitor.initial_consistent setup.joint count) started
  have consistent := RegistrationNativeIdentityReportMonitor.program_consistent setup.joint count _ _ _ initialConsistent ran
  have invariant := RegistrationNativePlatformIdentityOriginRun.client_inv setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  rw [RegistrationNativeIdentityOriginRun.emit_pool setup.joint count _ reached ((),after) reported] at invariant
  have finalUnrevealed := RegistrationNativePlatformIdentityOriginRun.client_unrevealed setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  have reportReveals := RegistrationNativeIdentityReportFresh.program_reveals setup.joint count _
    (RegistrationNativeIdentityMainNoRevealCore.emit_safe _) reached ((),after) reported
  exact ⟨reached,reported,consistent,invariant.1,reportReveals.symm.trans finalUnrevealed⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginPrepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginPrepare.client_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginPrepare.client_prepared
