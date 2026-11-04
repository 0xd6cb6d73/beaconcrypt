-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability
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

open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
local notation "cfgClient" => RegistrationNativePlatformIdentityOriginObserved.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

def projection {count : Nat}
    (result : Option (RegistrationNativePlatformIdentityOriginObserved.Observed n KemSK Platform Value source) × MonitorState count) :=
  RegistrationNativePlatformIdentityOriginObserved.sourceProject (result.1,privatePool result.2)

/-- The ordinary reporting game restores the same complete retained native/platform outcome. -/
theorem reported_source (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform) (count : Nat) :
    projection <$> PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous) =
    RegistrationNativePlatformIdentityOriginObserved.native (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous := by
  have same := congrArg (fun distribution => RegistrationNativePlatformIdentityOriginObserved.sourceProject <$> distribution)
    (RegistrationNativeIdentityReportSource.run_source setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))
  rw [RegistrationNativePlatformIdentityOriginObserved.client_source] at same
  unfold projection
  simpa only [Functor.map_map,Prod.map_def,id_eq] using same

/-- Changing the final value observer leaves the exact ordinary source monitor event unchanged. -/
theorem monitor_same (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform) (count : Nat) :
    Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false) previous))}[result.2.1.occurred = true] =
    Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))}[result.2.1.occurred = true] := by
  rw [RegistrationNativePlatformIdentityOriginObserved.client_map,PqxdhJointPhase1Reports.run,simulateQ_map,StateT.run_map,prEvent_map]
  rfl

/-- Original native events keep their complete actual platform poststate under the retained initialized game. -/
theorem native_profile (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    (fun result : Option (RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) × Platform) => match result with
      | none => (false,previous)
      | some observed => (event observed.1,observed.2)) <$>
      RegistrationNativePlatformIdentityOriginObserved.native (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous =
    (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode adversary event).run previous := by
  unfold RegistrationNativePlatformIdentityOriginObserved.native RegistrationNativePlatformOrdinaryExperiment.profile
  simp only [map_bind,StateT.run_bind,StateT.run_lift,bind_assoc,pure_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial => simp only [Functor.map_map,StateT.run_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability.reported_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability.reported_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability.monitor_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability.monitor_same

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability.native_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability.native_profile
