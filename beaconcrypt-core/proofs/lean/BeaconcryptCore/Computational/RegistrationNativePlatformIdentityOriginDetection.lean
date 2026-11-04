-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginPrepare
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFixedMain
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection
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

/-- The reached fixed-prekey source policy turns any changed accepted tuple into the same ordinary monitor event. -/
private theorem detects_of_fixed (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous)))
    (fixed : ∀ owner ∈ observed.2.1.beacons,RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory)
    (changed : RegistrationNativeIdentityOriginFinal.Changed setup.joint (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      observed.1.2.transcript observed.2.1.beacons) : after.1.occurred = true := by
  obtain ⟨reached,reported,consistent,holds,unrevealed⟩ := RegistrationNativePlatformIdentityOriginPrepare.client_prepared setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  exact RegistrationNativeIdentityOriginFinal.recognizes setup.joint (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    observed.1.2.transcript observed.2.1.beacons count reached consistent holds fixed
    (fun owner member => RegistrationNativePlatformIdentityOriginRun.client_fits setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded count room observed after supported owner member)
    unrevealed changed ((),after) reported

/-- The actual initialized dynamic source derives every final owner's fixed-prekey signing policy internally. -/
theorem client_fixed (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (count : Nat) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous))) :
    ∀ owner ∈ observed.2.1.beacons,RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory := by
  obtain ⟨initial,starting,reached,_started,ran,_reported⟩ := RegistrationNativePlatformIdentityOriginRun.client_receipt setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) ran
  rw [←support_map,RegistrationNativeIdentityReportSource.program_source] at projected
  apply RegistrationNativePlatformIdentityFixedMain.run_fixed setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    bounds mode (adversary initial.public) (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous,privatePool starting)
    (observed.1,(observed.2,privatePool reached))
  · intro owner impossible
    cases impossible
  · change (observed.1,(observed.2,privatePool reached)) ∈ support
      ((fun evaluated => (evaluated.1.1,(evaluated.1.2,evaluated.2))) <$>
        (simulateQ (RegistrationNativeIdentityMainSource.implementation setup.joint)
          ((RegistrationNativePlatformIdentityMainFull.run setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
            bounds mode (adversary initial.public)).run (RegistrationNativePlatformIdentityMainProfile.fromInitial initial previous))).run (privatePool starting))
    rw [support_map]
    exact Set.mem_image_of_mem _ projected

/-- Every changed accepted prekey against any final generated source owner is recognized by the same actual ordinary joint monitor. -/
theorem client_detects (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count) (observed : Observed n KemSK Platform Value source) (after : MonitorState count)
    (supported : (some observed,after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous)))
    (changed : RegistrationNativeIdentityOriginFinal.Changed setup.joint (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      observed.1.2.transcript observed.2.1.beacons) : after.1.occurred = true :=
  detects_of_fixed setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded count room observed after supported
    (client_fixed setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous count observed after supported) changed

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection.client_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection.client_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection.client_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection.client_detects
