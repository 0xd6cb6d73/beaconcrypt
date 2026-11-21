-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginProbability
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginDetection
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginBound
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The actual initialized dynamic-writer changed-prekey event reduces to the finite ordinary joint-Ed family. Genuine startup, future-born final aliases, complete native/platform outcomes and all signing/writer failures remain in the same execution. The fixed source policy and generated-history facts are derived internally. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound
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
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
local notation "cfgClient" => RegistrationNativePlatformIdentityOriginObserved.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

open RegistrationNativePlatformIdentityOriginProbability (projection)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

/-- Every original accepted changed-prekey tuple against any final generated owner reduces to the ordinary joint family, on the actual initialized dynamic-writer run. -/
theorem changed_prekey_bound (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← ((RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode adversary (RegistrationNativeIdentityOriginEvents.event setup.joint canonical)).run previous)}[result.1 = true] ≤
    ∑ target : Fin (count+1),PqxdhJointIdentity.advantage setup.joint
      (RegistrationNativePlatformIdentityOriginBound.reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false) previous count fallback ordinaryFallback target) := by
  classical
  let work := cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous
  calc
    _ = Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint (count+1) work)}[
      (projection result).any (fun observed => RegistrationNativeIdentityOriginEvents.event setup.joint canonical observed.1) = true] := by
      rw [←RegistrationNativePlatformIdentityOriginProbability.native_profile (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous (RegistrationNativeIdentityOriginEvents.event setup.joint canonical),prEvent_map,
        ←RegistrationNativePlatformIdentityOriginProbability.reported_source (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous (count+1),prEvent_map]
      apply prEvent_congr
      intro result
      cases projection result <;> rfl
    _ ≤ Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint (count+1) work)}[result.2.1.occurred = true] := by
      apply prEvent_mono_of_support
      rintro ⟨observed,monitor⟩ reached bad
      cases observed with
      | none => exact False.elim (Bool.false_ne_true bad)
      | some observed =>
        have owned := RegistrationNativePlatformIdentityOriginRun.client_inv setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous (count+1) observed monitor reached
        have nativeChanged : RegistrationNativeIdentityOriginEvents.Changed setup.joint canonical observed.1.2.transcript
            (RegistrationNativeIdentityRealization.owners (privatePool monitor) observed.2.1.beacons) := by
          exact of_decide_eq_true bad
        have changed := (RegistrationNativeIdentityOriginEvents.realized setup.joint canonical observed.1.2.transcript
          (privatePool monitor) observed.2.1.beacons owned.1.1).mp nativeChanged
        exact RegistrationNativePlatformIdentityOriginDetection.client_detects setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded (count+1) room observed monitor reached changed
    _ = Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint (count+1)
      (RegistrationNativePlatformIdentityMainProfile.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false) previous))}[result.2.1.occurred = true] :=
      (RegistrationNativePlatformIdentityOriginProbability.monitor_same setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous (count+1)).symm
    _ ≤ _ := RegistrationNativePlatformIdentityOriginBound.field_origin_bound setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false) previous budget bounded count room fallback ordinaryFallback

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound.changed_prekey_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityChangedBound.changed_prekey_bound
