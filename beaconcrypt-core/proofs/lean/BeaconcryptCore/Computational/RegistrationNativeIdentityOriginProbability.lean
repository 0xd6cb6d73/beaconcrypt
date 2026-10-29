-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginBound

/-! The whole original native changed-prekey event reduces to the same generated-position ordinary joint Ed25519/converted-static-DH family. Actual startup, broad future-born aliases, all source failures and the original complete native CE ledger are retained. Retrospective reports are source ghosts and add no generated-key, field or target factor. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Budget Mode)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def projection {source : RegistrationNativeMldsa.Source} {count : Nat}
    (result : Option (RegistrationNativeEvents.Observed Value (RegistrationNativeIdentityMain.State n KemSK source)) × MonitorState count) :=
  RegistrationNativeIdentityOriginObserved.sourceProject (result.1, privatePool result.2)

theorem reported_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (count : Nat) :
    projection <$> PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary) =
      RegistrationNativeIdentityOriginObserved.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary := by
  have same := congrArg (fun distribution => RegistrationNativeIdentityOriginObserved.sourceProject <$> distribution)
    (RegistrationNativeIdentityReportSource.run_source setup.joint count
      (RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary))
  rw [RegistrationNativeIdentityOriginObserved.client_source] at same
  unfold projection
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same

theorem monitor_same (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (count : Nat) :
    Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false)))}[
        result.2.1.occurred = true] =
      Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint count
        (RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary))}[
          result.2.1.occurred = true] := by
  rw [RegistrationNativeIdentityOriginObserved.client_map, PqxdhJointPhase1Reports.run,
    simulateQ_map, StateT.run_map, prEvent_map]
  rfl

theorem native_profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    (fun result => result.any (RegistrationNativeIdentityOriginEvents.event setup.joint wire)) <$>
      RegistrationNativeIdentityOriginObserved.native (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary =
      RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
        (RegistrationNativeIdentityOriginEvents.event setup.joint wire) := by
  unfold RegistrationNativeIdentityOriginObserved.native RegistrationNativeExperiment.profile
  rw [map_bind]
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial => simp only [Functor.map_map, Option.any_some]

/-- Every accepted changed-prekey packet against any final generated native owner is covered by ordinary joint weak-EUF, without an accept, field or alias-position factor. -/
theorem changed_prekey_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
      (RegistrationNativeIdentityOriginEvents.event setup.joint wire))}[result = true] ≤
      ∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityOriginBound.reduction (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
          (fun _ => false) count fallback ordinaryFallback target) := by
  classical
  let work := RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
  calc
    _ = Pr{let result ← PqxdhJointPhase1Reports.run setup.joint (count + 1) work}[
      (projection result).any (RegistrationNativeIdentityOriginEvents.event setup.joint wire) = true] := by
      rw [← native_profile, ← reported_source (count := count + 1), prEvent_map, prEvent_map]
    _ ≤ Pr{let result ← PqxdhJointPhase1Reports.run setup.joint (count + 1) work}[result.2.1.occurred = true] := by
      apply prEvent_mono_of_support
      rintro ⟨observed, monitor⟩ reached bad
      cases observed with
      | none => exact False.elim (Bool.false_ne_true bad)
      | some observed =>
          have owned := RegistrationNativeIdentityOriginRun.client_owned setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
            (count + 1) observed monitor reached
          have nativeChanged : RegistrationNativeIdentityOriginEvents.Changed setup.joint wire observed.2.1.transcript
              (RegistrationNativeIdentityRealization.owners (privatePool monitor) observed.2.2.beacons) := by
            exact of_decide_eq_true bad
          have changed := (RegistrationNativeIdentityOriginEvents.realized setup.joint wire observed.2.1.transcript
            (privatePool monitor) observed.2.2.beacons owned).mp nativeChanged
          exact RegistrationNativeIdentityOriginRun.client_detects setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
            budget bounded (count + 1) room observed monitor reached changed
    _ = Pr{let result ← (PqxdhJointPhase1Reports.run setup.joint (count + 1)
      (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false)))}[
        result.2.1.occurred = true] := (monitor_same setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary (count + 1)).symm
    _ ≤ _ := RegistrationNativeIdentityOriginBound.field_origin_bound setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary
      (fun _ => false) budget bounded count room fallback ordinaryFallback

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.reported_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.reported_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.monitor_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.monitor_same
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.native_profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.native_profile
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.changed_prekey_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginProbability.changed_prekey_bound
