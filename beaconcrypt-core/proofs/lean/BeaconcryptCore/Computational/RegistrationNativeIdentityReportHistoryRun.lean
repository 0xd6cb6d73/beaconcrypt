-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainFull
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor
import BeaconcryptCore.Computational.RegistrationNativeEdHistoryRun

/-! Ordinary joint report instrumentation retains the actual native fixed-prekey policy and exact per-handle signing history. Both properties are derived on initialized native CE prefixes through the complete source projection; they are not supplied by an authentication event or an untrusted history callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem run_inv (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (context : Context n KemSK) (count : Nat)
    (result : RegistrationNativeEvents.Observed Value (State n KemSK source) × MonitorState count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩))) :
    RegistrationNativeIdentityMainHistory.Inv setup.joint (result.1.2.2, privatePool result.2) := by
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) supported
  rw [← support_map, RegistrationNativeIdentityReportSource.run_source] at projected
  exact RegistrationNativeIdentityMainHistoryRun.initialized_run_inv setup checks wire route representation created credential
    bounds mode work context (result.1, privatePool result.2) projected

/-- Actual native source execution derives the immutable-prekey signing policy in the ordinary joint report experiment. -/
theorem run_fixed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (context : Context n KemSK) (count : Nat)
    (result : RegistrationNativeEvents.Observed Value (State n KemSK source) × MonitorState count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩))) :
    ∀ owner ∈ result.1.2.2.beacons,
      RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory := by
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) supported
  rw [← support_map, RegistrationNativeIdentityReportSource.run_source] at projected
  have native := Set.mem_image_of_mem RegistrationNativeIdentityMainFull.observedProject projected
  rw [← support_map, RegistrationNativeIdentityMainFull.full_source setup checks wire route representation created credential
    bounds mode work (⟨context, []⟩, PqxdhDynamicIdentityPool.initialState)
    (RegistrationNativeIdentitySourceCreateOwned.empty_owned setup.joint _)] at native
  have fixed := RegistrationNativeEdHistoryRun.run_fixed setup checks wire route representation created source credential bounds mode work
    (RegistrationNativeIdentityMainSource.project (⟨context, []⟩, PqxdhDynamicIdentityPool.initialState))
    (RegistrationNativeIdentityMainFull.observedProject (result.1, privatePool result.2))
    (RegistrationNativeEdHistorySource.fixed_empty source) native
  intro owner member
  exact fixed (RegistrationNativeIdentityRealization.owner (privatePool result.2) owner)
    (List.mem_map.mpr ⟨owner, member, rfl⟩)

/-- The actual ordinary monitor has the source owner's complete chronological signed-message ledger at its generated handle. -/
theorem run_signed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (context : Context n KemSK) (count : Nat)
    (result : RegistrationNativeEvents.Observed Value (State n KemSK source) × MonitorState count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩)))
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ result.1.2.2.beacons)
    (valid : owner.identity.handle < count) :
    PqxdhJointIdentity.signedMessages (result.2.1.snapshot.history.histories ⟨owner.identity.handle, valid⟩) =
      PqxdhJointIdentity.signedMessages owner.edHistory := by
  have invariant := run_inv setup checks wire route representation created credential bounds mode work context count result supported
  rw [RegistrationNativeIdentityReportMonitor.run_snapshot setup.joint count _ result supported]
  exact RegistrationNativeIdentityHistoryObservation.replay_signed ⟨owner.identity.handle, valid⟩
    (privatePool result.2) result.1.2.2.beacons invariant.1.2.2 owner member rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun.run_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun.run_inv

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun.run_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun.run_fixed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun.run_signed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun.run_signed
