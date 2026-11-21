-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityProfileCreateCaps
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportHistoryRun

/-! The actual source private roster obeys the structural native creation cap. Every retained public owner therefore fits the same finite generated-identity family at every bounded initialized native prefix. Neither public-key injectivity nor a final winning-budget assertion is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointPhase1Reports (ProtocolSpec SourceClass)
open PqxdhDynamicIdentityPool (IsCreate)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

theorem query_growth (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ProtocolSpec.Domain)
    (before : MonitorState count) (result : ProtocolSpec.Range query × MonitorState count)
    (supported : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count query).run before)) :
    (privatePool result.2).seeds.length ≤ (privatePool before).seeds.length + if SourceClass IsCreate query then 1 else 0 := by
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) supported
  rw [← support_map, RegistrationNativeIdentityReportSource.query_source] at projected
  cases query with
  | inl request =>
      obtain ⟨appended, extended, length⟩ := PqxdhDynamicIdentityPool.lazyImpl_seed_extension joint request
        (privatePool before) (result.1, privatePool result.2) projected
      rw [extended, List.length_append, length]
      exact Nat.le_refl _
  | inr report =>
      change (result.1, privatePool result.2) ∈ support (pure ((), privatePool before)) at projected
      have same := congrArg Prod.snd (eq_of_mem_support_pure projected)
      change privatePool result.2 = privatePool before at same
      rw [same]
      exact Nat.le_refl _

/-- Any bounded complete source client, with arbitrary adaptive replies and stopping, has at most its original number of generated identities. -/
theorem program_growth (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (cap : Nat) (bounded : work.IsQueryBoundP (SourceClass IsCreate) cap)
    (before : MonitorState count) (result : Value × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count) work).run before)) :
    (privatePool result.2).seeds.length ≤ (privatePool before).seeds.length + cap := by
  apply bounded.cost_le_of_mem_support_run_simulateQ (fun current : MonitorState count => (privatePool current).seeds.length)
    (fun query selected state next reached => by simpa only [selected, ite_true] using query_growth joint count query state next reached)
    (fun query selected state next reached => by simpa only [selected, ite_false, Nat.add_zero] using query_growth joint count query state next reached)
    before result supported

/-- Every source-generated owner at a reached bounded actual native prefix fits the finite ordinary multi-user family. -/
theorem run_handle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (context : RegistrationNativeIdentityWorld.Context n KemSK) (count : Nat) (room : budget.create ≤ count)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeIdentityMain.State n KemSK source) × MonitorState count)
    (supported : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩)))
    (owner : RegistrationNativeIdentityFrontend.Owner source) (member : owner ∈ result.1.2.2.beacons) :
    owner.identity.handle < count := by
  have grows := program_growth setup.joint count _ budget.create
    (RegistrationNativeIdentityProfileCreateCaps.run_bound setup checks wire route representation created credential bounds mode work budget bounded _)
    _ result supported
  have invariant := RegistrationNativeIdentityReportHistoryRun.run_inv setup checks wire route representation created credential
    bounds mode work context count result supported
  obtain ⟨seed, stored⟩ := invariant.1.1 owner member
  have valid := (List.getElem?_eq_some_iff.mp stored.1).1
  change owner.identity.handle < (privatePool result.2).seeds.length at valid
  change (privatePool result.2).seeds.length ≤ 0 + budget.create at grows
  omega

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity.query_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity.query_growth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity.program_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity.program_growth
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity.run_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity.run_handle
