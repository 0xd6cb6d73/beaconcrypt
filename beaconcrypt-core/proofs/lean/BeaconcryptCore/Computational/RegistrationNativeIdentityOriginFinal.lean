-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportCapacity
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportEmit
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh

/-! Retrospective reports cover changed accepted prekeys against every final generated owner, including owners born after the acceptance. The actual source fixed-prekey policy makes the changed message unissued even at this final snapshot. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Changed (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (transcript : List RegistrationNativeInterface.Entry) (owners : RegistrationNativeIdentityFrontend.State source) : Prop :=
  ∃ packet ∈ RegistrationNativeIdentityFinalReports.packets wire transcript, ∃ owner ∈ owners,
    ∃ decoded : PqxdhEd25519EufCma.Phase1KeyTuple,
      PqxdhEd25519EufCma.acceptPhase1Candidate joint.verify (RegistrationRootInput.candidate packet) =
        some (owner.identity.publicIdentity.ed25519, decoded) ∧
      decoded.prekey ≠ PqxdhPhase2InputBytes.word owner.prekeyPublic

theorem recognizes (joint : PqxdhJointIdentity.Primitives) (wire : RegistrationNativeWire.Wire)
    (transcript : List RegistrationNativeInterface.Entry) (owners : RegistrationNativeIdentityFrontend.State source)
    (count : Nat) (before : MonitorState count)
    (consistent : RegistrationNativeIdentityReportMonitor.Consistent joint before)
    (holds : RegistrationNativeIdentityHistoryInvariant.Holds joint (privatePool before) owners)
    (fixed : ∀ owner ∈ owners, RegistrationNativeEdOrigin.FixedPrekey (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.edHistory)
    (fits : ∀ owner ∈ owners, owner.identity.handle < count) (unrevealed : before.1.snapshot.history.reveals = [])
    (changed : Changed joint wire transcript owners) (result : Unit × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports wire transcript owners))).run before)) :
    result.2.1.occurred = true := by
  obtain ⟨packet, packetPresent, owner, member, decoded, accepted, different⟩ := changed
  have valid := fits owner member
  have snapshot : before.1.snapshot = RegistrationNativeIdentityHistoryReport.snapshot joint count (privatePool before) :=
    consistent.1.1.trans (RegistrationNativeIdentityReportSnapshot.reporting_snapshot joint before.2 consistent.2)
  have fresh : (⟨owner.identity.handle, valid⟩ : Fin count) ∉
      (RegistrationNativeIdentityHistoryReport.snapshot joint count (privatePool before)).history.reveals := by
    rw [← snapshot, unrevealed]
    simp only [List.not_mem_nil, not_false_eq_true]
  have event := (RegistrationNativeIdentityHistoryReport.prekey_or_event joint count (privatePool before) owners
    holds.1 holds.2.2 owner member valid (fixed owner member) fresh (RegistrationRootInput.candidate packet) decoded accepted).resolve_left different
  have recognized : PqxdhJointPhase1Reports.candidateAccepted joint
      ⟨owner.identity.handle, RegistrationRootInput.candidate packet⟩ before.1.snapshot = true := by
    rw [snapshot]
    exact event
  exact RegistrationNativeIdentityReportEmit.emit_detects joint count _ _
    (RegistrationNativeIdentityFinalReports.report_member wire transcript owners packet packetPresent _
      (RegistrationNativeIdentityHistoryReport.reports_accepted joint packet owners owner member decoded accepted))
    before result recognized supported

/-- Complete actual native execution, with arbitrary earlier coins and no earlier indexed service, supplies every final reporting invariant internally. -/
theorem run_detects (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (context : Context n KemSK) (count : Nat)
    (room : budget.create ≤ count) (before : MonitorState count)
    (consistent : RegistrationNativeIdentityReportMonitor.Consistent setup.joint before)
    (empty : RegistrationNativeIdentityCompiler.poolView (privatePool before) = PqxdhDynamicIdentityPool.initialState)
    (unrevealed : before.1.snapshot.history.reveals = [])
    (result : RegistrationNativeEvents.Observed Value (State n KemSK source) × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
      (RegistrationNativeIdentityMain.run setup checks wire route representation created credential bounds mode work ⟨context, []⟩)).run before))
    (changed : Changed setup.joint wire result.1.2.1.transcript result.1.2.2.beacons)
    (reported : Unit × MonitorState count)
    (reportedSupport : reported ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
      (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports wire result.1.2.1.transcript result.1.2.2.beacons))).run result.2)) :
    reported.2.1.occurred = true := by
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) supported
  rw [← support_map, RegistrationNativeIdentityReportSource.program_source] at projected
  have initial : RegistrationNativeIdentityMainHistory.Inv setup.joint ((⟨context, []⟩ : State n KemSK source), privatePool before) := by
    apply (RegistrationNativeIdentityMainHistory.projection_inv setup.joint _).mp
    change RegistrationNativeIdentityMainHistory.Inv setup.joint (⟨context, []⟩, RegistrationNativeIdentityCompiler.poolView (privatePool before))
    rw [empty]
    exact RegistrationNativeIdentityMainHistoryRun.initial_inv setup.joint context
  have invariant := RegistrationNativeIdentityMainHistoryRun.run_inv setup checks wire route representation created credential bounds mode work
    (⟨context, []⟩, privatePool before) (result.1, privatePool result.2) initial projected
  have native := Set.mem_image_of_mem RegistrationNativeIdentityMainFull.observedProject projected
  rw [← support_map, RegistrationNativeIdentityMainFull.full_source setup checks wire route representation created credential bounds mode work
    (⟨context, []⟩, privatePool before) initial.1.1] at native
  have fixed := RegistrationNativeEdHistoryRun.run_fixed setup checks wire route representation created source credential bounds mode work
    (RegistrationNativeIdentityMainSource.project (⟨context, []⟩, privatePool before))
    (RegistrationNativeIdentityMainFull.observedProject (result.1, privatePool result.2))
    (RegistrationNativeEdHistorySource.fixed_empty source) native
  have grows := RegistrationNativeIdentityReportCapacity.program_growth setup.joint count _ budget.create
    (RegistrationNativeIdentityProfileCreateCaps.run_bound setup checks wire route representation created credential bounds mode work budget bounded _)
    before result supported
  have emptySeeds := congrArg PqxdhDynamicIdentityPool.SourceState.seeds empty
  change (privatePool before).seeds = [] at emptySeeds
  have fits : ∀ owner ∈ result.1.2.2.beacons, owner.identity.handle < count := by
    intro owner member
    obtain ⟨seed, stored⟩ := invariant.1.1 owner member
    have valid := (List.getElem?_eq_some_iff.mp stored.1).1
    change owner.identity.handle < (privatePool result.2).seeds.length at valid
    rw [emptySeeds, List.length_nil, Nat.zero_add] at grows
    omega
  have current := RegistrationNativeIdentityReportMonitor.program_consistent setup.joint count _ before result consistent supported
  have noReveal := RegistrationNativeIdentityReportFresh.program_reveals setup.joint count _
    (RegistrationNativeIdentityMainNoReveal.run_safe setup checks wire route representation created credential bounds mode work ⟨context, []⟩)
    before result supported
  apply recognizes setup.joint wire _ _ count result.2 current invariant.1 _ fits (noReveal.trans unrevealed) changed reported reportedSupport
  intro owner member
  exact fixed (RegistrationNativeIdentityRealization.owner (privatePool result.2) owner) (List.mem_map.mpr ⟨owner, member, rfl⟩)

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal.recognizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal.recognizes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal.run_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginFinal.run_detects
