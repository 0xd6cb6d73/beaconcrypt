-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginObserved
import BeaconcryptCore.Computational.RegistrationNativeIdentityOriginEvents

/-! The initialized whole native observer reaches an actual retained execution before its retrospective reports. Source startup contributes only ordinary uniform observations. The final batch therefore detects every changed accepted prekey against every final alias. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityReportMonitor renaming State → MonitorState
open RegistrationNativeIdentityReportSource (privatePool)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

theorem coins_pool (joint : PqxdhJointIdentity.Primitives) (count : Nat) (work : ProbComp Value)
    (before : MonitorState count) (result : Value × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      (simulateQ RegistrationNativeIdentityMain.coins work)).run before)) :
    RegistrationNativeIdentityCompiler.poolView (privatePool result.2) =
      RegistrationNativeIdentityCompiler.poolView (privatePool before) := by
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) supported
  rw [← support_map, RegistrationNativeIdentityReportSource.program_source] at projected
  have viewed := Set.mem_image_of_mem (Prod.map id RegistrationNativeIdentityCompiler.poolView) projected
  rw [← support_map, RegistrationNativeIdentityMainSource.coins_source, support_map] at viewed
  obtain ⟨value, _reached, same⟩ := viewed
  exact (congrArg Prod.snd same).symm

theorem emit_pool (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (reports : List PqxdhJointPhase1Reports.CandidateReport) (before : MonitorState count)
    (result : Unit × MonitorState count)
    (supported : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count)
      (RegistrationNativeIdentityMain.emit reports)).run before)) : privatePool result.2 = privatePool before := by
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) supported
  rw [← support_map, RegistrationNativeIdentityReportSource.program_source,
    RegistrationNativeIdentityMainSource.emit_source] at projected
  have same : (result.1, privatePool result.2) = ((), privatePool before) := eq_of_mem_support_pure projected
  exact congrArg (fun pair : Unit × PqxdhDynamicIdentityPool.SourceState => pair.2) same

theorem client_receipt (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (count : Nat) (observed : RegistrationNativeEvents.Observed Value (State n KemSK source)) (after : MonitorState count)
    (supported : (some observed, after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary))) :
    ∃ initial starting reached,
      (some initial, starting) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        (simulateQ RegistrationNativeIdentityMain.coins (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId))).run
          (RegistrationNativeIdentityReportMonitor.initial count)) ∧
      (observed, reached) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        (RegistrationNativeIdentityMain.run setup checks wire route representation initial.created initial.credential bounds mode
          (adversary initial.public) (RegistrationNativeIdentityMainProfile.fromInitial initial))).run starting) ∧
      ((), after) ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl setup.joint count)
        (RegistrationNativeIdentityMain.emit (RegistrationNativeIdentityFinalReports.reports wire observed.2.1.transcript observed.2.2.beacons))).run reached) := by
  unfold RegistrationNativeIdentityOriginObserved.client PqxdhJointPhase1Reports.run at supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨initialized, starting, continued⟩ := supported
  cases selected : initialized.1 with
  | none =>
      simp only [selected, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        Option.some_ne_none, false_and] at continued
  | some initial =>
      simp only [selected, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨finished, reached, emitted⟩ := continued
      obtain ⟨reported, called, returned⟩ := emitted
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at returned
      obtain ⟨rfl, rfl⟩ := returned
      refine ⟨initial, initialized.2, finished.2, ?_, reached, ?_⟩
      · rw [← selected]
        exact starting
      · have unit : reported.1 = () := Subsingleton.elim _ _
        simpa only [← unit, Prod.mk.eta] using called

/-- Every changed accepted prekey in the actual final source roster is recognized in the complete ordinary joint experiment. -/
theorem client_detects (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (count : Nat) (room : budget.create ≤ count) (observed : RegistrationNativeEvents.Observed Value (State n KemSK source)) (after : MonitorState count)
    (supported : (some observed, after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary)))
    (changed : RegistrationNativeIdentityOriginFinal.Changed setup.joint wire observed.2.1.transcript observed.2.2.beacons) :
    after.1.occurred = true := by
  obtain ⟨initial, starting, reached, started, ran, reported⟩ := client_receipt setup checks wire route representation source ensureInit identityIndex
    serverKeyId bounds mode adversary count observed after supported
  have consistent := RegistrationNativeIdentityReportMonitor.program_consistent setup.joint count _ _ _
    (RegistrationNativeIdentityReportMonitor.initial_consistent setup.joint count) started
  have empty := coins_pool setup.joint count _ _ _ started
  have reveals := RegistrationNativeIdentityReportFresh.program_reveals setup.joint count _
    (RegistrationNativeIdentityMainNoRevealCore.coins_safe _) _ _ started
  exact RegistrationNativeIdentityOriginFinal.run_detects setup checks wire route representation initial.created initial.credential bounds mode
    (adversary initial.public) budget (bounded initial.public) _ count room starting consistent empty reveals
    (observed, reached) ran changed ((), after) reported

theorem client_owned (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (count : Nat) (observed : RegistrationNativeEvents.Observed Value (State n KemSK source)) (after : MonitorState count)
    (supported : (some observed, after) ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityOriginObserved.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary))) :
    RegistrationNativeIdentityRealization.Owned setup.joint (privatePool after) observed.2.2.beacons := by
  obtain ⟨initial, starting, reached, started, ran, reported⟩ := client_receipt setup checks wire route representation source ensureInit identityIndex
    serverKeyId bounds mode adversary count observed after supported
  have empty := coins_pool setup.joint count _ _ _ started
  have projected := Set.mem_image_of_mem (Prod.map id privatePool) ran
  rw [← support_map, RegistrationNativeIdentityReportSource.program_source] at projected
  have prior : RegistrationNativeIdentityMainHistory.Inv setup.joint (RegistrationNativeIdentityMainProfile.fromInitial initial, privatePool starting) := by
    apply (RegistrationNativeIdentityMainHistory.projection_inv setup.joint _).mp
    change RegistrationNativeIdentityMainHistory.Inv setup.joint
      (RegistrationNativeIdentityMainProfile.fromInitial initial, RegistrationNativeIdentityCompiler.poolView (privatePool starting))
    rw [empty]
    exact RegistrationNativeIdentityMainHistoryRun.initial_inv setup.joint _
  have held := RegistrationNativeIdentityMainHistoryRun.run_inv setup checks wire route representation initial.created initial.credential
    bounds mode (adversary initial.public) (RegistrationNativeIdentityMainProfile.fromInitial initial, privatePool starting)
    (observed, privatePool reached) prior projected
  rw [emit_pool setup.joint count _ reached ((), after) reported]
  exact held.1.1

end BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.coins_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.coins_pool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.emit_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.emit_pool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.client_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.client_receipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.client_detects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.client_detects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.client_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityOriginRun.client_owned
