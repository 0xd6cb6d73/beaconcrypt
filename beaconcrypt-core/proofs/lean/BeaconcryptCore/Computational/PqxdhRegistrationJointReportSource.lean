-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointReportCompiler

/-! Forget only the auxiliary public report monitors from the existing Phase-1 report game. The entire ordinary private identity state and transcript remain exactly those of the original actual initialized registration execution. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhJointPhase1Reports PqxdhDynamicIdentityReports
open PqxdhRegistrationJointReportLift (erase)
variable {Result : Type}

set_option backward.isDefEq.respectTransparency false in
/-- One actual report-game query preserves the complete original private identity state when only the public monitors are omitted from the analysis projection. -/
theorem query_projection (joint : Primitives) (count : Nat) (query : ProtocolSpec.Domain)
    (state : Monitor count × ReportingState count) :
    (fun result => (result.1, result.2.2.source.2)) <$>
      (sourceImpl joint count query).run state =
        (simulateQ (lazyImpl joint) (erase query)).run state.2.source.2 := by
  rw [sourceImpl, QueryImpl.Stateful.link_impl_apply_run]
  simp only [Functor.map_map]
  change (fun result : (ProtocolSpec.Range query × Monitor count) × ReportingState count =>
    (result.1.1, result.2.source.2)) <$>
      (simulateQ (reportingImpl joint count) (wrapper joint count query state.1)).run state.2 = _
  cases query with
  | inl request =>
      simp only [wrapper, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, map_bind, map_pure, erase]
      simp only [reportingImpl, StateT.run, bind_assoc, pure_bind]
      change ((PqxdhDynamicIdentityRouting.sourceWithHistory count (lazyImpl joint) request).run state.2.source >>=
        fun result => pure (result.1, result.2.2)) = _
      rw [PqxdhDynamicIdentityRouting.sourceWithHistory_run]
      simp only [bind_assoc, pure_bind]
      change ((lazyImpl joint request).run state.2.source.2 >>= pure) = _
      rw [bind_pure]
      rfl
  | inr report =>
      simp only [wrapper]
      split <;> simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, map_bind, map_pure, erase]
      rfl

/-- Complete adaptive report-game execution projects to the original ordinary private execution. The entire generated seed pool and ordinary transcript are preserved. -/
theorem program_projection (joint : Primitives) (count : Nat) (program : OracleComp ProtocolSpec Result)
    (state : Monitor count × ReportingState count) :
    (fun result => (result.1, result.2.2.source.2)) <$>
      (simulateQ (sourceImpl joint count) program).run state =
        (simulateQ (lazyImpl joint) (simulateQ erase program)).run state.2.source.2 := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (lazyImpl joint) (simulateQ erase (next result.1))).run result.2)
        (query_projection joint count query state)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete report experiment executes the actual initialized source scheduler. Its analysis projection retains full private pools, owner/native/runtime state and all original outcomes; the only extra coordinates are public report monitors. -/
theorem initialized_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A) :
    (fun result => PqxdhRegistrationJointIdentityCompiler.initializedResult (result.1, result.2.2.source.2)) <$>
      run setup.joint count (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime) =
        (fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
          (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied program).run
            ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) := by
  have projection := program_projection setup.joint count
    (PqxdhRegistrationJointReportCompiler.initialized setup codec checks ensureInit supplied count program runtime)
    (initialMonitor count, ⟨initialSource count, initialSnapshot count, false, []⟩)
  have complete := congrArg (fun work => PqxdhRegistrationJointIdentityCompiler.initializedResult <$> work) projection
  rw [PqxdhRegistrationJointReportCompiler.initialized_erase] at complete
  have actual := PqxdhRegistrationJointIdentityCompiler.initialized_source setup codec checks ensureInit supplied program runtime
  simpa only [PqxdhJointPhase1Reports.run, Functor.map_map] using complete.trans actual

end BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource.query_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource.query_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource.program_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource.program_projection

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointReportSource.initialized_source
