-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryReport

/-! The ordinary report monitor instruments the same actual lazy indexed source. Dropping only its public history and report observations recovers the complete opaque-identity source execution, with every private generated seed and original source transcript retained. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource
open PqxdhJointPhase1Reports (ProtocolSpec Monitor)
open PqxdhDynamicIdentityReports (ReportingState)
variable {Value : Type}

private theorem state_bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_pure_apply {m : Type → Type} [Monad m] {S A : Type}
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

abbrev State (count : Nat) := Monitor count × ReportingState count

def privatePool {count : Nat} (before : State count) : PqxdhDynamicIdentityPool.SourceState := before.2.source.2

/-- Adding the ordinary field-origin monitor changes no actual indexed response or private source state. -/
theorem query_source (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ProtocolSpec.Domain) (before : State count) :
    Prod.map id privatePool <$>
      (PqxdhJointPhase1Reports.sourceImpl joint count query).run before =
      (RegistrationNativeIdentityMainSource.implementation joint query).run (privatePool before) := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run]
  cases query with
  | inl request =>
      simp only [PqxdhJointPhase1Reports.wrapper, StateT.run, state_bind_apply, state_pure_apply, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, PqxdhDynamicIdentityReports.reportingImpl, map_bind, map_pure,
        Prod.map_def, id_eq, privatePool, RegistrationNativeIdentityMainSource.implementation]
      have operated := PqxdhDynamicIdentityRouting.sourceWithHistory_run count
        (PqxdhDynamicIdentityPool.lazyImpl joint) request before.2.source.1 before.2.source.2
      change PqxdhDynamicIdentityRouting.sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl joint) request before.2.source = _ at operated
      rw [operated]
      simp only [bind_pure_comp, Functor.map_map]
      change id <$> (PqxdhDynamicIdentityPool.lazyImpl joint request).run before.2.source.2 = _
      exact id_map' _
  | inr report =>
      cases translated : PqxdhJointPhase1Reports.translateReport joint report before.1.snapshot with
      | none =>
          simp only [PqxdhJointPhase1Reports.wrapper, StateT.run, translated, simulateQ_pure,
            StateT.monad_pure_def, StateT.pure, map_pure, Prod.map_def, id_eq, privatePool,
            RegistrationNativeIdentityMainSource.implementation]
          rfl

      | some forgery =>
          simp only [PqxdhJointPhase1Reports.wrapper, StateT.run, state_bind_apply, state_pure_apply, translated, simulateQ_bind,
            simulateQ_spec_query, simulateQ_pure, PqxdhDynamicIdentityReports.reportingImpl,
            StateT.monad_pure_def, StateT.pure, pure_bind, map_pure, Prod.map_def, id_eq,
            privatePool, RegistrationNativeIdentityMainSource.implementation]
          rfl


/-- Whole adaptive monitor instrumentation retains every actual public reply, private generated seed and source transcript. -/
theorem program_source (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (before : State count) :
    Prod.map id privatePool <$>
      (simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count) work).run before =
      (simulateQ (RegistrationNativeIdentityMainSource.implementation joint) work).run (privatePool before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_source joint count query before, bind_map_left]
      apply bind_congr
      intro result
      exact ih result.1 result.2

/-- Literal initialized ordinary report execution projects to the native ghost-report source on the same complete client AST. -/
theorem run_source (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) :
    Prod.map id privatePool <$> PqxdhJointPhase1Reports.run joint count work =
      (simulateQ (RegistrationNativeIdentityMainSource.implementation joint) work).run PqxdhDynamicIdentityPool.initialState :=
  program_source joint count work _

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportSource.run_source
