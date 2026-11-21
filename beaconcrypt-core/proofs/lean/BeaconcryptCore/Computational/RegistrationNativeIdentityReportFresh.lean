-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoReveal
import BeaconcryptCore.Computational.RegistrationNativeIdentityReportMonitor

/-! The concrete ordinary report monitor derives target freshness from the actual native client's structural absence of identity-reveal queries. No unrevealed-identity premise is supplied at the native profile endpoint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh
open PqxdhJointPhase1Reports (ProtocolSpec Monitor)
open RegistrationNativeIdentityMainNoRevealCore (Allowed DynamicAllowed)
variable {Value : Type}

private theorem observe_reveals (count : Nat) (query : PqxdhDynamicIdentityPool.DynamicSpec.Domain)
    (answer : PqxdhDynamicIdentityPool.DynamicSpec.Range query)
    (before : PqxdhDynamicIdentityReports.PublicSnapshot count) (allowed : DynamicAllowed query) :
    (PqxdhDynamicIdentityReports.observe query answer before).history.reveals = before.history.reveals := by
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | create => rfl
    | reveal handle => exact False.elim allowed
    | service handle request =>
        simp only [PqxdhDynamicIdentityReports.observe, PqxdhDynamicIdentityRouting.historyUpdate]
        split <;> cases answer <;> simp [PqxdhJointIdentityEvents.publicUpdate]

/-- A permitted protocol callback cannot append an identity reveal for any possible ordinary oracle reply. -/
theorem wrapper_reveals (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ProtocolSpec.Domain)
    (before : Monitor count) (result : ProtocolSpec.Range query × Monitor count) (allowed : Allowed query)
    (reached : result ∈ support ((PqxdhJointPhase1Reports.wrapper joint count query).run before)) :
    result.2.snapshot.history.reveals = before.snapshot.history.reveals := by
  cases query with
  | inl query =>
      simp only [PqxdhJointPhase1Reports.wrapper, StateT.run, bind_pure_comp, support_map] at reached
      obtain ⟨answer, _observed, returned⟩ := reached
      cases returned
      exact observe_reveals count query answer before.snapshot allowed
  | inr report =>
      simp only [PqxdhJointPhase1Reports.wrapper, StateT.run] at reached
      cases translated : PqxdhJointPhase1Reports.translateReport joint report before.snapshot with
      | none =>
          simp only [translated, support_pure, Set.mem_singleton_iff] at reached
          cases reached
          rfl
      | some forgery =>
          simp only [translated, bind_pure_comp, support_map] at reached
          obtain ⟨reply, _observed, returned⟩ := reached
          cases returned
          rfl

/-- The actual ordinary source interpretation retains that same complete public reveal history. -/
theorem query_reveals (joint : PqxdhJointIdentity.Primitives) (count : Nat) (query : ProtocolSpec.Domain)
    (before : RegistrationNativeIdentityReportMonitor.State count)
    (result : ProtocolSpec.Range query × RegistrationNativeIdentityReportMonitor.State count)
    (allowed : Allowed query)
    (reached : result ∈ support ((PqxdhJointPhase1Reports.sourceImpl joint count query).run before)) :
    result.2.1.snapshot.history.reveals = before.1.snapshot.history.reveals := by
  rw [PqxdhJointPhase1Reports.sourceImpl, QueryImpl.Stateful.link_impl_apply_run] at reached
  obtain ⟨inner, supported, returned⟩ := OracleComp.mem_support_map_peel _ _ reached
  cases returned
  apply wrapper_reveals joint count query before.1 inner.1 allowed
  apply OracleComp.support_simulateQ_run'_subset (PqxdhDynamicIdentityReports.reportingImpl joint count) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

/-- Every adaptive allowed prefix retains the original reveal history under the actual ordinary report source. -/
theorem program_reveals (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (allowed : AllQueriesSatisfy work Allowed)
    (before : RegistrationNativeIdentityReportMonitor.State count)
    (result : Value × RegistrationNativeIdentityReportMonitor.State count)
    (reached : result ∈ support ((simulateQ (PqxdhJointPhase1Reports.sourceImpl joint count) work).run before)) :
    result.2.1.snapshot.history.reveals = before.1.snapshot.history.reveals := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      cases reached
      rfl
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, observed, continued⟩ := reached
      exact (ih middle.1 (later middle.1) middle.2 result continued).trans
        (query_reveals joint count query before middle first observed)

/-- Every generated identity remains fresh in the actual initialized ordinary report experiment for an allowed client. -/
theorem run_fresh (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (work : OracleComp ProtocolSpec Value) (allowed : AllQueriesSatisfy work Allowed)
    (result : Value × RegistrationNativeIdentityReportMonitor.State count)
    (reached : result ∈ support (PqxdhJointPhase1Reports.run joint count work)) (identity : Fin count) :
    PqxdhJointIdentityFreshness.Fresh identity result.2.1.snapshot.history := by
  have empty := program_reveals joint count work allowed (RegistrationNativeIdentityReportMonitor.initial count) result reached
  change result.2.1.snapshot.history.reveals = [] at empty
  simp only [PqxdhJointIdentityFreshness.Fresh, empty, List.not_mem_nil, not_false_eq_true]

/-- Every target in the actual generated-startup ordinary native client has derived report-time freshness. -/
theorem client_fresh {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool) (count : Nat)
    (result : Bool × RegistrationNativeIdentityReportMonitor.State count)
    (reached : result ∈ support (PqxdhJointPhase1Reports.run setup.joint count
      (RegistrationNativeIdentityMainProfile.client (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event)))
    (identity : Fin count) : PqxdhJointIdentityFreshness.Fresh identity result.2.1.snapshot.history :=
  run_fresh setup.joint count _
    (RegistrationNativeIdentityMainNoReveal.client_safe setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode adversary event)
    result reached identity

end BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.wrapper_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.wrapper_reveals
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.query_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.query_reveals
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.program_reveals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.program_reveals
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.run_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.run_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.client_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityReportFresh.client_fresh
