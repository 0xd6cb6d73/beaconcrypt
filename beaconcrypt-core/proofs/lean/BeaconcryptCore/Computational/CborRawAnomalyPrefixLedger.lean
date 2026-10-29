-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyLedger

/-! The full original secrecy ledger commutes with both actual prefix projections until the selected original raw accept. Counter and source invariants are derived on every supported branch, including test/fresh draws and cursor refusals. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentTranscript (acceptCount)
open CborRawPreScan (Source Inv counter native pool)
open CborRawAnomalyLedger (full full_run full_project)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The source classifier identifies exactly the original native accept commands. -/
theorem accept_kind (query : Spec.Domain) : commandKind query = 3 ↔ ∃ raw, query = .inr (.accept raw) := by
  rcases query with coin | command
  · simp [commandKind]
  · cases command <;> simp [commandKind]

/-- The original ledger counts every raw accept attempt and no secrecy-generated send. -/
theorem record_count (ledger : Ledger) (query : FullSpec.Domain) (reply : FullSpec.Range query) :
    acceptCount (ledger.record query reply).transcript = acceptCount ledger.transcript +
      if PqxdhDeploymentInterface.queryClass query = 3 then 1 else 0 := by
  rcases query with (coin | command) | secrecy
  · simp [Ledger.record, acceptCount, List.countP_append, PqxdhDeploymentInterface.queryClass]
  · cases command <;> simp [Ledger.record, acceptCount, List.countP_append, PqxdhDeploymentInterface.queryClass]
  · cases secrecy <;> simp [Ledger.record, acceptCount, List.countP_append, PqxdhDeploymentInterface.queryClass]

section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK) (bounds : FreshBounds)
include phase1 phase2

/-- Native raw and source full-query states have the exact same projected distribution before the selected accept. -/
theorem middle_project (query : FullSpec.Domain) (ledger : Ledger) (state : Source KemSK)
    (valid : Inv setup wire parse initial state) :
    Prod.map id (Prod.map id native) <$>
      (full (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created) setup.source.crypto
        (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, state) =
      (full (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) setup.source.crypto
        (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, native state) := by
  apply full_project
  cases query with
  | inl forwarded =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, StateT.run_map, simulateQ_spec_query]
      have projected := CborRawPreScan.query_native setup wire parse checks target parameters created initial forwarded
        state valid
      have mapped := congrArg (fun work => (fun result => ((result.1, ledger.record (.inl forwarded) result.1), result.2))
        <$> work) projected
      simp only [Functor.map_map, Prod.map, id_eq] at mapped ⊢
      convert mapped using 1 <;> rfl
  | inr secrecy =>
      exact (CborRawAnomalyPrefixPrograms.middle setup wire parse checks target parameters created phase1 phase2 initial
        _ (CborRawAnomalyNoAccept.secrecy_no_accept _ _ _ _ secrecy ledger) state valid).1

/-- The same nonselected full query projects to the concrete source-owned pool compiler. -/
theorem pool_project (query : FullSpec.Domain) (ledger : Ledger) (state : Source KemSK)
    (valid : Inv setup wire parse initial state)
    (other : ∀ raw, query = .inl (.inr (.accept raw)) → counter state ≠ target.accept) :
    Prod.map id (Prod.map id pool) <$>
      (full (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created) setup.source.crypto
        (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, state) =
      (full (CborRawPreScan.poolCompiler setup wire parse checks target parameters created) setup.source.crypto
        (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, pool state) := by
  apply full_project
  cases query with
  | inl forwarded =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, StateT.run_map, simulateQ_spec_query]
      have projected := CborRawPreScan.query_pool setup wire parse checks target parameters created initial forwarded
        state valid (fun raw same => other raw (congrArg Sum.inl same))
      have mapped := congrArg (fun work => (fun result => ((result.1, ledger.record (.inl forwarded) result.1), result.2))
        <$> work) projected
      simp only [Functor.map_map, Prod.map, id_eq] at mapped ⊢
      convert mapped using 1 <;> rfl
  | inr secrecy =>
      exact (CborRawAnomalyPrefixPrograms.pooled setup wire parse checks target parameters created phase1 phase2 initial
        _ (CborRawAnomalyNoAccept.secrecy_no_accept _ _ _ _ secrecy ledger) state valid).1

/-- Every concrete nonselected full query preserves source validity and exact agreement between its native ordinal and original ledger. -/
theorem keeps (query : FullSpec.Domain) (ledger : Ledger) (state : Source KemSK)
    (valid : Inv setup wire parse initial state) (clock : counter state = acceptCount ledger.transcript)
    (before : counter state ≤ target.accept)
    (other : ∀ raw, query = .inl (.inr (.accept raw)) → counter state ≠ target.accept)
    (result : FullSpec.Range query × Ledger × Source KemSK)
    (reached : result ∈ support ((full (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
      setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds query).run (ledger, state))) :
    Inv setup wire parse initial result.2.2 ∧ counter result.2.2 = acceptCount result.2.1.transcript ∧
      counter result.2.2 ≤ target.accept := by
  rw [full_run, support_map] at reached
  obtain ⟨inner, reached, rfl⟩ := reached
  cases query with
  | inl forwarded =>
      rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, StateT.run_map, simulateQ_spec_query,
        support_map] at reached
      obtain ⟨step, supported, rfl⟩ := reached
      have held := CborRawPreScan.query_keeps setup wire parse checks target parameters created phase1 phase2 initial
        forwarded state valid (fun raw same => other raw (congrArg Sum.inl same)) step supported
      refine ⟨held.1, ?_, ?_⟩
      · rw [record_count, held.2, clock]
        rcases forwarded with coin | command
        · rfl
        · cases command <;> rfl
      · by_cases accepts : commandKind forwarded = 3
        · obtain ⟨raw, same⟩ := (accept_kind forwarded).mp accepts
          have different := other raw (congrArg Sum.inl same)
          rw [held.2, ite_eq_left accepts]
          omega
        · rw [held.2, ite_eq_right accepts, Nat.add_zero]
          exact before
  | inr secrecy =>
      have held := (CborRawAnomalyPrefixPrograms.middle setup wire parse checks target parameters created phase1 phase2
        initial _ (CborRawAnomalyNoAccept.secrecy_no_accept _ _ _ _ secrecy ledger) state valid).2 inner reached
      have appended := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto
        (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds secrecy ledger inner.1
        (PqxdhRecordLiftFlat.support_run_fst _ _ _ inner reached)
      refine ⟨held.1, ?_, held.2.trans_le before⟩
      rw [held.2, clock, appended]
      cases secrecy <;> simp [acceptCount, List.countP_append]

end Prefix
end BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.accept_kind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.accept_kind
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.record_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.record_count
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.middle_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.middle_project
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.pool_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.pool_project
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixLedger.keeps
