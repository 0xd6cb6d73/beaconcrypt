-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog
open RegistrationNativeRawRegistrationJournal (Mark typedMark rawMarks logging)
open RegistrationNativeRawAdapter (TypedSpec)
variable {S A Reader Response : Type}

def marks (wire : RegistrationNativeWire.Wire) (entry : RegistrationNativeInterface.Entry) : List Mark :=
  match entry with
  | ⟨.inl query, reply⟩ => rawMarks wire query reply
  | ⟨.inr _, _⟩ => []
def transcript (wire : RegistrationNativeWire.Wire) (entries : List RegistrationNativeInterface.Entry) : List Mark :=
  entries.flatMap (marks wire)

private theorem quiet_query (wire : RegistrationNativeWire.Wire)
    (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (query : RegistrationNativeInterface.Spec.Domain)
    (allowed : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) ≠ false)
    (before : S × List Mark) (result : RegistrationNativeInterface.Spec.Range query × (S × List Mark))
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler wire (logging implementation) query).run before)) :
    result.2.2 = before.2 := by
  have recorded := RegistrationNativeRawRegistrationJournal.raw_step wire implementation query before result supported
  have quiet : rawMarks wire query result.1 = [] := by
    cases query with
    | inl coin => rfl
    | inr command => cases command <;>
        simp only [RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand,
          PqxdhDeploymentSecrecy.coinOrSend] at allowed <;> first | contradiction | rfl
  simpa only [quiet, List.append_nil] using recorded

/-- Original test/fresh callbacks cannot emit a registration marker, although their actual coins, sends and complete source poststate remain executed. -/
theorem quiet_program (wire : RegistrationNativeWire.Wire)
    (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (work : OracleComp RegistrationNativeInterface.Spec A)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0)
    (before : S × List Mark) (result : A × (S × List Mark))
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire (logging implementation)) work).run before)) :
    result.2.2 = before.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    obtain ⟨allowed, following⟩ := bounded
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨returned, called, continued⟩ := supported
    exact (ih returned.1 (by simpa using following returned.1) returned.2 continued).trans
      (quiet_query wire implementation query (allowed.resolve_right (by omega)) before returned called)

/-- One full native API callback relates the original ledger's public registration projection to the exact typed source log. -/
theorem full_step (wire : RegistrationNativeWire.Wire)
    (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × (S × List Mark))
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × (S × List Mark)))
    (supported : result ∈ support ((RegistrationNativeLedger.interpreted
      (RegistrationNativeRawAdapter.handler wire (logging implementation)) crypto codec serverKeyId bounds query).run before)) :
    result.2.2.2 = before.2.2 ++ marks wire ⟨query, result.1⟩ := by
  rw [RegistrationNativeLedger.interpreted, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨returned, reached, rfl⟩ := supported
  cases query with
  | inl core =>
    rw [RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at reached
    obtain ⟨inner, called, rfl⟩ := reached
    exact RegistrationNativeRawRegistrationJournal.raw_step wire implementation core before.2 inner called
  | inr secrecy =>
    simpa only [marks, List.append_nil] using quiet_program wire implementation
      ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds (.inr secrecy)).run before.1)
      (RegistrationNativeLedger.secrecy_frame crypto codec serverKeyId bounds secrecy before.1) before.2 returned reached

/-- The actual current native ledger and typed registration log agree at every original full-API prefix. -/
def Consistent (wire : RegistrationNativeWire.Wire)
    (before : RegistrationNativeLedger.State × (S × List Mark)) : Prop :=
  transcript wire before.1.transcript = before.2.2

/-- Complete source state and original private test/fresh ledger are retained while the public registration projection remains exact. -/
theorem full_consistent (wire : RegistrationNativeWire.Wire)
    (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × (S × List Mark)) (prior : Consistent wire before)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × (S × List Mark)))
    (supported : result ∈ support ((RegistrationNativeLedger.interpreted
      (RegistrationNativeRawAdapter.handler wire (logging implementation)) crypto codec serverKeyId bounds query).run before)) :
    Consistent wire result.2 := by
  have recorded := RegistrationNativeLedgerJournal.handler_records
    (RegistrationNativeRawAdapter.handler wire (logging implementation)) crypto codec serverKeyId bounds query before result supported
  have logged := full_step wire implementation crypto codec serverKeyId bounds query before result supported
  change transcript wire result.2.1.transcript = result.2.2.2
  rw [recorded, transcript, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact (congrArg (· ++ marks wire ⟨query, result.1⟩) prior).trans logged.symm

/-- Starting from the original empty native ledger yields an exact decoded registration chronology after the entire adaptive run, including all later callbacks. -/
theorem initialized (wire : RegistrationNativeWire.Wire)
    (implementation : QueryImpl TypedSpec (StateT S ProbComp))
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (work : OracleComp RegistrationNativeInterface.FullSpec A)
    (before : S) (result : A × (RegistrationNativeLedger.State × (S × List Mark)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeLedger.interpreted
      (RegistrationNativeRawAdapter.handler wire (logging implementation)) crypto codec serverKeyId bounds) work).run
        (RegistrationNativeLedger.empty, (before, [])))) :
    Consistent wire result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle _ (Consistent wire)
    (fun query current prior returned reached => full_consistent wire implementation crypto codec serverKeyId bounds
      query current prior returned reached) work (RegistrationNativeLedger.empty, (before, [])) rfl result supported
end BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.quiet_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.quiet_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.full_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.full_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.full_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationLedgerLog.initialized
