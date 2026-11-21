-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSnapshotCoverage
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativeInterface (FullSpec Entry)
open PqxdhDeploymentSessionSnapshots (Journal)
variable {Index Reader Response S A : Type}

/-- Every native full-ledger branch records its original input and actual reply, including failed fresh/test calls and ML-pin-aware creation. -/
theorem ledger_records (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (result : FullSpec.Range query × RegistrationNativeLedger.State)
    (supported : result ∈ support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds query).run before)) :
    result.2.transcript = before.transcript ++ [⟨query, result.1⟩] := by
  cases query with
  | inl forwarded =>
    rw [RegistrationNativeLedger.query_forward, support_map] at supported
    obtain ⟨reply, _possible, rfl⟩ := supported
    rfl
  | inr secrecy =>
    rw [RegistrationNativeLedger.query_secrecy, support_map] at supported
    obtain ⟨returned, _possible, rfl⟩ := supported
    rfl

/-- The exact native ledger recording law survives any actual stateful raw handler, retaining its complete private and platform poststate. -/
theorem handler_records (implementation : QueryImpl RegistrationNativeInterface.Spec (StateT S ProbComp))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : FullSpec.Domain)
    (before : RegistrationNativeLedger.State × S) (result : FullSpec.Range query × (RegistrationNativeLedger.State × S))
    (supported : result ∈ support ((RegistrationNativeLedger.interpreted implementation crypto codec serverKeyId bounds query).run before)) :
    result.2.1.transcript = before.1.transcript ++ [⟨query, result.1⟩] := by
  rw [RegistrationNativeLedger.interpreted, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨returned, reached, rfl⟩ := supported
  apply ledger_records crypto codec serverKeyId bounds query before.1 returned.1
  apply OracleComp.support_simulateQ_run'_subset implementation _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst reached

def entries (journal : Journal FullSpec) : List Entry := journal.map fun entry => ⟨entry.1, entry.2⟩
abbrev SnapshotState (Index S : Type) := PqxdhDeploymentSessionSnapshots.State Index FullSpec (RegistrationNativeLedger.State × S)
def Consistent (state : SnapshotState Index S) : Prop :=
  state.native.1.transcript = entries state.journal ∧
    ∀ index snapshot, state.captured index = some snapshot → snapshot.2.1.transcript = entries snapshot.1

/-- Every write-once receipt retains the exact original native transcript at its own callback prefix. -/
theorem advance_consistent (stop : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stop index)]
    (state : SnapshotState Index S) (query : FullSpec.Domain) (reply : FullSpec.Range query)
    (native : RegistrationNativeLedger.State × S) (consistent : Consistent state)
    (recorded : native.1.transcript = state.native.1.transcript ++ [⟨query, reply⟩]) :
    Consistent (PqxdhDeploymentSessionSnapshots.advance stop state query reply native) := by
  have current : native.1.transcript = entries (state.journal ++ [⟨query, reply⟩]) := by
    simpa [entries] using recorded.trans (congrArg (fun transcript => transcript ++ [⟨query, reply⟩]) consistent.1)
  refine ⟨current, ?_⟩
  intro index snapshot saved
  cases previous : state.captured index with
  | none =>
    simp [PqxdhDeploymentSessionSnapshots.advance, previous] at saved
    rcases saved with ⟨_, rfl⟩
    exact current
  | some receipt =>
    have same : receipt = snapshot := by simpa [PqxdhDeploymentSessionSnapshots.advance, previous] using saved
    exact same ▸ consistent.2 index receipt previous

/-- The same native ledger and every captured prefix remain linked through the entire original adaptive suffix. -/
theorem program_consistent (implementation : QueryImpl RegistrationNativeInterface.Spec (StateT S ProbComp))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (stop : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stop index)]
    (work : OracleComp FullSpec A) (before : SnapshotState Index S) (consistent : Consistent before)
    (result : A × SnapshotState Index S)
    (supported : result ∈ support ((simulateQ (PqxdhDeploymentSessionSnapshots.handler
      (RegistrationNativeLedger.interpreted implementation crypto codec serverKeyId bounds) stop) work).run before)) :
    Consistent result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact consistent
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      PqxdhDeploymentSessionSnapshots.handler_run, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨returned, reached, continued⟩ := supported
    exact ih returned.1 _ (advance_consistent stop before query returned.1 returned.2 consistent
      (handler_records implementation crypto codec serverKeyId bounds query before.native returned reached)) continued

/-- Literal empty initialization gives the exact journal/ledger identity for one fully continued native run. -/
theorem run_consistent (implementation : QueryImpl RegistrationNativeInterface.Spec (StateT S ProbComp))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (stop : Index → Journal FullSpec → Prop) [∀ index, DecidablePred (stop index)]
    (work : OracleComp FullSpec A) (before : S) (result : A × SnapshotState Index S)
    (supported : result ∈ support (PqxdhDeploymentSessionSnapshots.run
      (RegistrationNativeLedger.interpreted implementation crypto codec serverKeyId bounds) stop work (RegistrationNativeLedger.empty, before))) :
    Consistent result.2 :=
  program_consistent implementation crypto codec serverKeyId bounds stop work
    (⟨[], fun _ => none, (RegistrationNativeLedger.empty, before)⟩ : SnapshotState Index S)
    ⟨rfl, fun _ _ impossible => nomatch impossible⟩ result supported
end BeaconcryptCore.Computational.RegistrationNativeLedgerJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.ledger_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.ledger_records
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.handler_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.handler_records
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.advance_consistent' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.advance_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.program_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.run_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerJournal.run_consistent
