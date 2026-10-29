-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound

/-! The original secrecy ledger above any actual native interpreter. Transcript append and frozen pre-accept guesses are independent of private record behavior, cursor refusal, writer failure and the later selected-root continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyLedger
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds Entry)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentTranscript (acceptCount)
open PqxdhDeploymentIdealParams (Target)
open PqxdhDeploymentIdealGuess (guessCt)
variable {S T Reader Response Value : Type}

noncomputable def full (native : QueryImpl Spec (StateT S ProbComp)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (Ledger × S) ProbComp) :=
  (native.mapStateTBase (ledgerImpl crypto codec serverKid bounds)).flattenStateT

theorem full_run (native : QueryImpl Spec (StateT S ProbComp)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (query : FullSpec.Domain) (ledger : Ledger) (state : S) :
    (full native crypto codec serverKid bounds query).run (ledger, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ native ((ledgerImpl crypto codec serverKid bounds query).run ledger)).run state := rfl

/-- A concrete native program projection commutes with the exact full ledger query and its complete private state. -/
theorem full_project (source : QueryImpl Spec (StateT S ProbComp)) (target : QueryImpl Spec (StateT T ProbComp))
    (project : S → T) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (query : FullSpec.Domain) (ledger : Ledger) (state : S)
    (equation : Prod.map id project <$>
      (simulateQ source ((ledgerImpl crypto codec serverKid bounds query).run ledger)).run state =
      (simulateQ target ((ledgerImpl crypto codec serverKid bounds query).run ledger)).run (project state)) :
    Prod.map id (Prod.map id project) <$> (full source crypto codec serverKid bounds query).run (ledger, state) =
      (full target crypto codec serverKid bounds query).run (ledger, project state) := by
  have mapped := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work) equation
  simpa only [full_run, Functor.map_map, Prod.map, id_eq] using mapped

/-- Every actual full query appends exactly its original query and actual reply, independently of its private implementation. -/
theorem transcript (native : QueryImpl Spec (StateT S ProbComp)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (query : FullSpec.Domain) (ledger : Ledger) (state : S)
    (result : FullSpec.Range query × Ledger × S)
    (reached : result ∈ support ((full native crypto codec serverKid bounds query).run (ledger, state))) :
    result.2.1.transcript = ledger.transcript ++ [⟨query, result.1⟩] := by
  rw [full_run, support_map] at reached
  obtain ⟨inner, actual, rfl⟩ := reached
  rcases query with forwarded | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at actual
    obtain ⟨answer, _, rfl⟩ := actual
    rfl
  · exact PqxdhDeploymentEligibility.ledger_secrecy crypto codec serverKid bounds secrecy ledger inner.1
      (PqxdhRecordLiftFlat.support_run_fst _ _ _ inner actual)

def stop {count : Nat} (codec : Codec Reader Response) (target : Target count) (state : Ledger × S) :
    Option (Option PqxdhKemIndCca.MlKem768Ciphertext) :=
  if target.accept < acceptCount state.1.transcript then some (guessCt codec target state.1.transcript) else none

/-- Once the selected original raw accept has happened, every actual subsequent full query preserves the frozen prefix guess. -/
theorem stop_keeps {count : Nat} (native : QueryImpl Spec (StateT S ProbComp)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds) (target : Target count)
    (query : FullSpec.Domain) (state : Ledger × S) (value : Option PqxdhKemIndCca.MlKem768Ciphertext)
    (stopped : stop codec target state = some value)
    (result : FullSpec.Range query × Ledger × S)
    (reached : result ∈ support ((full native crypto codec serverKid bounds query).run state)) :
    stop codec target result.2 = some value := by
  have appended := transcript native crypto codec serverKid bounds query state.1 state.2 result reached
  unfold stop at stopped ⊢
  split at stopped
  · rename_i later
    have after : target.accept < acceptCount result.2.1.transcript := by
      rw [appended]
      exact lt_of_lt_of_le later (PqxdhDeploymentIdealBeacon.acceptCount_prefix _ _)
    simp only [after, ite_true, Option.some.injEq]
    rw [appended, PqxdhDeploymentIdealGuess.guessCt_append codec target _ _ later]
    exact Option.some.inj stopped
  · cases stopped

/-- At the selected original raw accept, both native implementations freeze the same pre-query guess regardless of their different registration replies. -/
theorem selected_stop {count : Nat} (native : QueryImpl Spec (StateT S ProbComp)) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds) (target : Target count)
    (raw : Pqxdh.Bytes) (state : Ledger × S) (clock : acceptCount state.1.transcript = target.accept)
    (result : FullSpec.Range (.inl (.inr (.accept raw))) × Ledger × S)
    (reached : result ∈ support ((full native crypto codec serverKid bounds (.inl (.inr (.accept raw)))).run state)) :
    stop codec target result.2 = some (guessCt codec target state.1.transcript) := by
  have appended := transcript native crypto codec serverKid bounds (.inl (.inr (.accept raw))) state.1 state.2 result reached
  unfold stop
  rw [appended, PqxdhDeploymentIdealTrace.acceptCount_accept, clock]
  simp only [Nat.lt_succ_self, ite_true, Option.some.injEq]
  unfold guessCt PqxdhDeploymentIdealGuess.earlyFinish
  rw [PqxdhDeploymentIdealAnomalyBound.cutAt_selected target.accept _ clock raw]

end BeaconcryptCore.Computational.CborRawAnomalyLedger

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyLedger.full_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyLedger.full_run
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyLedger.full_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyLedger.full_project
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyLedger.transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyLedger.transcript
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyLedger.stop_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyLedger.stop_keeps
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyLedger.selected_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyLedger.selected_stop
