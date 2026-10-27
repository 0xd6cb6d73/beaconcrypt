import BeaconcryptCore.Computational.PqxdhServerAuthAcceptedEntry
import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-! Chronological observations of the actual public API. Logging is a transformation of the public client, so existing full-continuation simulations apply to the entire joint execution, not merely to its final marginal state. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthApiJournal
variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Record the exact query and actual reply after each public call returns. Private interpreter state is absent from this interface. The returned list has source chronological order. -/
def record (client : OracleComp spec α) : OracleComp spec (α × QueryLog spec) :=
  (simulateQ loggingOracle client).run

/-- Erasing the journal gives the identical client program, before any oracle interpretation or probability calculation. -/
theorem erase (client : OracleComp spec α) : Prod.fst <$> record client = client :=
  loggingOracle.fst_map_run_simulateQ client

/-- Journaling preserves every predicate-based source query cap, including adaptive requests that are later rejected. -/
theorem query_bound (client : OracleComp spec α) (predicate : ι → Prop) [DecidablePred predicate]
    (cap : Nat) :
    (record client).IsQueryBoundP predicate cap ↔ client.IsQueryBoundP predicate cap := by
  exact isQueryBoundP_iff_of_map_eq (p := predicate) (erase client)

/-- The exact original answer and entire private state are recovered after any stateful interpreter, without assuming anything about its replies. -/
theorem interpreted_erase {κ σ : Type} {target : OracleSpec κ}
    (impl : QueryImpl spec (StateT σ (OracleComp target))) (client : OracleComp spec α) (state : σ) :
    (fun result => (result.1.1, result.2)) <$> (simulateQ impl (record client)).run state =
      (simulateQ impl client).run state := by
  have same := congrArg (fun work => (simulateQ impl work).run state) (erase client)
  simpa only [simulateQ_map, StateT.run_map] using same

/-- Every base, uniform, hash or other predicate-based interpreter bill is unchanged by the observer, as a syntactic all-replies query bound. -/
theorem interpreted_query_bound {κ σ : Type} {target : OracleSpec κ}
    (impl : QueryImpl spec (StateT σ (OracleComp target))) (client : OracleComp spec α) (state : σ)
    (predicate : κ → Prop) [DecidablePred predicate] (cap : Nat) :
    ((simulateQ impl (record client)).run state).IsQueryBoundP predicate cap ↔
      ((simulateQ impl client).run state).IsQueryBoundP predicate cap :=
  isQueryBoundP_iff_of_map_eq (p := predicate) (interpreted_erase impl client state)

end BeaconcryptCore.Computational.PqxdhServerAuthApiJournal

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.interpreted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.interpreted_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.interpreted_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthApiJournal.interpreted_query_bound
