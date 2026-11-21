-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRawRegistrationJournal
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalProjection
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeRawRegistrationJournal (Mark typedMark logging)
open RegistrationNativeStageTrace (Call)
variable {S A Reader Response : Type}
def project (before : S × List (Call TypedSpec S)) : S × List Mark :=
  (before.1, before.2.filterMap fun call => typedMark call.query call.reply)

/-- Forgetting only private callback pre/poststates gives precisely the decoded public registration log, with the complete current source state unchanged. -/
theorem typed (implementation : QueryImpl TypedSpec (StateT S ProbComp)) (work : OracleComp TypedSpec A)
    (before : S × List (Call TypedSpec S)) :
    Prod.map id project <$> (simulateQ (RegistrationNativeStageTrace.handler implementation) work).run before =
      (simulateQ (logging implementation) work).run (project before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  simp only [RegistrationNativeStageTrace.handler, logging, StateT.run, Functor.map_map]
  congr 1
  funext result
  simp only [Prod.map, id_eq, project, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  rfl
end BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalProjection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalProjection.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationJournalProjection.typed
