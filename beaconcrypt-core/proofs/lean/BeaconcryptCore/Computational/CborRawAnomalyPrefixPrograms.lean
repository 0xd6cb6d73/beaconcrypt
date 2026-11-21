-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawAnomalyNoAccept
import BeaconcryptCore.Computational.CborRawPrefixHandoff

/-! The actual source prefix gives both complete native raw and pool executions for every no-accept program. In particular, hidden test/fresh sampling retains all original private draws below the unchanged ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid)
open CborRawPreScan (Source Inv counter native pool)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (initial : Mid KemSK)
include phase1 phase2

/-- Concrete prefix queries without a raw accept preserve their whole source invariant and exact ordinal. -/
theorem query_keeps (query : Spec.Domain) (state : Source KemSK) (valid : Inv setup wire parse initial state)
    (free : commandKind query ≠ 3)
    (result : Spec.Range query × Source KemSK)
    (reached : result ∈ support
      ((CborRawMiddleSimulation.compiled setup wire parse checks target parameters created query).run state)) :
    Inv setup wire parse initial result.2 ∧ counter result.2 = counter state := by
  have held := CborRawPreScan.query_keeps setup wire parse checks target parameters created phase1 phase2 initial query
    state valid (fun raw same => by subst same; exact fun _ => free rfl) result reached
  simpa only [ite_eq_right free, Nat.add_zero] using held

/-- The actual native raw execution of a no-accept prefix is its concrete source projection. -/
theorem middle (work : OracleComp Spec Result)
    (bounded : work.IsQueryBoundP (fun query => commandKind query = 3) 0)
    (state : Source KemSK) (valid : Inv setup wire parse initial state) :
    Prod.map id native <$>
      (simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created) work).run state =
      (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) work).run (native state) ∧
    ∀ result ∈ support ((simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
      work).run state), Inv setup wire parse initial result.2 ∧ counter result.2 = counter state :=
  CborRawAnomalyNoAccept.project_run _ _ native (Inv setup wire parse initial) counter
    (fun query state valid _ => CborRawPreScan.query_native setup wire parse checks target parameters created initial query
      state valid)
    (query_keeps setup wire parse checks target parameters created phase1 phase2 initial) work bounded state valid

/-- The identical no-accept source prefix also projects to the actual pool compiler with its full private pool. -/
theorem pooled (work : OracleComp Spec Result)
    (bounded : work.IsQueryBoundP (fun query => commandKind query = 3) 0)
    (state : Source KemSK) (valid : Inv setup wire parse initial state) :
    Prod.map id pool <$>
      (simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created) work).run state =
      (simulateQ (CborRawPreScan.poolCompiler setup wire parse checks target parameters created) work).run (pool state) ∧
    ∀ result ∈ support ((simulateQ (CborRawMiddleSimulation.compiled setup wire parse checks target parameters created)
      work).run state), Inv setup wire parse initial result.2 ∧ counter result.2 = counter state :=
  CborRawAnomalyNoAccept.project_run _ _ pool (Inv setup wire parse initial) counter
    (fun query state valid free => CborRawPreScan.query_pool setup wire parse checks target parameters created initial query
      state valid (fun raw same => by subst same; exact fun _ => free rfl))
    (query_keeps setup wire parse checks target parameters created phase1 phase2 initial) work bounded state valid

end Prefix
end BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms.query_keeps
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms.middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms.middle
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms.pooled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyPrefixPrograms.pooled
