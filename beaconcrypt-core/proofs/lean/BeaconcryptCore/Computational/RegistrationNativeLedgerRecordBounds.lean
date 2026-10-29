-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLedgerCaps
import BeaconcryptCore.Computational.PqxdhRecordLiftBudget

/-! Joint native send/raw accounting retains the original secrecy-wrapper bills. A test or fresh command makes one handle-selected send, so neither role direction is charged twice. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds
open PqxdhRecordLiftBudget (RecordKind NativeRecord recordCost recordBudget)
open PqxdhDeploymentInterface (Mode Budget FreshBounds)
open RegistrationNativeInterface (FullSpec ModeSpec asModeO queryClass Respects eraseCore)
variable {Reader Response Value : Type}

def IsRecord (kind : RecordKind) (query : RegistrationNativeInterface.Spec.Domain) : Prop :=
  NativeRecord kind (eraseCore query)

instance (kind : RecordKind) : DecidablePred (IsRecord kind) := fun _ => inferInstanceAs (Decidable (NativeRecord _ _))

theorem legacy_bound (kind : RecordKind) (work : OracleComp PqxdhDeploymentInterface.Spec Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (NativeRecord kind) cap) :
    (simulateQ RegistrationNativeLedger.legacyLift work).IsQueryBoundP (IsRecord kind) cap := by
  apply RawCtxSourceOpen.simulate_bound RegistrationNativeLedger.legacyLift (NativeRecord kind) (IsRecord kind) work cap bounded
  intro query
  cases query with
  | inl coin =>
      cases kind <;> simp [RegistrationNativeLedger.legacyLift, IsRecord, NativeRecord, eraseCore,
        PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
  | inr command =>
      cases command <;> cases kind <;> simp [RegistrationNativeLedger.legacyLift, IsRecord, NativeRecord, eraseCore,
        RegistrationNativeInterface.eraseCommand, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]

theorem step_bound (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Std.U64) (bounds : FreshBounds) (kind : RecordKind) (query : FullSpec.Domain)
    (before : RegistrationNativeLedger.State) :
    ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds query).run before).IsQueryBoundP
      (IsRecord kind) (recordCost kind (queryClass query)) := by
  cases query with
  | inl core =>
      rw [RegistrationNativeLedger.query_forward, isQueryBoundP_map_iff]
      rcases core with coin | command
      · cases kind <;> simp [IsRecord, NativeRecord, eraseCore, recordCost, queryClass,
          RegistrationNativeInterface.eraseQuery, PqxdhDeploymentInterface.queryClass,
          PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
      · cases command <;> cases kind <;> simp [IsRecord, NativeRecord, eraseCore, recordCost, queryClass,
          RegistrationNativeInterface.eraseQuery, RegistrationNativeInterface.eraseCommand,
          PqxdhDeploymentInterface.queryClass, PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
  | inr secrecy =>
      rw [RegistrationNativeLedger.query_secrecy, isQueryBoundP_map_iff]
      exact legacy_bound kind _ _ (PqxdhRecordLiftBudget.wrap_record_step crypto codec serverKeyId bounds kind (.inr secrecy) before.ledger)

/-- The original native full ledger has exactly the original joint send/raw caps in either observation mode. -/
theorem wrap_bound (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (work : OracleComp (ModeSpec mode) Value) (bounded : Respects budget work) (kind : RecordKind) :
    (RegistrationNativeLedger.wrap crypto codec serverKeyId bounds (asModeO mode work)).IsQueryBoundP
      (IsRecord kind) (recordBudget budget kind) := by
  have counted := FinitePartitionQueryBounds.weighted_bound queryClass (recordCost kind) budget.cap
    (RegistrationNativeLedger.handler crypto codec serverKeyId bounds) (IsRecord kind)
    (asModeO mode work) (RegistrationNativeInterface.asModeO_bound budget work bounded)
    (fun query current => step_bound crypto codec serverKeyId bounds kind query current) RegistrationNativeLedger.empty
  cases kind <;> simpa [RegistrationNativeLedger.wrap, recordCost, recordBudget, Budget.cap, Budget.sends, Budget.receives,
    Fin.sum_univ_succ, Nat.add_assoc] using counted

end BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds.legacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds.legacy_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds.step_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds.wrap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds.wrap_bound
