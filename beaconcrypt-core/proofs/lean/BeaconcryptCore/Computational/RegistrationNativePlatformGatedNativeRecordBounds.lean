-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds
import BeaconcryptCore.Computational.RegistrationNativeLedgerRecordBounds

/-! The actual gated native record client has the original joint send/raw limits. Public pin metadata and stateful allocation consume no record capability; every optional reply, failed allocation and reached poststate remains in the same original computation. Startup resources are separate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds
open RegistrationNativeEntropyInterface (Environment)
open RegistrationNativeLedgerRecordBounds (IsRecord)
open PqxdhRecordLiftBudget (RecordKind WorldRecord NativeRecord recordBudget)
open PqxdhDeploymentInterface (Mode FreshBounds Budget)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {E Failure V Reader Response : Type}

private theorem compiler (kind : RecordKind) (request : RegistrationNativeInterface.Spec.Domain) :
    (RegistrationNativeEntropyCore.compiler request).IsQueryBoundP (NativeRecord kind)
      (if IsRecord kind request then 1 else 0) := by
  cases request with
  | inl coin => cases kind <;>
      simp [RegistrationNativeEntropyCore.compiler, IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
        PqxdhDeploymentCompileBudget.commandKind, isQueryBoundP_query_iff]
  | inr request => cases request <;> cases kind <;>
      simp [RegistrationNativeEntropyCore.compiler, IsRecord, NativeRecord, RegistrationNativeInterface.eraseCore,
        PqxdhDeploymentCompileBudget.commandKind, RegistrationNativeInterface.eraseCommand, isQueryBoundP_query_iff,
        isQueryBoundP_query_bind_iff]

/-- Every actual native request emits at most its original one selected send/raw capability; metadata and allocation add none. -/
theorem query (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (kind : RecordKind) (request : RegistrationNativeInterface.Spec.Domain) (before : E) :
    ((RegistrationNativePlatformGatedNativeEntropy.native env reserve request).run before).IsQueryBoundP (WorldRecord kind)
      (if IsRecord kind request then 1 else 0) := by
  rw [← RegistrationNativePlatformGatedNativeEntropy.query_drop env reserve request ([], before)]
  apply (isQueryBoundP_map_iff _ _ _).mpr
  exact RegistrationNativePlatformGatedRecordBounds.native_bound (RegistrationNativeEntropyPort.environment env)
    (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) kind
    (RegistrationNativeEntropyCore.compiler request) _ (compiler kind request) ([], before)

/-- The complete original full ledger wrapper retains the original all-mode joint record allowance through the literal stateful gate. -/
theorem wrapped (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : E) (kind : RecordKind) :
    ((simulateQ (RegistrationNativePlatformGatedNativeEntropy.native env reserve)
      (RegistrationNativeLedger.wrap crypto codec serverKeyId bounds (RegistrationNativeInterface.asModeO mode work))).run before).IsQueryBoundP
      (WorldRecord kind) (recordBudget budget kind) := by
  exact (RegistrationNativeLedgerRecordBounds.wrap_bound crypto codec serverKeyId bounds mode budget work bounded kind).simulateQ_run_of_step
    (fun request selected state => by simpa only [ite_eq_left selected] using query env reserve kind request state)
    (fun request other state => by simpa only [ite_eq_right other] using query env reserve kind request state) before

/-- The actual native stage, including its public startup description, has the same original record caps before any separate startup prefix. -/
theorem program (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKeyId : U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V) (bounded : RegistrationNativeInterface.Respects budget work)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : E) (kind : RecordKind) :
    (RegistrationNativePlatformGatedNativeEntropy.program env reserve crypto codec serverKeyId bounds mode work created before).IsQueryBoundP
      (WorldRecord kind) (recordBudget budget kind) := by
  unfold RegistrationNativePlatformGatedNativeEntropy.program
  rw [isQueryBoundP_map_iff]
  exact wrapped env reserve crypto codec serverKeyId bounds mode budget work bounded before kind

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds.wrapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds.wrapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBounds.program
