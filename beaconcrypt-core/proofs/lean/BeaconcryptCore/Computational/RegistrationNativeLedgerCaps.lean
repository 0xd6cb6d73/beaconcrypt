-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLedger
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! The ML-pin-aware native wrapper retains the original CE secrecy bills. The literal original hidden-bit and byte draws add exactly the existing test and fresh allowances; each native public command retains its original command class. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeLedgerCaps
open RegistrationNativeInterface (Spec FullSpec ModeSpec asModeO queryClass Respects)
open RegistrationNativeLedger (State legacyLift)
open PqxdhDeploymentInterface (Mode Budget FreshBounds)
open PqxdhDeploymentCompileSecrecy (wrapCost)
variable {Reader Response Value : Type}

def coreKind (query : Spec.Domain) : Fin 12 :=
  PqxdhDeploymentCompileBudget.commandKind (RegistrationNativeInterface.eraseCore query)

/-- Every actual native ordinary command keeps its original native class, including the extra ML pin at create. -/
theorem core_class (query : Spec.Domain) : (queryClass (.inl query)).val = (coreKind query).val :=
  PqxdhDeploymentCompileSecrecy.queryClass_inl (RegistrationNativeInterface.eraseCore query)

set_option backward.isDefEq.respectTransparency false in
/-- The secrecy-only embedding preserves the full original per-command structural bill. -/
theorem legacy_bound (work : OracleComp PqxdhDeploymentInterface.Spec Value) (kind : Fin 12) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => PqxdhDeploymentCompileBudget.commandKind query = kind) cap) :
    (simulateQ legacyLift work).IsQueryBoundP (fun query => coreKind query = kind) cap := by
  apply RawCtxSourceOpen.simulate_bound legacyLift
    (fun query => PqxdhDeploymentCompileBudget.commandKind query = kind) _ _ cap bounded
  intro query
  cases query with
  | inl coin =>
      simp only [legacyLift]
      rw [isQueryBoundP_query_iff]
      intro counted
      simp_all [coreKind, RegistrationNativeInterface.eraseCore, PqxdhDeploymentCompileBudget.commandKind]
  | inr command =>
      cases command <;> simp only [legacyLift] <;> rw [isQueryBoundP_query_iff] <;>
        intro counted <;>
        simp_all [coreKind, RegistrationNativeInterface.eraseCore, RegistrationNativeInterface.eraseCommand,
          PqxdhDeploymentCompileBudget.commandKind]

/-- Each actual native full-interface query incurs precisely the original secrecy-wrapper class allowance. -/
theorem step_bound (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (kind : Fin 12) (query : FullSpec.Domain) (state : State) :
    ((RegistrationNativeLedger.handler crypto codec serverKid bounds query).run state).IsQueryBoundP
      (fun request => coreKind request = kind) (wrapCost bounds kind (queryClass query)) := by
  cases query with
  | inl core =>
      rw [RegistrationNativeLedger.query_forward, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro counted
      have same : (queryClass (.inl core)).val = kind.val := (core_class core).trans (congrArg Fin.val counted)
      simp only [wrapCost, same]
      split_ifs <;> omega
  | inr secrecy =>
      rw [RegistrationNativeLedger.query_secrecy, isQueryBoundP_map_iff]
      exact legacy_bound _ kind _ (PqxdhDeploymentCompileSecrecy.wrap_step crypto codec serverKid bounds kind
        (.inr secrecy) state.ledger)

/-- Arbitrary ML-pin-aware adaptive clients keep the original tight classwise test and fresh-byte bills in either observation mode. -/
theorem wrap_bound (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (budget : Budget) (bounded : Respects budget work) (kind : Fin 12) :
    (RegistrationNativeLedger.wrap crypto codec serverKid bounds (asModeO mode work)).IsQueryBoundP
      (fun query => coreKind query = kind) (∑ full, wrapCost bounds kind full * budget.cap full) :=
  FinitePartitionQueryBounds.weighted_bound queryClass (wrapCost bounds kind) budget.cap
    (RegistrationNativeLedger.handler crypto codec serverKid bounds) (fun query => coreKind query = kind)
    (asModeO mode work) (RegistrationNativeInterface.asModeO_bound budget work bounded)
    (fun query state => step_bound crypto codec serverKid bounds kind query state) RegistrationNativeLedger.empty

end BeaconcryptCore.Computational.RegistrationNativeLedgerCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.core_class' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.core_class
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.legacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.legacy_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.step_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.wrap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLedgerCaps.wrap_bound
