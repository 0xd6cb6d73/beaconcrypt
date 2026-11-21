-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyController

/-! Complete adaptive full-ledger transport. The actual old secrecy interpreter runs the compiled native adversary, and exact transcript restoration gives the actual native interpreter with its original hidden bit, fresh draws and all raw replies. The theorem has no source/game-equality premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyLedger
open PqxdhDeploymentSecrecy (Ledger)
variable {Value Reader Response : Type}

noncomputable def oldLayer (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) : QueryImpl RegistrationNativeInterface.FullSpec
      (StateT Ledger (OracleComp PqxdhDeploymentInterface.Spec)) :=
  PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds ∘ₛ RegistrationNativeEntropyCompile.modeO

noncomputable def nativeLayer (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) : QueryImpl RegistrationNativeInterface.FullSpec
      (StateT RegistrationNativeLedger.State (OracleComp PqxdhDeploymentInterface.Spec)) :=
  RegistrationNativeEntropyCore.compiler.mapStateTBase
    (RegistrationNativeLedger.handler crypto codec serverKid bounds)

/-- Every full native query commutes with the actual original ledger interpreter. -/
theorem query (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : Ledger) :
    Prod.map id RegistrationNativeEntropyRestore.ledger <$>
        (oldLayer crypto codec serverKid bounds query).run before =
      (nativeLayer crypto codec serverKid bounds query).run
        (RegistrationNativeEntropyRestore.ledger before) := by
  cases query with
  | inl core => exact RegistrationNativeEntropyLayer.ledger_core crypto codec serverKid bounds core before
  | inr secrecy =>
      unfold oldLayer nativeLayer
      rw [QueryImpl.compose, RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query]
      exact RegistrationNativeEntropyController.controller crypto codec serverKid bounds secrecy before

/-- Original test/fresh controllers and native metadata transport commute through every adaptive full-interface continuation. -/
theorem program (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value) (before : Ledger) :
    Prod.map id RegistrationNativeEntropyRestore.ledger <$>
        (simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)
          (simulateQ RegistrationNativeEntropyCompile.modeO work)).run before =
      simulateQ RegistrationNativeEntropyCore.compiler
        ((simulateQ (RegistrationNativeLedger.handler crypto codec serverKid bounds) work).run
          (RegistrationNativeEntropyRestore.ledger before)) := by
  rw [← QueryImpl.simulateQ_compose, QueryImpl.simulateQ_mapStateTBase_run]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ RegistrationNativeEntropyRestore.ledger
    (query crypto codec serverKid bounds) work before

/-- Starting from the actual empty ledger gives exactly the complete native wrapped client, without resampling any private state. -/
theorem wrap (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value) :
    Prod.map id RegistrationNativeEntropyRestore.ledger <$>
        PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds
          (RegistrationNativeEntropyCompile.compile .O work) =
      simulateQ RegistrationNativeEntropyCore.compiler
        (RegistrationNativeLedger.wrap crypto codec serverKid bounds work) :=
  program crypto codec serverKid bounds work Ledger.empty

end BeaconcryptCore.Computational.RegistrationNativeEntropyLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyLedger.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyLedger.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyLedger.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyLedger.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyLedger.wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyLedger.wrap
