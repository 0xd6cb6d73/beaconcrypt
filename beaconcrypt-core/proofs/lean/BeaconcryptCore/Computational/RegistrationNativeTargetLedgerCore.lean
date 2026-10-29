-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap

/-! Original public full-ledger callbacks expose the same raw typed source and literal ledger append under any concrete native state kernel. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
variable {NativeState : Type}

/-- The original full public call is the actual raw typed callback followed by its own literal ledger entry. -/
theorem run (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (query : RegistrationNativeInterface.Spec.Domain) (before : RegistrationNativeLedger.State × NativeState) :
    (RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds typed (.inl query)).run before =
      (fun result => (result.1, (RegistrationNativeLedger.record before.1 ⟨.inl query, result.1⟩, result.2))) <$>
        (RegistrationNativeRawAdapter.handler wire typed query).run before.2 := by
  rcases before with ⟨ledger, sourceBefore⟩
  simp only [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, RegistrationNativeLedger.query_forward,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl
end BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore.run
