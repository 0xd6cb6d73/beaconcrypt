-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTargetStateMap
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler

/-! Concrete pointwise typed source projections lift through the actual raw adapter and original secrecy ledger without changing any original command or reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap
variable {First Second : Type}
variable (project : First → Second)
  (first : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT First ProbComp))
  (second : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT Second ProbComp))
  (step : ∀ query before, Prod.map id project <$> (first query).run before = (second query).run (project before))

include step

/-- Actual raw decoding retains the pointwise source projection through every optional parser continuation. -/
theorem raw (wire : RegistrationNativeWire.Wire) (query : RegistrationNativeInterface.Spec.Domain) (before : First) :
    Prod.map id project <$> ((RegistrationNativeRawAdapter.handler wire first query).run before) =
      ((RegistrationNativeRawAdapter.handler wire second query).run (project before)) := by
  simpa only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose] using
    RegistrationNativeTargetStateMap.program project first second step (RegistrationNativeRawAdapter.adapter wire query) before

/-- The literal original secrecy compiler and complete ledger preserve the same concrete typed state projection. -/
theorem full (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × First) :
    Prod.map id (Prod.map id project) <$>
      ((RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds first query).run before) =
      ((RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds second query).run (before.1, project before.2)) := by
  rcases before with ⟨ledger, native⟩
  have original := RegistrationNativeTargetStateMap.program project
    (RegistrationNativeRawAdapter.handler wire first) (RegistrationNativeRawAdapter.handler wire second)
    (raw project first second step wire) ((RegistrationNativeLedger.handler crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query).run ledger) native
  have mapped := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work) original
  simpa only [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map, Prod.map_def, id_eq] using mapped
end BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTargetLedgerMap.full
