-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! A source-owned frontend invariant lifts through any persistent World interpretation and the original raw ledger adapter. The only generic premise is the literal per-source-query invariant; concrete owner mask and pending-pin instances are derived from the already checked source callback bodies. No real record support is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame
open RegistrationNativePlatformLorStatefulSupport (typed State)
variable {n : Nat} {KemSK Front Private Value : Type}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
    (invariant : Front → Prop)
    (step : ∀ query before result, invariant before →
      result ∈ support ((controller query).run before) → invariant result.2)

include step

theorem typed_preserves (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State Front Private)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State Front Private)
    (prior : invariant before.1)
    (supported : result ∈ support ((typed implementation controller query).run before)) : invariant result.2.1 :=
  step query before.1 (result.1,result.2.1) prior
    (RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller query before result supported)

theorem program_preserves (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State Front Private)
    (result : Value × State Front Private) (prior : invariant before.1)
    (supported : result ∈ support ((simulateQ (typed implementation controller) work).run before)) : invariant result.2.1 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (typed implementation controller) (fun current => invariant current.1)
    (fun query first valid next reached => typed_preserves implementation controller invariant step query first next valid reached)
    work before prior result supported

theorem full_preserves (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × State Front Private)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State Front Private))
    (prior : invariant before.2.1)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds
      (typed implementation controller) query).run before)) : invariant result.2.2.1 := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  rw [RegistrationNativeRawAdapter.program_native] at called
  have kept := program_preserves implementation controller invariant step _ before.2 reached prior called
  cases returned
  exact kept

theorem path_preserves (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State Front Private} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds (typed implementation controller)) before entries after)
    (prior : invariant before.2.1) : invariant after.2.1 :=
  RegistrationNativeSecretWordTargetPath.preserves _ (fun current => invariant current.2.1)
    (fun query first next valid reached => full_preserves implementation controller invariant step crypto wire serverKeyId bounds query first next valid reached)
    actual prior
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.typed_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.typed_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.program_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.program_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.full_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.full_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.path_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceFrame.path_preserves
