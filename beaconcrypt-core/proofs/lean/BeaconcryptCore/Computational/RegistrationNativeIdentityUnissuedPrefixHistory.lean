-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFamilyActual
/-! Actual prefix resource bounds supply exact source histories for the same eagerly sampled family and actual before-signing log. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixHistory
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace)
open RegistrationNativeIdentityUnissuedAcceptCut (Cut stop)
variable {A S : Type}

/-- A same-family prefix whose exact source marginal is available has the same successful signing messages as the literal observed log. -/
theorem messages (joint : PqxdhJointIdentity.Primitives) (count : Nat)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (work : OracleComp TypedSpec A)
    (before : S) (physical : RegistrationNativePlatformCtxBackend.State)
    (bounded : ((simulateQ RegistrationNativePlatformIdentityCtxIndependent.reify
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) work).run (before,{}))).run physical).IsQueryBoundP
        RegistrationNativeIdentityIndependentSource.IsCreate count)
    (result : RegistrationNativePlatformIdentityCtxFamily.Result count (A × (S × Trace)))
    (supported : result ∈ support (RegistrationNativePlatformIdentityCtxFamily.run joint count
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) work).run (before,{})) physical))
    (identity : Fin count) :
    PqxdhJointIdentity.signedMessages (result.2.2.2.histories identity) =
      RegistrationNativeIdentityUnissuedObserved.observedMessages identity.val result.2.1.1.2.2 := by
  have marginal := RegistrationNativePlatformIdentityCtxFamily.source_marginal joint count
    ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) work).run (before,{})) physical bounded
  have image := Set.mem_image_of_mem RegistrationNativePlatformIdentityCtxFamily.project supported
  rw [←support_map,←support_eq_of_evalDistEq marginal] at image
  have aligned := RegistrationNativePlatformIdentityCtxSigningSource.typed_interpreted joint frontend work
    (before,{}) (PqxdhDynamicIdentityPool.initialState,physical) rfl _ image
  rw [RegistrationNativePlatformIdentityCtxFamily.history joint count _ physical result supported identity]
  exact RegistrationNativeIdentityUnissuedObserved.messages_eq identity.val
    (((RegistrationNativePlatformIdentityCtxFamily.project result).1.2),
      (RegistrationNativePlatformIdentityCtxFamily.project result).2) aligned

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixHistory.messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedPrefixHistory.messages
