-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFreeStageTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
/-! The actual before-call signature log recovers the complete successful source signing history at every chronological callback. Only that projected log is needed to express unissued attached fields. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePlatformIdentityCtxSigningSource (typedHandler Aligned traceCalls sourceCalls selected)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace)
variable {S A : Type}
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Whole (S : Type) := (S × Trace) × RegistrationNativePlatformIdentityCtxSource.State

def Coherent (before : Whole S) : Prop := Aligned (before.1.2,before.2)

def sourceMessages (handle : Nat) (before : Whole S) : List Pqxdh.Bytes :=
  PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle before.2.1.transcript)

def observedMessages (handle : Nat) (trace : Trace) : List Pqxdh.Bytes :=
  (traceCalls trace).filterMap (selected handle)

/-- Successful signing messages are exactly the same ordered public reply log, with rejected and future-handle requests still absent. -/
theorem messages_eq (handle : Nat) (before : Whole S) (prior : Coherent before) :
    sourceMessages handle before = observedMessages handle before.1.2 := by
  change traceCalls before.1.2 = sourceCalls before.2.1 at prior
  rw [sourceMessages,RegistrationNativePlatformIdentityCtxSigningSource.selected_history,←prior]
  rfl

private theorem coherent_query (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain)
    (before : Whole S) (prior : Coherent before) (result : TypedSpec.Range query × Whole S)
    (supported : result ∈ support ((typedHandler joint frontend query).run before)) : Coherent result.2 := by
  rw [typedHandler,QueryImpl.Stateful.link_impl_apply_run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact RegistrationNativePlatformIdentityCtxSigningSource.typed_interpreted joint frontend (TypedSpec.query query)
    before.1 before.2 prior inner (by simpa only [simulateQ_spec_query] using called)

/-- Every prefix of the same actual path retains this exact source/public-log alignment. -/
theorem coherent_path (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    {before after : Whole S} {calls : List (Call TypedSpec (Whole S))}
    (actual : Path (typedHandler joint frontend) before calls after) (prior : Coherent before) : Coherent after := by
  induction actual with
  | nil state => exact prior
  | cons call called rest last following ih =>
      exact ih (coherent_query joint frontend call.query call.before prior (call.reply,call.after) called)

/-- The complete actual initialized source journal supplies every callback's original before-signing history without a caller-owned history or final-owner admission premise. -/
theorem initialized_messages (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (work : OracleComp TypedSpec A)
    (before : S) (physical : RegistrationNativePlatformCtxBackend.State)
    (result : A × (Whole S × List (Call TypedSpec (Whole S))))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler (typedHandler joint frontend)) work).run
      (((before,{}),(PqxdhDynamicIdentityPool.initialState,physical)),[]))) :
    ∀ call ∈ result.2.2, ∀ handle, sourceMessages handle call.before = observedMessages handle call.before.1.2 := by
  have actual := RegistrationNativeStageTrace.path (typedHandler joint frontend) work
    ((before,{}),(PqxdhDynamicIdentityPool.initialState,physical)) result supported
  intro call member handle
  obtain ⟨_leading,_trailing,_same,leadingPath,_called,_following⟩ := actual.member call member
  exact messages_eq handle call.before (coherent_path joint frontend leadingPath rfl)

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved.messages_eq' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved.messages_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved.coherent_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved.coherent_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved.initialized_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedObserved.initialized_messages
