-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningTrace
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistory

/-! The analysis signing log and the private source transcript record the same complete request and optional reply on the same execution. Failed signing calls remain in both lists. This bridge does not infer an occurrence from a final signature value or reveal a private source seed to the executable client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace Receipt signing remember logging)
open PqxdhDynamicIdentityPool (SourceState Observation)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}
abbrev Call := Nat × Pqxdh.Bytes × Option Ed25519Signature

def sourceCall : Observation → Option Call
  | ⟨.inr (.service handle (.sign message)), reply⟩ => some (handle, message, reply)
  | _ => none

def sourceCalls (pool : SourceState) : List Call := pool.transcript.filterMap sourceCall

def receiptCall (receipt : Receipt) : Call := (receipt.handle, receipt.message, receipt.reply)
def traceCalls (trace : Trace) : List Call := trace.log.map receiptCall

def Aligned (before : Trace × State) : Prop := traceCalls before.1 = sourceCalls before.2.1

private theorem record_calls (query : PqxdhDynamicIdentityPool.DynamicSpec.Domain)
    (reply : PqxdhDynamicIdentityPool.DynamicSpec.Range query) (before : SourceState) :
    sourceCalls (PqxdhDynamicIdentityPool.record query reply before) =
      sourceCalls before ++ (sourceCall ⟨query, reply⟩).toList := by
  simp only [sourceCalls, PqxdhDynamicIdentityPool.record, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases sourceCall ⟨query, reply⟩ <;> rfl

private theorem source_query (joint : PqxdhJointIdentity.Primitives) (query : Spec.Domain)
    (before : State) (result : Spec.Range query × State)
    (reached : result ∈ support ((implementation joint query).run before)) :
    sourceCalls result.2.1 = sourceCalls before.1 ++ (signing query result.1).toList := by
  cases query with
  | inr bytes =>
    simp only [implementation, StateT.run, support_map] at reached
    obtain ⟨returned, _called, rfl⟩ := reached
    exact (List.append_nil _).symm
  | inl query =>
    simp only [implementation, StateT.run, support_map] at reached
    obtain ⟨returned, called, rfl⟩ := reached
    cases query with
    | inr report =>
      simp only [RegistrationNativeIdentityMainSource.implementation] at called
      cases called
      exact (List.append_nil _).symm
    | inl query =>
      cases query with
      | inl coin =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, mem_support_bind_iff] at called
        obtain ⟨answer, _sampled, literal⟩ := called
        simp only [mem_support_pure_iff] at literal
        cases literal
        simpa only [sourceCall, signing, Option.toList_none, List.append_nil] using record_calls (.inl coin) answer before.1
      | inr query => cases query with
        | create =>
          change returned ∈ support ((PqxdhDynamicIdentityPool.lazyImpl joint (.inr .create)).run before.1) at called
          rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at called
          obtain ⟨seed, _sampled, rfl⟩ := called
          simpa only [PqxdhDynamicIdentityPool.createdReply, sourceCall, signing, Option.toList_none,
            List.append_nil, sourceCalls] using record_calls (.inr .create)
              (some (before.1.seeds.length, joint.publicKeys seed)) { before.1 with seeds := before.1.seeds ++ [seed] }
        | reveal handle =>
          simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl, mem_support_pure_iff] at called
          cases called
          simpa only [sourceCall, signing, Option.toList_none, List.append_nil] using
            record_calls (.inr (.reveal handle)) before.1.seeds[handle]? before.1
        | service handle request =>
          simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
            PqxdhDynamicIdentityPool.poolImpl, mem_support_pure_iff] at called
          cases called
          cases request <;> exact record_calls _ _ _

private theorem remember_calls (tag : Option Nat) (query : Spec.Domain) (reply : Spec.Range query) (before : Trace) :
    traceCalls (remember tag query reply before) = traceCalls before ++ (signing query reply).toList := by
  unfold remember
  cases found : signing query reply with
  | none => exact (List.append_nil _).symm
  | some call =>
    rcases call with ⟨handle, message, answer⟩
    simp only [traceCalls, List.map_append, List.map_cons, List.map_nil, receiptCall, Option.toList_some]

noncomputable def handler (joint : PqxdhJointIdentity.Primitives) (tag : Option Nat) :
    QueryImpl Spec (StateT (Trace × State) ProbComp) :=
  QueryImpl.Stateful.link (logging tag) (implementation joint)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem query (joint : PqxdhJointIdentity.Primitives) (tag : Option Nat) (request : Spec.Domain)
    (before : Trace × State) :
    (handler joint tag request).run before =
      (fun result => (result.1, (remember tag request result.1 before.1, result.2))) <$>
        (implementation joint request).run before.2 := by
  rw [handler, QueryImpl.Stateful.link_impl_apply_run]
  simp only [logging, StateT.run, simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map]
  rfl

private theorem step (joint : PqxdhJointIdentity.Primitives) (tag : Option Nat) (request : Spec.Domain)
    (before : Trace × State) (prior : Aligned before)
    (result : Spec.Range request × (Trace × State))
    (reached : result ∈ support ((handler joint tag request).run before)) : Aligned result.2 := by
  rw [query, support_map] at reached
  obtain ⟨returned, called, rfl⟩ := reached
  exact (remember_calls tag request returned.1 before.1).trans
    ((congrArg (fun earlier => earlier ++ (signing request returned.1).toList) prior).trans
      (source_query joint request before.2 returned called).symm)

/-- Every adaptive source prefix keeps all failed and successful indexed signing calls aligned with its analysis log. -/
theorem synchronized (joint : PqxdhJointIdentity.Primitives) (tag : Option Nat)
    (work : OracleComp Spec Value) (before : Trace × State) (prior : Aligned before)
    (result : Value × (Trace × State))
    (reached : result ∈ support ((simulateQ (handler joint tag) work).run before)) : Aligned result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (handler joint tag) Aligned (step joint tag) work before prior result reached

/-- Interpreting the actual passthrough logger with the original source retains the same chronological signing list, without erasing either private coordinate. -/
theorem interpreted (joint : PqxdhJointIdentity.Primitives) (tag : Option Nat)
    (work : OracleComp Spec Value) (trace : Trace) (before : State) (prior : Aligned (trace, before))
    (result : (Value × Trace) × State)
    (reached : result ∈ support ((simulateQ (implementation joint)
      ((simulateQ (logging tag) work).run trace)).run before)) : Aligned (result.1.2, result.2) := by
  apply synchronized joint tag work (trace, before) prior (result.1.1, (result.1.2, result.2))
  rw [handler, QueryImpl.Stateful.simulateQ_link_run, support_map]
  exact ⟨result, reached, rfl⟩

open RegistrationNativeRawAdapter (TypedSpec)
variable {S : Type}

private theorem marked_calls (query : TypedSpec.Domain) (before : Trace) :
    traceCalls (RegistrationNativePlatformIdentityCtxSigningTrace.mark query before).2 = traceCalls before := by
  unfold RegistrationNativePlatformIdentityCtxSigningTrace.mark
  split <;> rfl

private theorem typed_query (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain)
    (before : S × Trace) (privateBefore : State) (prior : Aligned (before.2, privateBefore))
    (result : (TypedSpec.Range query × (S × Trace)) × State)
    (reached : result ∈ support ((simulateQ (implementation joint)
      ((RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend query).run before)).run privateBefore)) :
    Aligned (result.1.2.2, result.2) := by
  unfold RegistrationNativePlatformIdentityCtxSigningTrace.wrap at reached
  simp only [StateT.run, simulateQ_map, map_apply, support_map] at reached
  obtain ⟨inner, called, rfl⟩ := reached
  apply interpreted joint (RegistrationNativePlatformIdentityCtxSigningTrace.mark query before.2).1
    ((frontend query).run before.1) (RegistrationNativePlatformIdentityCtxSigningTrace.mark query before.2).2 privateBefore ?_ inner called
  exact (marked_calls query before.2).trans prior

noncomputable def typedHandler (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) :
    QueryImpl TypedSpec (StateT ((S × Trace) × State) ProbComp) :=
  QueryImpl.Stateful.link (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) (implementation joint)

private theorem typed_step (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec))) (query : TypedSpec.Domain)
    (before : (S × Trace) × State) (prior : Aligned (before.1.2, before.2))
    (result : TypedSpec.Range query × ((S × Trace) × State))
    (reached : result ∈ support ((typedHandler joint frontend query).run before)) :
    Aligned (result.2.1.2, result.2.2) := by
  rw [typedHandler, QueryImpl.Stateful.link_impl_apply_run, support_map] at reached
  obtain ⟨inner, called, rfl⟩ := reached
  exact typed_query joint frontend query before.1 before.2 prior inner called

/-- The public all-attempt typed marker and the exact private backend retain the same source signing list through the full adaptive callback program. -/
theorem typed_interpreted (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Spec)))
    (work : OracleComp TypedSpec Value) (before : S × Trace) (privateBefore : State)
    (prior : Aligned (before.2, privateBefore)) (result : (Value × (S × Trace)) × State)
    (reached : result ∈ support ((simulateQ (implementation joint)
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap frontend) work).run before)).run privateBefore)) :
    Aligned (result.1.2.2, result.2) := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query (typedHandler joint frontend)
    (fun current => Aligned (current.1.2, current.2)) (typed_step joint frontend) work
    (before, privateBefore) prior (result.1.1, (result.1.2, result.2))
  rw [typedHandler, QueryImpl.Stateful.simulateQ_link_run, support_map]
  exact ⟨result, reached, rfl⟩

def selected (handle : Nat) (call : Call) : Option Pqxdh.Bytes :=
  if call.1 = handle then call.2.2.map (fun _ => call.2.1) else none

/-- Successful source signing-history messages are precisely the matching successful entries of the complete request/reply list. -/
theorem selected_history (handle : Nat) (before : SourceState) :
    PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle before.transcript) =
      (sourceCalls before).filterMap (selected handle) := by
  simp only [PqxdhJointIdentity.signedMessages, RegistrationNativeIdentityHistory.history, sourceCalls,
    List.filterMap_filterMap]
  congr 1
  funext observation
  rcases observation with ⟨query, reply⟩
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | create | reveal index => rfl
    | service index request =>
      cases request with
      | sign message =>
        cases reply <;> by_cases same : index = handle <;>
          simp [RegistrationNativeIdentityHistory.entry, sourceCall, selected, PqxdhJointIdentity.requestEvent, same]
      | staticDh peer =>
        cases reply <;> simp [RegistrationNativeIdentityHistory.entry, sourceCall, selected,
          PqxdhJointIdentity.requestEvent]

/-- A message in the actual successful source history has an actual matching successful receipt in an aligned same-run trace. -/
theorem history_receipt (handle : Nat) (message : Pqxdh.Bytes) (trace : Trace) (before : State)
    (aligned : Aligned (trace, before))
    (signed : message ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history handle before.1.transcript)) :
    ∃ receipt ∈ trace.log, receipt.handle = handle ∧ receipt.message = message ∧ receipt.reply.isSome = true := by
  rw [selected_history, ← aligned] at signed
  simp only [traceCalls, List.mem_filterMap] at signed
  obtain ⟨call, member, selectedCall⟩ := signed
  rw [List.mem_map] at member
  obtain ⟨receipt, present, rfl⟩ := member
  unfold selected receiptCall at selectedCall
  split at selectedCall
  next same =>
    cases answer : receipt.reply with
    | none => simp only [answer, Option.map_none, reduceCtorEq] at selectedCall
    | some signature =>
      simp only [answer, Option.map_some, Option.some.injEq] at selectedCall
      exact ⟨receipt, present, same, selectedCall, by simp only [answer, Option.isSome_some]⟩
  next different => cases selectedCall

section Actual
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "SourceState" => RegistrationNativeIdentityMain.State n KemSK source × Platform

/-- The literal typed source program assigns every actual successful signing-history message a finite public bundle-attempt ordinal. The private seed/cache interpretation is retained jointly and supplies the occurrence rather than an assumed membership premise. -/
theorem history_ordinal (work : OracleComp TypedSpec Value) (budget : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle budget)
    (before : SourceState) (physicalBefore : RegistrationNativePlatformCtxBackend.State)
    (result : (Value × (SourceState × Trace)) × State)
    (reached : result ∈ support ((simulateQ (implementation setup.joint)
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap actual) work).run (before, {}))).run
        (PqxdhDynamicIdentityPool.initialState, physicalBefore)))
    (handle : Nat) (message : Pqxdh.Bytes)
    (signed : message ∈ PqxdhJointIdentity.signedMessages
      (RegistrationNativeIdentityHistory.history handle result.2.1.transcript)) :
    ∃ ordinal, ordinal < budget ∧ ∃ receipt ∈ result.1.2.2.log,
      receipt.bundle = some ordinal ∧ receipt.handle = handle ∧ receipt.message = message ∧ receipt.reply.isSome = true := by
  have aligned := typed_interpreted setup.joint actual work (before, {})
    (PqxdhDynamicIdentityPool.initialState, physicalBefore) (by rfl) result reached
  obtain ⟨receipt, member, sameHandle, sameMessage, successful⟩ :=
    history_receipt handle message result.1.2.2 result.2 aligned signed
  obtain ⟨ordinal, tagged, finite⟩ := RegistrationNativePlatformIdentityCtxSigningTrace.source_receipt_budget
    setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer work budget bounded before (PqxdhDynamicIdentityPool.initialState, physicalBefore) result reached receipt member
  exact ⟨ordinal, finite, receipt, member, tagged, sameHandle, sameMessage, successful⟩
end Actual

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.synchronized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.synchronized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.interpreted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.typed_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.typed_interpreted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.selected_history' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.selected_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.history_receipt' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.history_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.history_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource.history_ordinal
