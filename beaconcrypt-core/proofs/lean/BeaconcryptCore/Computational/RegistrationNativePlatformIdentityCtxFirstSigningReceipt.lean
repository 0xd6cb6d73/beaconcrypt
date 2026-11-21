-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
/-! A first successful signing receipt for a fixed generated handle and message has an actual source-transcript prefix with no earlier successful signing of that message. Its bundle ordinal is the original public all-attempt marker, independent of any acceptance failure selector. Failed signing calls and all non-signing source observations remain in their original chronological lists. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt
open RegistrationNativePlatformIdentityCtxSigningLog (Trace Receipt)
open RegistrationNativePlatformIdentityCtxSigningSource (Aligned Call selected sourceCalls receiptCall traceCalls sourceCall)
open PqxdhDynamicIdentityPool (Observation SourceState)
variable {Value : Type}

def Matches (handle : Nat) (message : Pqxdh.Bytes) (receipt : Receipt) : Prop :=
  receipt.handle = handle ∧ receipt.message = message ∧ receipt.reply.isSome = true

private theorem first_split {A : Type} (predicate : A → Prop) (items : List A)
    (occurs : ∃ item ∈ items, predicate item) :
    ∃ earlier item later, items = earlier ++ item :: later ∧ predicate item ∧ ∀ prior ∈ earlier, ¬ predicate prior := by
  classical
  induction items with
  | nil => obtain ⟨_, impossible, _⟩ := occurs; cases impossible
  | cons head tail ih =>
    by_cases matched : predicate head
    · exact ⟨[], head, tail, rfl, matched, by simp⟩
    · obtain ⟨item, present, found⟩ := occurs
      have later : item ∈ tail := by
        rcases List.mem_cons.mp present with same | rest
        · exact False.elim (matched (same ▸ found))
        · exact rest
      obtain ⟨earlier, chosen, after, same, chosenMatch, fresh⟩ := ih ⟨item, later, found⟩
      refine ⟨head :: earlier, chosen, after, by rw [same]; rfl, chosenMatch, ?_⟩
      intro prior present
      rcases List.mem_cons.mp present with equal | included
      · exact equal ▸ matched
      · exact fresh prior included

/-- The first successful matching receipt is selected from the literal chronological log, retaining all earlier failed and unrelated requests. -/
theorem first (handle : Nat) (message : Pqxdh.Bytes) (trace : Trace)
    (occurs : ∃ receipt ∈ trace.log, Matches handle message receipt) :
    ∃ earlier receipt later, trace.log = earlier ++ receipt :: later ∧ Matches handle message receipt ∧
      ∀ prior ∈ earlier, ¬ Matches handle message prior := first_split (Matches handle message) trace.log occurs

private theorem prefix_fresh (handle : Nat) (message : Pqxdh.Bytes) (earlier : List Receipt)
    (fresh : ∀ prior ∈ earlier, ¬ Matches handle message prior) :
    message ∉ (earlier.map receiptCall).filterMap (selected handle) := by
  intro present
  rw [List.mem_filterMap] at present
  obtain ⟨call, member, chosen⟩ := present
  rw [List.mem_map] at member
  obtain ⟨receipt, included, rfl⟩ := member
  unfold selected receiptCall at chosen
  split at chosen
  next same =>
    cases answer : receipt.reply with
    | none => simp only [answer, Option.map_none, reduceCtorEq] at chosen
    | some signature =>
      simp only [answer, Option.map_some, Option.some.injEq] at chosen
      exact fresh receipt included ⟨same, chosen, by simp only [answer, Option.isSome_some]⟩
  next different => cases chosen

/-- Same-run alignment lifts the first trace receipt to an actual full private source-transcript prefix, whose successful source history is fresh for that exact handle/message. -/
theorem first_history (handle : Nat) (message : Pqxdh.Bytes) (trace : Trace)
    (before : RegistrationNativePlatformIdentityCtxSource.State) (aligned : Aligned (trace, before))
    (signed : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle before.1.transcript)) :
    ∃ earlier receipt later earlierSource call suffix,
      trace.log = earlier ++ receipt :: later ∧ Matches handle message receipt ∧
      (∀ prior ∈ earlier, ¬ Matches handle message prior) ∧
      before.1.transcript = earlierSource ++ call :: suffix ∧ sourceCall call = some (receiptCall receipt) ∧
      earlierSource.filterMap sourceCall = earlier.map receiptCall ∧
      message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle earlierSource) := by
  obtain ⟨receipt, member, handleSame, messageSame, success⟩ :=
    RegistrationNativePlatformIdentityCtxSigningSource.history_receipt handle message trace before aligned signed
  obtain ⟨earlier, chosen, later, splitLog, matching, fresh⟩ := first handle message trace ⟨receipt, member, handleSame, messageSame, success⟩
  have calls : before.1.transcript.filterMap sourceCall = earlier.map receiptCall ++ receiptCall chosen :: later.map receiptCall := by
    change sourceCalls before.1 = _
    rw [aligned.symm]
    simp only [traceCalls, splitLog, List.map_append, List.map_cons]
  obtain ⟨earlierSource, rest, splitSource, prefixCalls, restCalls⟩ := List.filterMap_eq_append_iff.mp calls
  obtain ⟨skipped, call, suffix, splitRest, noCalls, current, _laterCalls⟩ := List.filterMap_eq_cons_iff.mp restCalls
  have prefixEq : (earlierSource ++ skipped).filterMap sourceCall = earlier.map receiptCall := by
    rw [List.filterMap_append, prefixCalls, List.filterMap_eq_nil_iff.mpr noCalls, List.append_nil]
  refine ⟨earlier, chosen, later, earlierSource ++ skipped, call, suffix, splitLog, matching, fresh, ?_, current, prefixEq, ?_⟩
  · rw [splitSource, splitRest, List.append_assoc]
  · have actual := RegistrationNativePlatformIdentityCtxSigningSource.selected_history handle { before.1 with transcript := earlierSource ++ skipped }
    change PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle (earlierSource ++ skipped)) =
      ((earlierSource ++ skipped).filterMap sourceCall).filterMap (selected handle) at actual
    rw [actual, prefixEq]
    exact prefix_fresh handle message earlier fresh

open RegistrationNativeRawAdapter (TypedSpec)
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

/-- The actual private backend run supplies the first source receipt and its fresh prefix; every such receipt has an ordinal below the unchanged public typed bundle allowance. -/
theorem history_ordinal (work : OracleComp TypedSpec Value) (budget : Nat)
    (bounded : work.IsQueryBoundP RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle budget)
    (before : SourceState) (physicalBefore : RegistrationNativePlatformCtxBackend.State)
    (result : (Value × (SourceState × Trace)) × RegistrationNativePlatformIdentityCtxSource.State)
    (reached : result ∈ support ((simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      ((simulateQ (RegistrationNativePlatformIdentityCtxSigningTrace.wrap actual) work).run (before, {}))).run
        (PqxdhDynamicIdentityPool.initialState, physicalBefore)))
    (handle : Nat) (message : Pqxdh.Bytes)
    (signed : message ∈ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle result.2.1.transcript)) :
    ∃ ordinal earlier receipt later earlierSource call suffix,
      ordinal < budget ∧ receipt.bundle = some ordinal ∧
      result.1.2.2.log = earlier ++ receipt :: later ∧ Matches handle message receipt ∧
      (∀ prior ∈ earlier, ¬ Matches handle message prior) ∧
      result.2.1.transcript = earlierSource ++ call :: suffix ∧ sourceCall call = some (receiptCall receipt) ∧
      earlierSource.filterMap sourceCall = earlier.map receiptCall ∧
      message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history handle earlierSource) := by
  have aligned := RegistrationNativePlatformIdentityCtxSigningSource.typed_interpreted setup.joint actual work
    (before, {}) (PqxdhDynamicIdentityPool.initialState, physicalBefore) (by rfl) result reached
  obtain ⟨earlier, receipt, later, earlierSource, call, suffix, splitLog, matched, fresh, splitSource, called, prefixCalls, sourceFresh⟩ :=
    first_history handle message result.1.2.2 result.2 aligned signed
  have included : receipt ∈ result.1.2.2.log := by rw [splitLog]; exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨ordinal, tagged, finite⟩ := RegistrationNativePlatformIdentityCtxSigningTrace.source_receipt_budget
    setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer work budget bounded before (PqxdhDynamicIdentityPool.initialState, physicalBefore) result reached receipt included
  exact ⟨ordinal, earlier, receipt, later, earlierSource, call, suffix, finite, tagged, splitLog, matched, fresh, splitSource, called, prefixCalls, sourceFresh⟩
end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt.first_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt.first_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt.history_ordinal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFirstSigningReceipt.history_ordinal
