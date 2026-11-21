-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds
/-! The actual source completion has at most nine reached typed callback sites. Interpreting those literal sites bounds physical CTX requests without restricting optional failures or either mutable state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds
open BeaconcryptCore.Refinement
open RegistrationNativePlatformCtxCompletionProgram (Spec record sealed hashed written signed capability encoded)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformCtxBirthdayBudget (IsHash)
open RegistrationNativePlatformCtxLeafHashBounds (Bounded)
variable {n : Nat} {I KemSK Reader Response Platform E Input : Type} {base : OracleSpec I}

private theorem rec_with (head : RustM Input)
    (next : Input → OracleComp (Spec n) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerRecord.continueWith head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok value => exact bounded value
private theorem rec_result (head : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp (Spec n) (RustM RegistrationServerRecordExecutor.Result))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerRecord.continueResult head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok reply => cases reply with
    | Err state => trivial
    | Ok value => exact bounded value

private theorem write_bound (pending : registration.ServerRecordWrite) :
    (RegistrationNativePlatformServerRecord.fromWrite (written (n := n)) pending).IsTotalQueryBound 1 := by
  apply rec_with
  intro request
  unfold written
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩
private theorem hash_bound (pending : registration.ServerRecordCommitment) :
    (RegistrationNativePlatformCommitment.fromCommitment (hashed (n := n)) written pending).IsTotalQueryBound 2 := by
  rw [RegistrationNativePlatformCommitment.normalize]
  unfold hashed
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun result => rec_result _ _ 1 write_bound⟩
private theorem aead_bound (pending : registration.ServerRecordAead) :
    (RegistrationNativePlatformSourceRecord.fromAeadWithHash (sealed (n := n)) hashed written pending).IsTotalQueryBound 3 := by
  apply rec_with
  intro request
  unfold sealed
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun result => rec_result _ _ 2 hash_bound⟩
private theorem ratchet_bound (pending : registration.ServerInitialSeal) :
    (RegistrationNativePlatformSourceRecord.fromRatchetWithHash (record (n := n)) sealed hashed written pending).IsTotalQueryBound 4 := by
  apply rec_with
  intro request
  unfold record
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun result => rec_result _ _ 3 aead_bound⟩
private theorem record_bound (pending : registration.ServerInitialKdf) :
    (RegistrationNativePlatformSourceRecord.fromInitialWithHash (record (n := n)) sealed hashed written pending).IsTotalQueryBound 5 := by
  apply rec_with
  intro request
  unfold record
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun result => rec_result _ _ 4 ratchet_bound⟩

private theorem pub_with {X : Type} (head : RustM X)
    (next : X → OracleComp (Spec n) (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerPublication.continueWith head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok value => exact bounded value
private theorem pub_result {X : Type} (head : RustM (core.result.Result X pqxdh.ServerState))
    (next : X → OracleComp (Spec n) (RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8))))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerPublication.continueResult head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok reply => cases reply with
    | Err state => trivial
    | Ok value => exact bounded value
private theorem ready_bound (pending : registration.ServerResponseReady) :
    (RegistrationNativePlatformServerPublication.ready (encoded (n := n)) pending).IsTotalQueryBound 1 := by
  apply pub_with
  intro view
  unfold encoded
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩
private theorem signing_bound (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    (RegistrationNativePlatformServerPublication.signing (signed (n := n)) encoded payload digest pending).IsTotalQueryBound 2 := by
  apply pub_with
  intro request
  unfold signed
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun result => pub_result _ _ 1 ready_bound⟩
private theorem publication_bound (pending : registration.ServerResponseHash) :
    (RegistrationNativePlatformServerPublication.program (signed (n := n)) encoded pending).IsTotalQueryBound 3 := by
  apply pub_with
  intro request
  unfold signed
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun digest => pub_result _ _ 2 (signing_bound _ digest)⟩

private theorem complete_with {X : Type} (head : RustM X)
    (next : X → OracleComp (Spec n) (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerCompletion.continueWith head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok value => exact bounded value
private theorem complete_result {X : Type} (head : RustM (core.result.Result X pqxdh.ServerState))
    (next : X → OracleComp (Spec n) (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))))
    (cap : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound cap) :
    (RegistrationNativePlatformServerCompletion.continueResult head next).IsTotalQueryBound cap := by
  cases head with
  | fail error | div => trivial
  | ok reply => cases reply with
    | Err state => trivial
    | Ok value => exact bounded value
private theorem install_bound (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse (alloc.vec.Vec U8)) :
    (RegistrationNativePlatformServerCompletion.installWith (capability (n := n)) control published).IsTotalQueryBound 1 := by
  apply complete_result
  intro pending
  apply complete_with
  intro keyId
  apply complete_with
  intro parts
  unfold capability
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- All source KDF, AEAD, commitment, writer, publication and install sites fit the literal nine-callback skeleton. -/
theorem program (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    (RegistrationNativePlatformCtxCompletionProgram.program (n := n) control pending).IsTotalQueryBound 9 := by
  unfold RegistrationNativePlatformCtxCompletionProgram.program RegistrationNativePlatformSourceCompletion.fromInitialSource
  exact isTotalQueryBound_bind (record_bound pending) (fun recorded =>
    complete_result recorded _ 4 (fun response =>
      isTotalQueryBound_bind (publication_bound response) (fun published =>
        complete_result published _ 1 (install_bound control))))
section Physical
variable [sealPrimitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealPrimitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Each actual physical callback uses at most one CTX request, with no restriction on native or platform coins. -/
theorem query (request : (Spec n).Domain) :
    Bounded (RegistrationNativePlatformCtxCompletion.free setup codec view failure allocation erased sign helper writer request) 1 := by
  cases request with
  | records request =>
    exact RegistrationNativePlatformCtxLeafHashBounds.private_work _ 1
      (RegistrationNativePlatformCtxLeafHashBounds.records setup codec request)
  | «seal» request =>
    intro before previous
    exact (RegistrationNativePlatformCtxLeafHashBounds.sealing setup codec view failure allocation request before previous).mono (by decide)
  | hash request => exact RegistrationNativePlatformCtxLeafHashBounds.hash setup codec erased request
  | write request =>
    intro before previous
    exact (RegistrationNativePlatformCtxLeafHashBounds.write helper request before previous).mono (by decide)
  | signing request =>
    exact RegistrationNativePlatformCtxLeafHashBounds.private_work _ 1
      (RegistrationNativePlatformCtxLeafHashBounds.outgoing sign request)
  | encode current =>
    intro before previous
    exact (RegistrationNativePlatformCtxLeafHashBounds.encode writer current before previous).mono (by decide)
  | effect request =>
    exact RegistrationNativePlatformCtxLeafHashBounds.private_work _ 1
      (RegistrationNativePlatformCtxLeafHashBounds.effects request)

/-- The complete literal supplied-pending source body has a finite physical CTX budget on every failure and poststate. -/
theorem completion (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Bounded (RegistrationNativePlatformCtxCompletion.completion (n := n) setup codec view failure allocation erased sign helper writer control pending) 9 := by
  intro before previous
  apply RegistrationNativePlatformQueryBounds.simulate_bound (fun _ => True) IsHash _ _ _ 9
    ((isQueryBoundP_true_iff _ _).mpr (program control pending)) before previous
  intro request current prior
  exact query setup codec view failure allocation erased sign helper writer request current prior
end Physical

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds.completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionHashBounds.completion
