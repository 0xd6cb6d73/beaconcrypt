-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaRequestAlignment
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer

/-! The actual private signer log and native unsigned-payload receipts have a chronological, position-by-position relation. Complete source requests are linked to their actual payload/digest before ordinary-EUF message freshness is transferred. Failed signing replies are retained on both sides. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaChronology
open RegistrationNativeMldsaOpaque (Attempt Pool handleSource)
open RegistrationSigningShared (Receipt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (replyBytes)
open RegistrationNativeMldsaRequestAlignment (Correct SharedQuery)
open RegistrationNativeMldsaTableProgram (runState evaluate handler)
variable {n : Nat} {Value Next : Type}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

structure Match (attempt : Attempt) (receipt : Receipt) : Prop where
  publicKey : attempt.request.public_key = receipt.observation.publicKey
  correct : Correct attempt.request receipt.observation.payload receipt.digest
  reply : replyBytes attempt.reply = receipt.observation.reply

def Aligned (attempts : List Attempt) (receipts : List Receipt) : Prop := List.Forall₂ Match attempts receipts

theorem append (attempts : List Attempt) (receipts : List Receipt) (attempt : Attempt) (receipt : Receipt)
    (aligned : Aligned attempts receipts) (linked : Match attempt receipt) :
    Aligned (attempts ++ [attempt]) (receipts ++ [receipt]) :=
by
  induction aligned with
  | nil => exact .cons linked .nil
  | cons first rest ih => exact .cons first ih

/-- Every actual prior primitive attempt has its same-position native receipt and complete source operands. -/
theorem receipt_of_attempt (attempts : List Attempt) (receipts : List Receipt) (aligned : Aligned attempts receipts)
    (attempt : Attempt) (member : attempt ∈ attempts) :
    ∃ receipt ∈ receipts, Match attempt receipt := by
  induction aligned with
  | nil => cases member
  | @cons head receipt attempts receipts linked tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst attempt
        exact ⟨receipt, List.mem_cons_self, linked⟩
      · obtain ⟨found, inTail, matchFound⟩ := ih later
        exact ⟨found, List.mem_cons_of_mem receipt inTail, matchFound⟩

/-- Native weak message freshness transfers to every same-key complete request in the real private signer log, using the actual current cache and all attempted replies. -/
theorem fresh (attempts : List Attempt) (state : RegistrationSigningShared.State)
    (aligned : Aligned attempts state.1) (cached : RegistrationSigningShared.Cached state)
    (trial : MldsaTranscriptAuth.Trial) (verify : MldsaTranscriptAuth.Verify)
    (history : trial.history = RegistrationSigningShared.historyFor trial.publicKey state)
    (forgery : MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash state.2) verify trial)
    (attempt : Attempt) (member : attempt ∈ attempts)
    (selected : absBytes attempt.request.public_key = trial.publicKey) :
    absBytes attempt.request.input ≠ trial.candidate.message (MldsaSharedAuthentication.cacheHash state.2) := by
  obtain ⟨receipt, reached, linked⟩ := receipt_of_attempt attempts state.1 aligned attempt member
  have message := RegistrationNativeMldsaRequestAlignment.cached_message attempt.request receipt.observation.payload
    receipt.digest state.2 linked.correct (cached receipt reached)
  have callMember : receipt.observation.call ∈ trial.history := by
    rw [history, RegistrationSigningShared.historyFor]
    apply (BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff _ _ _).mpr
    exact ⟨receipt.observation, List.mem_map.mpr ⟨receipt, reached, rfl⟩,
      by rw [← linked.publicKey]; exact selected, rfl⟩
  rw [message.2]
  exact forgery.2 receipt.observation.call callMember

variable (source : RegistrationNativeMldsa.Source)

/-- The actual table records each complete reached request once before returning its original optional reply and private count, even for invalid handles. -/
theorem leaf_history (before : Pool source) (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (request : registration.MldsaSigningRequest)
    (result : (RegistrationSigningShared.SignReply × Nat) × Pool source)
    (supported : result ∈ support ((RegistrationNativeMldsaOpaque.actual source (.sign credential request)).run before)) :
    result.2.signing = before.signing ++ [⟨credential.secret, credential.publicKey, request, result.1.1⟩] := by
  classical
  simp only [RegistrationNativeMldsaOpaque.actual, StateT.run] at supported
  cases found : before.keys[credential.secret]? with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | some key =>
      simp only [found] at supported
      split at supported
      · rw [support_map] at supported
        obtain ⟨reply, _possible, same⟩ := supported
        cases same
        rfl
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        cases supported
        rfl

/-- Reified true-count table calls retain exactly that chronological request/reply append. -/
theorem call_history (accounting : RegistrationNativeMldsaCapability.Accounting)
    (before : PqxdhRecordLiftWorld.State n) (pool : Pool source)
    (credential : RegistrationNativeMldsa.Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (result : (RegistrationSigningShared.SignReply × PqxdhRecordLiftWorld.State n) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaProgram.call accounting (.sign credential request)) before pool)) :
    result.2.signing = pool.signing ++ [⟨credential.secret, credential.publicKey, request, result.1.1⟩] := by
  simp only [runState, evaluate, RegistrationNativeMldsaProgram.call, StateT.run, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, handler, map_apply, support_map] at supported
  obtain ⟨reply, possible, same⟩ := supported
  cases same
  exact leaf_history source pool credential request reply possible

namespace Server
variable (credential : RegistrationNativeMldsa.Credential (handleSource source))

/-- Each actual reified Server callback keeps the two chronological logs aligned under its source-derived request/payload condition. -/
theorem outgoing (query : RegistrationSigningShared.Spec.Domain) (correct : SharedQuery query)
    (before : RegistrationWorldSigning.State n) (pool : Pool source)
    (result : (RegistrationSigningShared.Spec.Range query × RegistrationWorldSigning.State n) × Pool source)
    (aligned : Aligned pool.signing before.2)
    (supported : result ∈ support
      (runState source (RegistrationNativeMldsaServer.outgoing (handleSource source) credential query) before pool)) :
    Aligned result.2.signing result.1.2.2 := by
  cases query with
  | hash request =>
      rw [RegistrationNativeMldsaServer.outgoing, RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
      obtain ⟨reply, possible, same⟩ := supported
      cases same
      simp only [RegistrationWorldSigning.outgoing, StateT.run, support_map] at possible
      obtain ⟨hashed, _queried, same⟩ := possible
      cases same
      exact aligned
  | sign request payload digest =>
      simp only [RegistrationNativeMldsaServer.outgoing, StateT.run, runState, evaluate,
        simulateQ_map, map_apply, support_map] at supported
      obtain ⟨reply, possible, same⟩ := supported
      cases same
      have history := call_history source .native before.1 pool credential request reply possible
      dsimp only [Prod.map, id] at ⊢
      rw [history]
      exact append _ _ _ _ aligned ⟨rfl, correct, rfl⟩

/-- Whole actual Server response source programs preserve chronological correspondence, including every failed signing or publication outcome. -/
theorem program (work : OracleComp RegistrationSigningShared.Spec Value)
    (correct : work.AllQueriesSatisfy SharedQuery) (before : RegistrationWorldSigning.State n) (pool : Pool source)
    (result : (Value × RegistrationWorldSigning.State n) × Pool source)
    (aligned : Aligned pool.signing before.2)
    (supported : result ∈ support
      (runState source (simulateQ (RegistrationNativeMldsaServer.outgoing (handleSource source) credential) work) before pool)) :
    Aligned result.2.signing result.1.2.2 := by
  induction work using OracleComp.inductionOn generalizing before pool with
  | pure value =>
      rw [simulateQ_pure, RegistrationNativeMldsaTableProgram.run_pure] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact aligned
  | query_bind query next ih =>
      obtain ⟨head, tail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp correct
      rw [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1.1 (tail middle.1.1) middle.1.2 middle.2
        (outgoing source credential query head before pool middle aligned queried) continued

end Server
end BeaconcryptCore.Computational.RegistrationNativeMldsaChronology
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.receipt_of_attempt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.receipt_of_attempt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.leaf_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.leaf_history
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.call_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.call_history
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.Server.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.Server.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.Server.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChronology.Server.program
