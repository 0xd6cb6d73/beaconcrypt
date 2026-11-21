-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSignScope
/-! An analysis-only passthrough records the exact indexed signing request and optional reply in the same free CTX execution. No request is omitted or replaced. The bundle tag is selected by the enclosing typed callback marker, without consulting an acceptance event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSignScope (Allowed IsSign)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}

structure Receipt where
  bundle : Option Nat
  handle : Nat
  message : Pqxdh.Bytes
  reply : Option Ed25519Signature

structure Trace where
  nextBundle : Nat := 0
  log : List Receipt := []

def signing : (query : Spec.Domain) → Spec.Range query → Option (Nat × Pqxdh.Bytes × Option Ed25519Signature)
  | .inl (.inl (.inr (.service handle (.sign message)))), reply => some (handle, message, reply)
  | _, _ => none

def remember (tag : Option Nat) (query : Spec.Domain) (reply : Spec.Range query) (before : Trace) : Trace :=
  match signing query reply with
  | none => before
  | some (handle, message, answer) => { before with log := before.log ++ [⟨tag, handle, message, answer⟩] }

def logging (tag : Option Nat) : QueryImpl Spec (StateT Trace (OracleComp Spec)) := fun query before =>
  (fun reply => (reply, remember tag query reply before)) <$> (Spec.query query : OracleComp Spec _)

private theorem logging_run (tag : Option Nat) (query : Spec.Domain) (before : Trace) :
    (logging tag query).run before =
      (fun reply => (reply, remember tag query reply before)) <$> (Spec.query query : OracleComp Spec _) := rfl

def Valid (trace : Trace) : Prop := ∀ receipt ∈ trace.log,
  ∃ ordinal, receipt.bundle = some ordinal ∧ ordinal < trace.nextBundle

private theorem remember_next (tag : Option Nat) (query : Spec.Domain) (reply : Spec.Range query) (before : Trace) :
    (remember tag query reply before).nextBundle = before.nextBundle := by
  unfold remember
  split <;> rfl

private theorem signing_allowed (query : Spec.Domain) (reply : Spec.Range query) (allowed : Allowed query) :
    signing query reply = none := by
  cases query with
  | inr bytes => rfl
  | inl query => cases query with
    | inr report => rfl
    | inl query => cases query with
      | inl coin => rfl
      | inr query => cases query with
        | create | reveal handle => rfl
        | service handle request => cases request with
          | staticDh point => rfl
          | sign message => exact False.elim (allowed True.intro)

private theorem remember_allowed (tag : Option Nat) (query : Spec.Domain) (reply : Spec.Range query) (before : Trace)
    (allowed : Allowed query) : remember tag query reply before = before := by
  rw [remember, signing_allowed query reply allowed]

/-- Erasing the analysis log gives exactly the original free program, including every request and reply. -/
theorem erase (tag : Option Nat) (work : OracleComp Spec A) (before : Trace) :
    Prod.fst <$> (simulateQ (logging tag) work).run before = work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logging_run, map_bind, bind_map_left]
    exact bind_congr (fun reply => ih reply (remember tag query reply before))

/-- A genuinely non-signing source tree leaves the entire analysis trace unchanged. -/
theorem no_sign (tag : Option Nat) (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy Allowed) (before : Trace) :
    (simulateQ (logging tag) work).run before = (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logging_run, map_bind, bind_map_left]
    apply bind_congr
    intro reply
    rw [remember_allowed tag query reply before allowed.1]
    exact ih reply (allowed.2 reply) before

/-- Primitive query logging never changes the enclosing public bundle-attempt counter. -/
theorem next_unchanged (tag : Option Nat) (work : OracleComp Spec A) (before : Trace) (result : A × Trace)
    (supported : result ∈ support ((simulateQ (logging tag) work).run before)) : result.2.nextBundle = before.nextBundle := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logging_run, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨reply, _queried, continued⟩ := supported
    exact (ih reply (remember tag query reply before) result continued).trans (remember_next tag query reply before)

private theorem remember_valid (tag : Option Nat) (query : Spec.Domain) (reply : Spec.Range query) (before : Trace)
    (valid : Valid before) (tagged : ∃ ordinal, tag = some ordinal ∧ ordinal < before.nextBundle) :
    Valid (remember tag query reply before) := by
  cases found : signing query reply with
  | none => simpa only [remember, found] using valid
  | some call =>
    rcases call with ⟨handle, message, answer⟩
    intro receipt member
    simp only [remember_next]
    simp only [remember, found, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact valid receipt member
    · exact tagged

/-- Every newly recorded successful or failed signing reply carries the enclosing supplied public bundle ordinal. -/
theorem valid (tag : Option Nat) (work : OracleComp Spec A) (before : Trace) (result : A × Trace)
    (prior : Valid before) (tagged : ∃ ordinal, tag = some ordinal ∧ ordinal < before.nextBundle)
    (supported : result ∈ support ((simulateQ (logging tag) work).run before)) : Valid result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, logging_run, bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨reply, _queried, continued⟩ := supported
    exact ih reply (remember tag query reply before) result (remember_valid tag query reply before prior tagged)
      (by simpa only [remember_next] using tagged) continued
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.erase' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.no_sign' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.no_sign

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.next_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.next_unchanged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningLog.valid
