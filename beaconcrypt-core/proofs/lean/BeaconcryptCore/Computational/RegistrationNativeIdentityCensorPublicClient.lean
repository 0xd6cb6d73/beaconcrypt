-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop

/-! The executable causal client stops at a public selected parsed-accept ordinal or an earlier successful selected-tuple publication. It never selects a private bad acceptance. Every attempted bundle still uses the original public bundle marker. A stopped continuation issues no later primitive request, so a publication after the chosen acceptance cannot change this client's prefix event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {S Value : Type}

abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Spec := RegistrationNativeIdentityCensorOperational.Spec

def callback (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) :
    QueryImpl TypedSpec (StateT (S × Mode) (OracleComp Spec)) := fun query before => do
  let result ← (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
    ((frontend query).run before.1)).run (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2)
  pure (result.1.1, (result.1.2, result.2))

/-- Keeping the real source markers changes no executable reply or local state after their zero-sign-call EUF interpretation. -/
theorem callback_erasure (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain) (before : S × Mode) :
    simulateQ (RegistrationNativeIdentityCensorOperational.erase placeholder)
      ((callback selected bundle placeholder frontend query).run before) =
      (RegistrationNativeIdentityCensorCompiler.callback selected bundle placeholder frontend query).run before := by
  simp only [callback, RegistrationNativeIdentityCensorCompiler.callback, StateT.run, simulateQ_bind, simulateQ_pure]
  have literal := RegistrationNativeIdentityCensorOperational.program selected placeholder ((frontend query).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2)
  change simulateQ (RegistrationNativeIdentityCensorOperational.erase placeholder)
    (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) (frontend query before.1)
      (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2)) = _ at literal
  rw [literal]
  rfl

def IsAccept : TypedSpec.Domain → Prop
  | .inr (.accept _) => True
  | _ => False
instance : DecidablePred IsAccept := fun query => by
  unfold IsAccept
  split <;> infer_instance

abbrev ClientState (S : Type) := (S × Mode) × Nat

def step (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) :
    QueryImpl TypedSpec (StateT (ClientState S) (OracleComp Spec)) := fun query before =>
  (fun result => (result.1, (result.2, before.2 + if IsAccept query then 1 else 0))) <$>
    (callback selected bundle placeholder frontend query).run before.1

/-- Every parsed accept attempt is counted, including rejected source callbacks; bundle numbering remains separate. -/
theorem step_counter (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain)
    (before : ClientState S) (result : TypedSpec.Range query × ClientState S)
    (reached : result ∈ support ((step selected bundle placeholder frontend query).run before)) :
    result.2.2 = before.2 + if IsAccept query then 1 else 0 := by
  change result ∈ support ((fun returned => (returned.1, (returned.2, before.2 + if IsAccept query then 1 else 0))) <$>
    (callback selected bundle placeholder frontend query).run before.1) at reached
  rw [support_map] at reached
  obtain ⟨returned, _called, rfl⟩ := reached
  rfl

/-- The original syntactic parsed-accept allowance bounds this actual public marker without any success restriction. -/
theorem accept_budget (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (work : OracleComp TypedSpec Value)
    (budget : Nat) (bounded : work.IsQueryBoundP IsAccept budget) (before : ClientState S)
    (result : Value × ClientState S)
    (reached : result ∈ support ((simulateQ (step selected bundle placeholder frontend) work).run before)) :
    result.2.2 ≤ before.2 + budget := by
  induction work using OracleComp.inductionOn generalizing budget before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, first, last⟩ := reached
    have counted := step_counter selected bundle placeholder frontend query before middle first
    have continued := ih middle.1 _ (bounded.2 middle.1) middle.2 result last
    rw [counted] at continued
    by_cases counted : IsAccept query
    · have positive := bounded.1.resolve_left (fun denied => denied counted)
      simp only [counted, ite_true] at continued
      omega
    · simp only [counted, ite_false, Nat.add_zero] at continued
      exact continued

inductive Stop where
  | published
  | attempted (packet : registration.InitPacket) (reply : RustM (Option Nat))

/-- Both tests use the public command, its public reply, the all-attempt counter and this callback's active selected-message flag. -/
def observe (accept : Nat) : RegistrationNativeMldsaStop.Observer (spec := TypedSpec) (State := ClientState S) (Candidate := Stop)
  | .inr (.bundle _), _before, reply, after =>
      if after.1.2.active ∧ (RegistrationNativeRawAdapter.resultOption reply).isSome then some .published else none
  | .inr (.accept packet), before, reply, _after =>
      if before.2 = accept then some (.attempted packet reply) else none
  | _, _, _, _ => none

def freeze (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaultReply : (query : TypedSpec.Domain) → TypedSpec.Range query) :
    QueryImpl TypedSpec (StateT (ClientState S × Option Stop) (OracleComp Spec)) :=
  RegistrationNativeMldsaStop.freeze (step selected bundle placeholder frontend) (observe accept) defaultReply

/-- Selecting the public stop freezes the complete exact snapshot and makes no further source or hash query. -/
theorem stopped (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaultReply : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec Value)
    (before : ClientState S) (reason : Stop) :
    ∃ value, (simulateQ (freeze selected bundle accept placeholder frontend defaultReply) work).run (before, some reason) =
      pure (value, (before, some reason)) :=
  RegistrationNativeMldsaStop.stopped (step selected bundle placeholder frontend) (observe accept) defaultReply work before reason

/-- The selected parsed-accept test depends only on the original ordinal and retains its actual public packet and callback reply. -/
theorem accept_stop (accept : Nat) (packet : registration.InitPacket) (reply : RustM (Option Nat))
    (before after : ClientState S) (selected : before.2 = accept) :
    observe accept (.inr (.accept packet)) before reply after = some (.attempted packet reply) := by
  simp only [observe, selected, ite_true]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.callback_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.callback_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.step_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.step_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.accept_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.accept_budget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.accept_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicClient.accept_stop
