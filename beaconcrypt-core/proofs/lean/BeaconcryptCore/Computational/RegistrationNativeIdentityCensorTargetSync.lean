-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource

/-! Public and private target selection are synchronized at actual source request boundaries. Selection replies drive both updates, including fresh selection from none and stale-message refusal. Signing, physical hashing and markers retain all their literal effects; no selected-row or successful-signing condition is imposed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync
open RegistrationNativeIdentityCensorSource (State implementation censored)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorOperational (Spec)
variable {A : Type}

def targetAfter (query : Spec.Domain) (reply : Spec.Range query) (prior : Option Pqxdh.Bytes) : Option Pqxdh.Bytes :=
  match query, reply with
  | .inl (.inl (.inl (.inr message))), chosen => cond (show Bool from chosen) (some message) prior
  | _, _ => prior

/-- The sole private target-changing leaf is the real select operation, and its actual Boolean reply determines the update. -/
theorem source_step (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (query : Spec.Domain)
    (before : State) (result : Spec.Range query × State)
    (supported : result ∈ support ((implementation joint selected query).run before)) :
    result.2.target = targetAfter query result.1 before.target := by
  cases query with
  | inl query => cases query with
    | inl query => cases query with
      | inl query => cases query with
        | inl query =>
          simp only [implementation, RegistrationNativeIdentityCensorSource.protocol, StateT.run, support_map] at supported
          obtain ⟨returned, _called, rfl⟩ := supported
          rfl
        | inr message =>
          simp only [implementation, RegistrationNativeIdentityCensorSource.select, StateT.run] at supported
          split at supported
          all_goals obtain rfl := eq_of_mem_support_pure _ supported
          all_goals rfl
      | inr inspected =>
        simp only [implementation, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | inr described =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
      obtain ⟨returned, _called, rfl⟩ := supported
      rfl
  | inr marker => cases marker with
    | omitted handle message =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.omitted, StateT.run, support_map] at supported
      obtain ⟨returned, _called, rfl⟩ := supported
      rfl
    | template handle message leading trailing =>
      simp only [implementation, RegistrationNativeIdentityCensorSource.template, RegistrationNativeIdentityCensorSource.physical,
        StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨returned, _called, rfl⟩ := supported
      rfl

/-- The censored source still performs the same private select, even when omitted signing replies are replaced by the public placeholder. -/
theorem censored_step (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (query : Spec.Domain)
    (before : State) (result : Spec.Range query × State)
    (supported : result ∈ support ((censored joint selected placeholder query).run before)) :
    result.2.target = targetAfter query result.1 before.target := by
  cases query with
  | inl query => exact source_step joint selected (.inl query) before result supported
  | inr marker => cases marker with
    | template handle message leading trailing => exact source_step joint selected _ before result supported
    | omitted handle message =>
      simp only [censored, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨returned, called, continued⟩ := supported
      obtain rfl := eq_of_mem_support_pure _ continued
      exact source_step joint selected (.inr (.omitted handle message)) before returned called

noncomputable def lower (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) : QueryImpl Spec (StateT State ProbComp) :=
  if masked then censored joint selected placeholder else implementation joint selected

/-- Both actual private backends obey the same reply-driven target transition. -/
theorem lower_step (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (query : Spec.Domain)
    (before : State) (result : Spec.Range query × State)
    (supported : result ∈ support ((lower joint selected placeholder masked query).run before)) :
    result.2.target = targetAfter query result.1 before.target := by
  cases masked
  · exact source_step joint selected query before result supported
  · exact censored_step joint selected placeholder query before result supported

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem prepare_sync (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (message : Pqxdh.Bytes)
    (mode : Mode) (before : State) (prior : mode.target = before.target)
    (result : (Unit × Mode) × State)
    (supported : result ∈ support ((simulateQ (lower joint selected placeholder masked)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode)).run before)) :
    result.1.2.target = result.2.target := by
  simp only [RegistrationNativeIdentityCensorOperational.promote, RegistrationNativeIdentityCensorCompiler.prepare,
    StateT.run] at supported
  split at supported
  · split at supported
    · simp only [RegistrationNativeIdentityCensorCompiler.select, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed, bind_apply, mem_support_bind_iff] at supported
      obtain ⟨chosen, called, rest⟩ := supported
      have step := lower_step joint selected placeholder masked (.inl (.inl (.inl (.inr message)))) before chosen called
      cases chosenReply : chosen.1 with
      | false =>
        simp only [chosenReply, Bool.false_eq_true, ite_false, simulateQ_pure, pure_apply, mem_support_pure_iff] at rest
        cases rest
        exact prior.trans (by simpa only [targetAfter, chosenReply, Bool.cond_false] using step.symm)
      | true =>
        simp only [chosenReply, ite_true, RegistrationNativeIdentityCensorCompiler.inspect,
          simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
          simulateQ_pure, bind_apply, pure_apply, mem_support_bind_iff] at rest
        obtain ⟨inspected, calledInspect, returned⟩ := rest
        obtain rfl := eq_of_mem_support_pure _ returned
        have inspectStep := lower_step joint selected placeholder masked (.inl (.inl (.inr (message, mode.knownInputs)))) chosen.2 inspected calledInspect
        have selectedTarget : some message = chosen.2.target := by
          simpa only [targetAfter, chosenReply, Bool.cond_true] using step.symm
        exact selectedTarget.trans inspectStep.symm
    · simp only [pure_bind, Bool.false_eq_true, ite_false, simulateQ_pure, pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact prior
  · simp only [simulateQ_pure, pure_apply, mem_support_pure_iff] at supported
    cases supported
    exact prior

private theorem constant_sync (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (query : Spec.Domain)
    (mode : Mode) (before : State) (prior : mode.target = before.target)
    (stable : ∀ reply, targetAfter query reply before.target = before.target)
    (result : (Spec.Range query × Mode) × State)
    (supported : result ∈ support ((simulateQ (lower joint selected placeholder masked)
      (do let reply ← Spec.query query; pure (reply, mode))).run before)) :
    result.1.2.target = result.2.target := by
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨queried, called, returned⟩ := supported
  obtain rfl := eq_of_mem_support_pure _ returned
  exact prior.trans ((lower_step joint selected placeholder masked query before queried called).trans (stable queried.1)).symm

private theorem protocol_sync (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (mode : Mode) (before : State)
    (prior : mode.target = before.target) (result : (PqxdhJointPhase1Reports.ProtocolSpec.Range query × Mode) × State)
    (supported : result ∈ support ((simulateQ (lower joint selected placeholder masked)
      ((RegistrationNativeIdentityCensorOperational.promote
        (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol query))).run mode)).run before)) :
    result.1.2.target = result.2.target := by
  change result ∈ support ((simulateQ (lower joint selected placeholder masked)
    (do let reply ← Spec.query (.inl (.inl (.inl (.inl query)))); pure (reply, mode))).run before) at supported
  exact constant_sync joint selected placeholder masked (.inl (.inl (.inl (.inl query)))) mode before prior (fun _ => rfl) result supported

private theorem signing_sync (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool) (message : Pqxdh.Bytes)
    (mode : Mode) (before : State) (prior : mode.target = before.target)
    (result : (Option PqxdhEd25519EufCma.Ed25519Signature × Mode) × State)
    (supported : result ∈ support ((simulateQ (lower joint selected placeholder masked)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before)) :
    result.1.2.target = result.2.target := by
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind,
    simulateQ_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, called, rest⟩ := supported
  have synced := prepare_sync joint selected handle placeholder masked message mode before prior prepared called
  simp only [StateT.run_get, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, exists_eq_left] at rest
  split at rest
  · exact constant_sync joint selected placeholder masked (.inr (.omitted handle message)) prepared.1.2 prepared.2 synced (fun _ => rfl) result rest
  · exact constant_sync joint selected placeholder masked
      (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message))))))))
      prepared.1.2 prepared.2 synced (fun _ => rfl) result rest

/-- Each actual source request synchronizes the public Mode target with either private backend, including a first selection from none. -/
theorem lower_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (query : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (mode : Mode) (before : State)
    (prior : mode.target = before.target)
    (result : (RegistrationNativePlatformIdentityCtxCompiler.Spec.Range query × Mode) × State)
    (supported : result ∈ support ((simulateQ (lower joint selected placeholder masked)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder query).run mode)).run before)) :
    result.1.2.target = result.2.target := by
  rcases query with ((coin | request) | report) | bytes
  · exact protocol_sync joint selected placeholder masked (.inl (.inl coin)) mode before prior result supported
  · cases request with
    | create => exact protocol_sync joint selected placeholder masked (.inl (.inr .create)) mode before prior result supported
    | reveal handle => exact protocol_sync joint selected placeholder masked (.inl (.inr (.reveal handle))) mode before prior result supported
    | service handle request => cases request with
      | staticDh peer => exact protocol_sync joint selected placeholder masked (.inl (.inr (.service handle (.staticDh peer)))) mode before prior result supported
      | sign message => exact signing_sync joint selected handle placeholder masked message mode before prior result supported
  · exact protocol_sync joint selected placeholder masked (.inr report) mode before prior result supported
  · change result ∈ support ((simulateQ (lower joint selected placeholder masked)
      (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
      | none => do
          let reply ← Spec.query (.inr (.template selected mode.target
            (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2))
          pure (reply, mode))).run before) at supported
    split at supported
    · change result ∈ support ((simulateQ (lower joint selected placeholder masked)
        (do let reply ← Spec.query (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)))
            pure (reply, {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
              | none => mode.knownInputs
              | some input => mode.knownInputs ++ [input]}))).run before) at supported
      exact constant_sync joint selected placeholder masked
        (.inl (.inr (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes)))
        {mode with knownInputs := match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
          | none => mode.knownInputs
          | some input => mode.knownInputs ++ [input]}
        before prior (fun _ => rfl) result supported
    · exact constant_sync joint selected placeholder masked
        (.inr (.template selected mode.target (RegistrationNativeIdentityCensorOperational.parts bytes).1
          (RegistrationNativeIdentityCensorOperational.parts bytes).2)) mode before prior (fun _ => rfl) result supported

/-- Arbitrary actual lower source work preserves target synchronization, without assuming a target was already selected. -/
theorem lower_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (masked : Bool)
    (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec A) (mode : Mode) (before : State)
    (prior : mode.target = before.target) (result : (A × Mode) × State)
    (supported : result ∈ support ((simulateQ (lower joint selected placeholder masked)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    result.1.2.target = result.2.target := by
  induction work using OracleComp.inductionOn generalizing mode before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, continued⟩ := supported
    exact ih middle.1.1 middle.1.2 middle.2
      (lower_query joint selected placeholder masked request mode before prior middle called) result continued

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.source_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.censored_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.censored_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.lower_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.lower_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.lower_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.lower_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync.lower_program
