-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource

/-! A public selector and its successful-reply log extend the template compiler before selection. Local state contains messages, the selected public target and symbolic cache/journal only. The private key table and genuine protocol audit remain in the separate source interpreter. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec coins source)
open RegistrationNativeIdentityReindexedCtx (State)
open RegistrationNativeIdentityTemplateAddress (Key)
open PqxdhDynamicIdentityPool (SourceState)
open RegistrationNativeIdentityCensorPolicySource (update choose messages)
variable {Value : Type}
abbrev Public := Policy × State Key

/-- This compiler records only public successful optional replies; hidden canonical attempts have already become pure placeholder returns in the marker-erased input program. -/
noncomputable def handler (selected : Nat) : QueryImpl Spec (StateT Public (OracleComp PublicSpec))
  | .inl (.inl (.inl query)) => fun before => do
      let answer ← PublicSpec.query (.inl query)
      pure (answer, (update selected query answer before.1, before.2))
  | .inl (.inl (.inr message)) => fun before =>
      let result := choose message before.1
      pure (result.1, (result.2, before.2))
  | .inl (.inr _) => pure ()
  | .inr described => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$>
        simulateQ coins ((RegistrationNativeIdentityReindexedCtx.implementation described.input).run before.2)

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (do let answer ← work; pure (answer, before)) := rfl

/-- After actual selection, the public policy is observational bookkeeping and the remaining compiler is the previously proved protocol/table compiler. -/
theorem query_after_some (selected : Nat) (target : Pqxdh.Bytes) (request : Spec.Domain) (before : Public)
    (held : before.1.target = some target) :
    Prod.map id Prod.snd <$> (handler selected request).run before =
      (RegistrationNativeIdentityTemplateProtocol.handler request).run before.2 := by
  rcases request with ((protocol | message) | scan) | described
  · simp only [handler, RegistrationNativeIdentityTemplateProtocol.handler,
      StateT.run, lift_apply, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
    rfl
  · simp only [handler, choose, held, reduceCtorEq, false_and, ite_false,
      RegistrationNativeIdentityTemplateProtocol.handler, StateT.run, pure_apply, map_pure, Prod.map_def, id_eq]
  · simp only [handler, RegistrationNativeIdentityTemplateProtocol.handler, StateT.run_pure,
      map_pure, Prod.map_def, id_eq]
  · simp only [handler, RegistrationNativeIdentityTemplateProtocol.handler, StateT.run,
      Functor.map_map, Prod.map_def, id_eq]
    exact id_map _

/-- Every possible query reply preserves an existing public target, including rejected services and every hash reply. -/
theorem query_target (selected : Nat) (target : Pqxdh.Bytes) (request : Spec.Domain) (before : Public)
    (held : before.1.target = some target) (result : Spec.Range request × Public)
    (reached : result ∈ support ((handler selected request).run before)) : result.2.1.target = some target := by
  rcases request with ((protocol | message) | scan) | described
  · simp only [handler, StateT.run, bind_pure_comp, support_map] at reached
    obtain ⟨answer, _called, rfl⟩ := reached
    exact held
  · simp only [handler, choose, held, reduceCtorEq, false_and, ite_false, StateT.run,
      mem_support_pure_iff] at reached
    cases reached
    exact held
  · simp only [handler, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact held
  · simp only [handler, StateT.run, support_map] at reached
    obtain ⟨actual, _called, rfl⟩ := reached
    exact held

/-- All adaptive postselection work erases the public forwarding log exactly, without deleting any protocol request or replacing its reply. -/
theorem program_after_some (selected : Nat) (target : Pqxdh.Bytes) (work : OracleComp Spec Value) (before : Public)
    (held : before.1.target = some target) :
    Prod.map id Prod.snd <$> (simulateQ (handler selected) work).run before =
      (simulateQ RegistrationNativeIdentityTemplateProtocol.handler work).run before.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query_after_some selected target request before held]
    rw [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 result.2 (query_target selected target request before held result reached)

noncomputable def execute (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (work : OracleComp Spec Value)
    (before : Public × SourceState) : ProbComp ((Value × Public) × SourceState) :=
  (simulateQ (source joint) ((simulateQ (handler selected) work).run before.1)).run before.2

def Aligned (selected : Nat) (before : Public × SourceState) : Prop :=
  before.1.1.forwarded = messages selected before.2

private theorem coins_apply (joint : PqxdhJointIdentity.Primitives) (work : ProbComp Value) (before : SourceState) :
    (simulateQ (source joint) (simulateQ coins work)) before = (fun value => (value, before)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin current
  change (do let answer ← unifSpec.query coin; pure (answer, current) : ProbComp _) = _
  simp only [bind_pure_comp]

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The public successful-reply log is exactly the genuine source signing-message history on every reached query outcome. Canonical omitted calls are absent from both histories. -/
theorem query_history (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (request : Spec.Domain)
    (before : Public × SourceState) (prior : Aligned selected before)
    (result : (Spec.Range request × Public) × SourceState)
    (reached : result ∈ support (execute joint selected (Spec.query request) before)) :
    Aligned selected (result.1.2, result.2) := by
  rcases request with ((protocol | message) | scan) | described
  · simp only [execute, simulateQ_spec_query, handler, StateT.run, bind_pure_comp,
      simulateQ_map, map_apply, source, support_map] at reached
    obtain ⟨actual, called, rfl⟩ := reached
    have factual := RegistrationNativeIdentityCensorPolicySource.protocol_messages joint selected protocol before.2 actual called
    change (update selected protocol actual.1 before.1.1).forwarded = messages selected actual.2
    simp only [update]
    rw [factual]
    exact congrArg (fun list => list ++ (RegistrationNativeIdentityCensorPolicySource.newMessage selected protocol actual.1).toList) prior
  · by_cases eligible : before.1.1.target = none ∧ message ∉ before.1.1.forwarded
    · simp only [execute, simulateQ_spec_query, handler, choose, StateT.run, eligible, simulateQ_pure] at reached
      cases reached
      exact prior
    · simp only [execute, simulateQ_spec_query, handler, choose, StateT.run, eligible, ite_false, simulateQ_pure] at reached
      cases reached
      exact prior
  · simp only [execute, simulateQ_spec_query, handler, StateT.run_pure, simulateQ_pure,
      mem_support_pure_iff] at reached
    cases reached
    exact prior
  · simp only [execute, simulateQ_spec_query, handler, StateT.run, simulateQ_map, map_apply,
      coins_apply, Functor.map_map, support_map] at reached
    obtain ⟨actual, _called, rfl⟩ := reached
    exact prior

private theorem execute_bind {B : Type} (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (work : OracleComp Spec Value) (next : Value → OracleComp Spec B) (before : Public × SourceState) :
    execute joint selected (work >>= next) before = (do
      let middle ← execute joint selected work before
      execute joint selected (next middle.1.1) (middle.1.2, middle.2)) := by
  simp only [execute, simulateQ_bind, StateT.run_bind]

/-- The entire adaptive public compiler derives its genuine source-history alignment from actual replies, including optional failures and independent hash coins. -/
theorem program_history (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (work : OracleComp Spec Value)
    (before : Public × SourceState) (prior : Aligned selected before) (result : (Value × Public) × SourceState)
    (reached : result ∈ support (execute joint selected work before)) :
    Aligned selected (result.1.2, result.2) := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [execute, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind request next ih =>
    rw [execute_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1.1 (middle.1.2, middle.2) (query_history joint selected request before prior middle called) result continued

/-- Initialized genuine oracle history has exactly the executable forwarding log, with no final freshness premise. -/
theorem initialized_history (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (work : OracleComp Spec Value)
    (hash : State Key) (result : (Value × Public) × SourceState)
    (reached : result ∈ support (execute joint selected work (({}, hash), PqxdhDynamicIdentityPool.initialState))) :
    Aligned selected (result.1.2, result.2) :=
  program_history joint selected work (({}, hash), PqxdhDynamicIdentityPool.initialState) rfl result reached

/-- The executable choice succeeds exactly before selection on a message absent from the genuine service history. History equality is derived by the initialized execution theorem above. -/
theorem choice (selected : Nat) (message : Pqxdh.Bytes) (before : Public × SourceState) (prior : Aligned selected before) :
    (choose message before.1.1).1 = true ↔ before.1.1.target = none ∧ message ∉ messages selected before.2 := by
  change before.1.1.forwarded = messages selected before.2 at prior
  rw [← prior]
  by_cases eligible : before.1.1.target = none ∧ message ∉ before.1.1.forwarded
  · simp [choose, eligible]
  · simp [choose, eligible]

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.query_after_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.query_after_some
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.query_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.query_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.program_after_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.program_after_some

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.query_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.query_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.program_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.program_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.initialized_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.initialized_history

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.choice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy.choice
