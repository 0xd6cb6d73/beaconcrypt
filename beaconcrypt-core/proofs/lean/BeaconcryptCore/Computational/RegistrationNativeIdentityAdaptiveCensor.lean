-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensor

/-! The suppressed message may be selected adaptively after independent protocol sampling and earlier ordinary joint-service calls. Selection succeeds only before its first forwarded signing request; it is fixed thereafter. The client retains only public messages, a placeholder and the selected message. The challenged identity seed and its signatures remain in the ordinary primitive interpreter. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor
open PqxdhJointIdentity (AdversarySpec IdentitySeed History signedMessages)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}

structure Policy where
  target : Option Pqxdh.Bytes := none
  forwarded : List Pqxdh.Bytes := []
  deriving Inhabited

abbrev Spec := AdversarySpec + (Pqxdh.Bytes →ₒ Bool)

def select (message : Pqxdh.Bytes) : OracleComp Spec Bool := Spec.query (.inr message)
def ordinary : QueryImpl AdversarySpec (OracleComp Spec) := fun query => Spec.query (.inl query)

/-- Retrying an already selected message returns the same client placeholder and makes no signing-oracle request. -/
def implementation (placeholder : Ed25519Signature) : QueryImpl Spec (StateT Policy (OracleComp AdversarySpec))
  | .inl (.inl query) => StateT.lift (AdversarySpec.query (.inl query) : OracleComp AdversarySpec _)
  | .inl (.inr (.staticDh peer)) => StateT.lift (AdversarySpec.query (.inr (.staticDh peer)) : OracleComp AdversarySpec _)
  | .inl (.inr (.sign message)) => fun before =>
      if before.target = some message then pure (placeholder, before)
      else do
        let signature ← AdversarySpec.query (.inr (.sign message))
        pure (signature, { before with forwarded := before.forwarded ++ [message] })
  | .inr message => fun before =>
      if before.target = none ∧ message ∉ before.forwarded then pure (true, { before with target := some message })
      else pure (false, before)

def Safe (policy : Policy) (history : History) : Prop :=
  policy.forwarded = signedMessages history ∧
    ∀ target, policy.target = some target → target ∉ signedMessages history

noncomputable def execute (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (placeholder : Ed25519Signature) (work : OracleComp Spec Value) (before : Policy) (history : History) :
    ProbComp ((Value × Policy) × History) :=
  (simulateQ (PqxdhJointIdentity.jointImpl primitives seed)
    ((simulateQ (implementation placeholder) work).run before)).run history

private theorem step_safe (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (placeholder : Ed25519Signature) (query : Spec.Domain) (before : Policy) (history : History)
    (prior : Safe before history) (result : (Spec.Range query × Policy) × History)
    (reached : result ∈ support (execute primitives seed placeholder (Spec.query query) before history)) :
    Safe result.1.2 result.2 := by
  cases query with
  | inr message =>
    by_cases selected : before.target = none ∧ message ∉ before.forwarded
    · simp only [execute, simulateQ_spec_query, implementation, StateT.run, selected] at reached
      cases reached
      exact ⟨prior.1, by intro target equal; cases Option.some.inj equal; simpa only [← prior.1] using selected.2⟩
    · simp only [execute, simulateQ_spec_query, implementation, StateT.run, selected, ite_false, simulateQ_pure] at reached
      cases reached
      exact prior
  | inl query => cases query with
    | inl query =>
      change result ∈ support (do
        let reply ← (unifSpec.query query : ProbComp _)
        pure ((reply, before), history)) at reached
      rw [bind_pure_comp, support_map] at reached
      obtain ⟨reply, _possible, same⟩ := reached
      cases same
      exact prior
    | inr query => cases query with
      | staticDh peer =>
        simp only [execute, simulateQ_spec_query, implementation, StateT.run] at reached
        cases reached
        simpa only [Safe, signedMessages, PqxdhJointIdentity.requestEvent,
          List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil] using prior
      | sign message =>
        by_cases suppressed : before.target = some message
        · simp only [execute, simulateQ_spec_query, implementation, StateT.run, suppressed] at reached
          cases reached
          exact prior
        · simp only [execute, simulateQ_spec_query, implementation, StateT.run, suppressed, ite_false,
            simulateQ_bind, simulateQ_pure] at reached
          cases reached
          constructor
          · simp only [signedMessages, PqxdhJointIdentity.requestEvent, List.filterMap_append,
              List.filterMap_cons, List.filterMap_nil, prior.1]
          · intro target chosen
            simp only [signedMessages, PqxdhJointIdentity.requestEvent, List.filterMap_append,
              List.filterMap_cons, List.filterMap_nil, List.mem_append, List.mem_singleton]
            intro present
            exact present.elim (prior.2 target chosen) (fun equal => suppressed (chosen.trans (congrArg some equal)))

private theorem execute_bind {Next : Type} (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (placeholder : Ed25519Signature) (work : OracleComp Spec Value) (next : Value → OracleComp Spec Next)
    (before : Policy) (history : History) :
    execute primitives seed placeholder (work >>= next) before history = (do
      let result ← execute primitives seed placeholder work before history
      execute primitives seed placeholder (next result.1.1) result.1.2 result.2) := by
  simp only [execute, simulateQ_bind, StateT.run_bind]

/-- Adaptive selection is fresh in the actual ordinary challenger history on every reached branch, including prior signatures and repeated censored attempts. -/
theorem safe_run (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (placeholder : Ed25519Signature) (work : OracleComp Spec Value) (before : Policy) (history : History)
    (prior : Safe before history) (result : (Value × Policy) × History)
    (reached : result ∈ support (execute primitives seed placeholder work before history)) :
    Safe result.1.2 result.2 := by
  induction work using OracleComp.inductionOn generalizing before history result with
  | pure value =>
    simp only [execute, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind query next ih =>
    rw [execute_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, called, continued⟩ := reached
    exact ih middle.1.1 middle.1.2 middle.2
      (step_safe primitives seed placeholder query before history prior middle called) result continued

/-- The empty actual signer starts with no forwarded message; no final-history freshness premise is supplied. -/
theorem initialized (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (placeholder : Ed25519Signature) (work : OracleComp Spec Value) (result : (Value × Policy) × History)
    (reached : result ∈ support (execute primitives seed placeholder work {} [])) :
    ∀ target, result.1.2.target = some target → target ∉ signedMessages result.2 := by
  apply (safe_run primitives seed placeholder work {} [] ?_ result reached).2
  exact ⟨rfl, by intro target selected; cases selected⟩

def recognized (primitives : PqxdhJointIdentity.Primitives) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (candidate : Option Ed25519Signature) (policy : Policy) : Bool :=
  policy.target.any fun target => candidate.any (primitives.verify publicIdentity.ed25519 target)

/-- The primitive adversary learns its target through the public adaptive selection capability. Neither its program nor its policy captures the challenged seed or canonical signature. -/
def reduction (placeholder : Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery)
    (work : PqxdhJointIdentity.PublicIdentity → OracleComp Spec (Option Ed25519Signature))
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) : OracleComp AdversarySpec PqxdhJointIdentity.Forgery := do
  let result ← (simulateQ (implementation placeholder) (work publicIdentity)).run {}
  pure ⟨result.2.target.getD fallback.message, result.1.getD fallback.signature⟩

noncomputable def observed (primitives : PqxdhJointIdentity.Primitives) (placeholder : Ed25519Signature)
    (work : PqxdhJointIdentity.PublicIdentity → OracleComp Spec (Option Ed25519Signature)) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let result ← execute primitives seed placeholder (work (primitives.publicKeys seed)) {} []
  pure (recognized primitives (primitives.publicKeys seed) result.1.1 result.1.2)

private theorem captured (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (placeholder : Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery)
    (work : OracleComp Spec (Option Ed25519Signature))
    (result : (Option Ed25519Signature × Policy) × History)
    (reached : result ∈ support (execute primitives seed placeholder work {} []))
    (valid : recognized primitives (primitives.publicKeys seed) result.1.1 result.1.2 = true) :
    PqxdhJointIdentity.wins primitives (primitives.publicKeys seed)
      ⟨result.1.2.target.getD fallback.message, result.1.1.getD fallback.signature⟩ result.2 = true := by
  have fresh := initialized primitives seed placeholder work result reached
  rcases result with ⟨⟨candidate, policy⟩, history⟩
  cases target : policy.target with
  | none => simp only [recognized, target, Option.any_none, Bool.false_eq_true] at valid
  | some message =>
    have absent := fresh message target
    cases candidate with
    | none => simp only [recognized, target, Option.any_some, Option.any_none, Bool.false_eq_true] at valid
    | some signature =>
      simpa only [recognized, target, Option.any_some, PqxdhJointIdentity.wins, Option.getD_some,
        absent, decide_false, Bool.not_false, Bool.and_true] using valid

/-- One ordinary joint Ed/static-DH weak-EUF advantage bounds recognition of an adaptively selected unpublished message. Freshness follows from the actual oracle log and selection/censor execution. -/
theorem recognition_bound (primitives : PqxdhJointIdentity.Primitives)
    (placeholder : Ed25519Signature) (fallback : PqxdhJointIdentity.Forgery)
    (work : PqxdhJointIdentity.PublicIdentity → OracleComp Spec (Option Ed25519Signature)) :
    Pr{let accepted ← observed primitives placeholder work}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives (reduction placeholder fallback work) := by
  unfold observed execute PqxdhJointIdentity.advantage PqxdhJointIdentity.game PqxdhJointIdentity.run reduction
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro seed _
  apply prEvent_bind_mono_of_forall_le_of_support
  intro result reached
  by_cases valid : recognized primitives (primitives.publicKeys seed) result.1.1 result.1.2 = true
  · have wins := captured primitives seed placeholder fallback _ result reached valid
    simp only [prEvent_pure, valid, wins, ite_true]
    exact le_rfl
  · simp only [prEvent_pure, valid, Bool.false_eq_true, ite_false, zero_le]

end BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor.safe_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor.safe_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor.initialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor.recognition_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveCensor.recognition_bound
