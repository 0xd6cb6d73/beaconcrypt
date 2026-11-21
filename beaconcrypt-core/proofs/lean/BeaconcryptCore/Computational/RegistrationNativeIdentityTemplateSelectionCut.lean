-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix

/-! Factoring a public program immediately before its first selector exposes a common executable prefix and the literal reply-dependent continuation. The transformer makes no private acceptance or source-history test. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
variable {A : Type}

inductive Cut (A : Type) where
  | returned : A → Cut A
  | selected : Pqxdh.Bytes → (Bool → OracleComp Spec A) → Cut A

/-- The query is retained together with its original continuation, before asking for its actual public Boolean reply. -/
def stop (work : OracleComp Spec A) : OracleComp Spec (Cut A) :=
  OracleComp.construct (C := fun _ => OracleComp Spec (Cut A))
    (fun value => pure (.returned value))
    (fun query next continued => match query with
      | .inl (.inl (.inr message)) => pure (.selected message next)
      | query => do let reply ← Spec.query query; continued reply) work

def resume : Cut A → OracleComp Spec A
  | .returned value => pure value
  | .selected message next => Spec.query (.inl (.inl (.inr message))) >>= next

private theorem stop_pure (value : A) : stop (pure value) = pure (.returned value) := rfl

private theorem stop_query (query : Spec.Domain) (next : Spec.Range query → OracleComp Spec A) :
    stop (Spec.query query >>= next) =
      (match query with
      | .inl (.inl (.inr message)) => pure (.selected message next)
      | query => do let reply ← Spec.query query; stop (next reply)) := by
  rcases query with ((protocol | selection) | scanned) | described <;> rfl

/-- Joining the common prefix, actual selector reply and literal original continuation recovers the complete program exactly. -/
theorem factor (work : OracleComp Spec A) : (stop work >>= resume) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rw [stop_pure, pure_bind]; rfl
  | query_bind query next ih =>
    rw [stop_query]
    rcases query with ((protocol | selection) | scanned) | described
    · simp only [bind_assoc, ih]
    · simp only [pure_bind, resume]
    · simp only [bind_assoc, ih]
    · simp only [bind_assoc, ih]

/-- The common prefix cannot consult a selector under any oracle reply, including prefixes which never select. -/
theorem no_selection (work : OracleComp Spec A) :
    (stop work).AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenPrefix.Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => rw [stop_pure]; exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [stop_query]
    rcases query with ((protocol | selection) | scanned) | described
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩
    · exact allQueriesSatisfy_pure _ _
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

/-- Any actual stateful interpreter executes the same first public prefix and then the retained original continuation; all interpreter state remains attached to that same reached cut. -/
theorem execution {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl Spec (StateT S m)) (work : OracleComp Spec A) (before : S) :
    (simulateQ handler work).run before = (do
      let cut ← (simulateQ handler (stop work)).run before
      (simulateQ handler (resume cut.1)).run cut.2) := by
  have law := congrArg (fun code => (simulateQ handler code).run before) (factor work)
  simpa only [simulateQ_bind, StateT.run_bind] using law.symm

/-- The actual public-table and ordinary challenged-key clients have a common entire first-selection prefix, with no supplied prefix-admission premise. -/
theorem prefix_equal {count : Nat} (joint : PqxdhJointIdentity.Primitives) (target : Fin (count+1))
    (others : Fin count → PqxdhJointIdentity.IdentitySeed) (identity : PqxdhJointIdentity.PublicIdentity)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp Spec A)
    (before : RegistrationNativeIdentityTemplatePolicy.Public × RegistrationNativeIdentityChosenPublicRouter.Auxiliary count)
    (held : before.1.1.target = none) :
    Prod.map id RegistrationNativeIdentityTemplateChosenSuffix.realize <$>
      (simulateQ (RegistrationNativeIdentityTemplateChosenSuffix.executable joint target others identity) (stop work)).run before =
      (simulateQ (RegistrationNativeIdentityTemplateChosenSuffix.ordinary joint target others identity placeholder) (stop work)).run
        (RegistrationNativeIdentityTemplateChosenSuffix.realize before) :=
  RegistrationNativeIdentityTemplateChosenPrefix.program joint target others identity placeholder (stop work) before held (no_selection work)

namespace Original
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec

inductive Cut (A : Type) where
  | returned : A → Cut A
  | selected : Pqxdh.Bytes → (Bool → OracleComp Old A) → Cut A

def stop (work : OracleComp Old A) : OracleComp Old (Cut A) :=
  OracleComp.construct (C := fun _ => OracleComp Old (Cut A))
    (fun value => pure (.returned value))
    (fun query next continued => match query with
      | .inl (.inl (.inl (.inr message))) => pure (.selected message next)
      | query => do let reply ← Old.query query; continued reply) work

def resume : Cut A → OracleComp Old A
  | .returned value => pure value
  | .selected message next => Old.query (.inl (.inl (.inl (.inr message)))) >>= next

private theorem stop_pure (value : A) : stop (pure value) = pure (.returned value) := rfl

theorem step (query : Old.Domain) (next : Old.Range query → OracleComp Old A) :
    stop (Old.query query >>= next) =
      (match query with
      | .inl (.inl (.inl (.inr message))) => pure (.selected message next)
      | query => do let reply ← Old.query query; stop (next reply)) := by
  rcases query with (((protocol | selection) | scanned) | described) | marker <;> rfl

/-- The original private marker program has the same exact first-selector factorization, retaining its literal canonical-omission continuation for the source proof. -/
theorem factor (work : OracleComp Old A) : (stop work >>= resume) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rw [stop_pure, pure_bind]; rfl
  | query_bind query next ih =>
    rw [step]
    rcases query with (((protocol | selection) | scanned) | described) | marker
    · simp only [bind_assoc, ih]
    · simp only [pure_bind, resume]
    · simp only [bind_assoc, ih]
    · simp only [bind_assoc, ih]
    · simp only [bind_assoc, ih]

/-- Stopping distributes through sequencing until the selector; a suspended continuation retains the entire original suffix. -/
theorem bind {B : Type} (work : OracleComp Old A) (next : A → OracleComp Old B) :
    stop (work >>= next) = (do
      let cut ← stop work
      match cut with
      | .returned value => stop (next value)
      | .selected message continued => pure (.selected message (fun reply => continued reply >>= next))) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [pure_bind, stop_pure]
  | query_bind query rest ih =>
    simp only [bind_assoc, step]
    rcases query with (((protocol | selection) | scanned) | described) | marker
    · simp only [bind_assoc, ih]
    · simp only [pure_bind]
      rfl
    · simp only [bind_assoc, ih]
    · simp only [bind_assoc, ih]
    · simp only [bind_assoc, ih]

def erased (placeholder : PqxdhEd25519EufCma.Ed25519Signature) : Cut A → RegistrationNativeIdentityTemplateSelectionCut.Cut A
  | .returned value => .returned value
  | .selected message next => .selected message (fun reply =>
      simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (next reply))

private theorem hash_step (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (described : RegistrationNativeIdentityTemplateCensorRecognition.HashInput)
    (next : (CtxRomAuth.CtxDigest × Nat) → OracleComp Old A)
    (continued : ∀ reply, erased placeholder <$> simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (stop (next reply)) =
      RegistrationNativeIdentityTemplateSelectionCut.stop (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (next reply))) :
    erased placeholder <$> ((Spec.query (.inr described) : OracleComp Spec _) >>= fun reply =>
      simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (stop (next reply))) =
    RegistrationNativeIdentityTemplateSelectionCut.stop ((Spec.query (.inr described) : OracleComp Spec _) >>= fun reply =>
      simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (next reply)) := by
  rw [map_bind, RegistrationNativeIdentityTemplateSelectionCut.stop_query]
  exact bind_congr continued

/-- Literal marker erasure commutes with the first-selector cut, retaining the original Boolean continuation and every earlier public query. -/
theorem erase_stop (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp Old A) :
    erased placeholder <$> simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (stop work) =
      RegistrationNativeIdentityTemplateSelectionCut.stop
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rw [stop_pure, simulateQ_pure, map_pure, erased, simulateQ_pure]; rfl
  | query_bind query next ih =>
    rw [step]
    rcases query with (((protocol | selection) | scanned) | described) | marker
    · simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase,
        map_bind, ih]
      rfl
    · simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase,
        simulateQ_pure, map_pure, erased]
      rfl
    · simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase,
        map_bind, ih]
      rfl
    · simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase,
        map_bind, ih]
      rfl
    · cases marker with
      | omitted handle message =>
        simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase]
        convert ih (some placeholder) using 1 <;> rfl
      | template handle message leading trailing =>
        simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateCensorRecognition.erase]
        convert hash_step placeholder ⟨message, .inr (leading, trailing)⟩ next ih using 1 <;> rfl

/-- The actual private interpreter keeps its full state at the same original first-selector cut. -/
theorem execution {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl Old (StateT S m)) (work : OracleComp Old A) (before : S) :
    (simulateQ handler work).run before = (do
      let cut ← (simulateQ handler (stop work)).run before
      (simulateQ handler (resume cut.1)).run cut.2) := by
  have law := congrArg (fun code => (simulateQ handler code).run before) (factor work)
  simpa only [simulateQ_bind, StateT.run_bind] using law.symm

end Original

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.factor' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.no_selection' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.no_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.execution' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.execution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.prefix_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.prefix_equal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.factor' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.erase_stop' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.erase_stop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.execution' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.execution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut.Original.bind
