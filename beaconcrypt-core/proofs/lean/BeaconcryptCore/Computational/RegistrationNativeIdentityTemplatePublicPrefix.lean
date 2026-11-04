-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicCtx
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedNoSelect

/-! The actual warm physical prefix and its successful-reply policy compile to the public symbolic table with the genuine source pool kept external. No selected private signature or physical hidden address enters the client state. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix
open PqxdhJointIdentity (Primitives)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPolicySource (handler observe)
open RegistrationNativeIdentityTemplatePolicy (Public)
open PqxdhDynamicIdentityPool (SourceState)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev New := RegistrationNativeIdentityTemplateCensorRecognition.Spec
variable {A : Type}

def Allowed : Old.Domain → Prop
  | .inl (.inl (.inl (.inl _))) => True
  | .inl (.inl (.inl (.inr _))) => False
  | .inl (.inl (.inr _)) => True
  | .inl (.inr described) => described.input.isSome = true
  | .inr _ => False

noncomputable def project (before : Policy × RegistrationNativeIdentityCensorSource.State) : Public × SourceState :=
  ((before.1, RegistrationNativeIdentityTemplatePublicCtx.install before.2.hash), before.2.pool)

noncomputable def publicSource (joint : Primitives) (selected : Nat) :
    QueryImpl New (StateT (Public × SourceState) ProbComp) :=
  QueryImpl.Stateful.link (RegistrationNativeIdentityTemplatePolicy.handler selected)
    (RegistrationNativeIdentityTemplateProtocol.source joint)

private theorem public_run (joint : Primitives) (selected : Nat) (request : New.Domain) (before : Public × SourceState) :
    publicSource joint selected request before =
      (QueryImpl.Stateful.Frame.prod Public SourceState).linkReshape before <$>
        (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
          ((RegistrationNativeIdentityTemplatePolicy.handler selected request).run before.1)).run before.2 :=
  QueryImpl.Stateful.link_impl_apply_run _ _ request before.1 before.2

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem coins (joint : Primitives) (work : ProbComp A) (before : SourceState) :
    (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
      (simulateQ RegistrationNativeIdentityTemplateProtocol.coins work)) before =
      (fun value => (value, before)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin current
  change (do let answer ← unifSpec.query coin; pure (answer, current) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- The actual physical source prefix, including every failed optional service, has the public policy/table compiler interpretation with its full genuine source audit outside the compiler. -/
theorem query (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature) (request : Old.Domain)
    (allowed : Allowed request) (before : Policy × RegistrationNativeIdentityCensorSource.State) :
    Prod.map id project <$> (handler joint selected placeholder request).run before =
      (simulateQ (publicSource joint selected) (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder request)).run (project before) := by
  rcases before with ⟨policy, privateState⟩
  rcases request with (((protocol | selection) | scanned) | described) | marker
  · simp only [handler, StateT.run, RegistrationNativeIdentityCensorSource.censored,
      RegistrationNativeIdentityCensorSource.implementation, RegistrationNativeIdentityCensorSource.protocol,
      observe, RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_spec_query,
      project, public_run,
      RegistrationNativeIdentityTemplatePolicy.handler, simulateQ_map, simulateQ_spec_query,
      map_apply, RegistrationNativeIdentityTemplateProtocol.source, bind_pure_comp, Functor.map_map,
      QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, Prod.map_def, id_eq]
    rfl
  · exact False.elim allowed
  · simp only [handler, StateT.run, RegistrationNativeIdentityCensorSource.censored,
      RegistrationNativeIdentityCensorSource.implementation, observe,
      RegistrationNativeIdentityCensorTargetSync.targetAfter,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_spec_query,
      project, public_run,
      RegistrationNativeIdentityTemplatePolicy.handler, QueryImpl.Stateful.Frame.prod, Prod.map_def, id_eq]
    rfl
  · cases found : described.input with
    | none => simp only [Allowed, found, Option.isSome_none, Bool.false_eq_true] at allowed
    | some input =>
      have physical := RegistrationNativeIdentityTemplatePublicCtx.query input privateState.hash
      have observed := congrArg (Functor.map (fun result => (result.1, ((policy, result.2), privateState.pool)))) physical
      simp only [handler, StateT.run, RegistrationNativeIdentityCensorSource.censored,
        RegistrationNativeIdentityCensorSource.implementation, RegistrationNativeIdentityCensorSource.physical,
        observe, RegistrationNativeIdentityCensorTargetSync.targetAfter,
        RegistrationNativeIdentityTemplateCensorRecognition.erase, found, simulateQ_spec_query,
        project, public_run,
        RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, simulateQ_map, map_apply,
        coins, Functor.map_map, QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
        PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, Prod.map_def, id_eq] at observed ⊢
      rw [observed]
      rw [found, Option.getD_some]
  · exact False.elim allowed

/-- First selection itself has the public policy's exact computable reply and poststate. The preselection history relation is the already derived actual optional-reply observer invariant. -/
theorem selection (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes)
    (before : Policy × RegistrationNativeIdentityCensorSource.State)
    (prior : RegistrationNativeIdentityCensorPolicySource.Aligned selected before) :
    Prod.map id project <$>
      (handler joint selected placeholder (.inl (.inl (.inl (.inr message))))).run before =
      (publicSource joint selected (.inl (.inl (.inr message)))).run (project before) := by
  have actual := RegistrationNativeIdentityCensorPolicySource.select_source selected message before prior
  simp only [StateT.run] at actual
  simp only [handler, RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
    StateT.run, actual, map_pure, project, public_run, RegistrationNativeIdentityTemplatePolicy.handler,
    simulateQ_pure, map_pure, observe, RegistrationNativeIdentityCensorTargetSync.targetAfter]
  by_cases eligible : before.1.target = none ∧ message ∉ before.1.forwarded
  all_goals simp [RegistrationNativeIdentityCensorPolicySource.choose, project, pure_apply,
    RegistrationNativeIdentityCensorPolicySource.afterSelection, eligible,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, id_eq]

/-- The complete actual physical prefix retains its full returned value, warm cache costs, successful-reply policy and genuine source pool in the public template language. -/
theorem program (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Old A)
    (allowed : work.AllQueriesSatisfy Allowed) (before : Policy × RegistrationNativeIdentityCensorSource.State) :
    Prod.map id project <$> (simulateQ (handler joint selected placeholder) work).run before =
      (simulateQ (publicSource joint selected) (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work)).run (project before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query joint selected placeholder request first before]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)

private theorem record_query (request : RegistrationNativeIdentityCensorPrefix.SourceSpec.Domain) (mode : Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      ((RegistrationNativeIdentityCensorPrefix.record request).run mode)).AllQueriesSatisfy Allowed := by
  cases request <;>
    simp only [RegistrationNativeIdentityCensorPrefix.record, StateT.run, simulateQ_bind, simulateQ_pure,
      RegistrationNativeIdentityCensorPrefix.embed, RegistrationNativeIdentityCensorCompiler.protocol,
      simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed] <;>
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨by first | trivial, fun _ => allQueriesSatisfy_pure _ _⟩

private theorem record_program (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec A) (mode : Mode) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      ((simulateQ RegistrationNativeIdentityCensorPrefix.record work).run mode)).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (record_query request mode) (fun result => ih result.1 result.2)

/-- Actual unarmed lowering discharges the prefix scope internally and exposes the whole current frontend/platform value unchanged to the public template compiler. -/
theorem unarmed (joint : Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorPrefix.SourceSpec A) (mode : Mode)
    (prior : RegistrationNativeIdentityCensorPrefix.Unarmed mode) (before : Policy × RegistrationNativeIdentityCensorSource.State) :
    Prod.map id project <$> (simulateQ (handler joint selected placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before =
      (simulateQ (publicSource joint selected)
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
          ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run (project before) := by
  rw [RegistrationNativeIdentityCensorOperationalPrefix.program selected placeholder work mode prior]
  exact program joint selected placeholder _ (record_program work mode) before

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.unarmed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.unarmed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicPrefix.selection
