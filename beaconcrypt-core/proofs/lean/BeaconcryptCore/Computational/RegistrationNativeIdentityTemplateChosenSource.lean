-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix

/-! The chosen public compiler's independent hash coins remain outside the actual reserved-family protocol audit. The complete target/other-key histories are recombined only by the private challenger interpretation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity History jointImpl)
open PqxdhJointIdentityFreshness (GlobalState)
open PqxdhJointIdentityFamily (familyPublic)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
open RegistrationNativeIdentityChosenPublicRouter (Auxiliary project)
open RegistrationNativeIdentityTemplateChosenSuffix (external)
variable {count : Nat} {A : Type}

def Allowed : PublicSpec.Domain → Prop
  | .inl query => RegistrationNativeIdentityMainNoRevealCore.Allowed query
  | .inr _ => True

def reserved (joint : Primitives) (seeds : Fin (count+1) → IdentitySeed) :
    QueryImpl PublicSpec (StateT (PqxdhDynamicIdentityRouting.PublicState × GlobalState (count+1)) ProbComp)
  | .inl query => RegistrationNativeIdentityPublicRouter.source joint seeds query
  | .inr query => StateT.lift (unifSpec.query query : ProbComp _)

/-- Genuine optional replies and the complete family audit have the same chosen-key interpretation; independent hash coins do not append a router or identity observation. -/
theorem query (joint : Primitives) (target : Fin (count+1)) (seed : IdentitySeed) (others : Fin count → IdentitySeed)
    (reveals : List (Fin (count+1))) (request : PublicSpec.Domain) (allowed : Allowed request)
    (before : Auxiliary count × History) :
    Prod.map id (project target reveals) <$>
      (QueryImpl.Stateful.link (external joint target others (joint.publicKeys seed)) (jointImpl joint seed) request).run before =
      (reserved joint (target.insertNth seed others) request).run (project target reveals before) := by
  rcases before with ⟨auxiliary, history⟩
  cases request with
  | inl protocol =>
    have coupled := RegistrationNativeIdentityChosenPublicRouter.query_source joint target seed others reveals protocol (auxiliary, history)
    have literal := RegistrationNativeIdentityPublicRouter.query_source joint (target.insertNth seed others) protocol allowed (project target reveals (auxiliary, history))
    simpa only [QueryImpl.Stateful.link_impl_apply_run, external, reserved] using coupled.trans literal
  | inr coin =>
    rw [QueryImpl.Stateful.link_impl_apply_run]
    simp only [external, RegistrationNativeIdentityTemplateChosenSuffix.primitiveCoins, StateT.run,
      Functor.map_map, reserved, QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, Prod.map_def, id_eq]
    rfl

/-- The entire public template program retains its literal optional replies, router state and genuine target/other-key histories under the ordinary challenger. -/
theorem program (joint : Primitives) (target : Fin (count+1)) (seed : IdentitySeed) (others : Fin count → IdentitySeed)
    (reveals : List (Fin (count+1))) (work : OracleComp PublicSpec A) (allowed : work.AllQueriesSatisfy Allowed)
    (before : Auxiliary count × History) :
    Prod.map id (project target reveals) <$>
      (simulateQ (QueryImpl.Stateful.link (external joint target others (joint.publicKeys seed)) (jointImpl joint seed)) work).run before =
      (simulateQ (reserved joint (target.insertNth seed others)) work).run (project target reveals before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query joint target seed others reveals request first before]
    rw [bind_map_left]
    exact bind_congr (fun result => ih result.1 (later result.1) result.2)

def TemplateAllowed : RegistrationNativeIdentityTemplateCensorRecognition.Spec.Domain → Prop
  | .inl (.inl (.inl query)) => RegistrationNativeIdentityMainNoRevealCore.Allowed query
  | _ => True

private theorem coins_safe (work : ProbComp A) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.coins work).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateProtocol.coins,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨trivial, ih⟩

private theorem template_query (selected : Nat) (request : RegistrationNativeIdentityTemplateCensorRecognition.Spec.Domain)
    (allowed : TemplateAllowed request) (before : RegistrationNativeIdentityTemplatePolicy.Public) :
    ((RegistrationNativeIdentityTemplatePolicy.handler selected request).run before).AllQueriesSatisfy Allowed := by
  rcases request with ((protocol | selection) | scanned) | described
  · change AllQueriesSatisfy ((PublicSpec.query (.inl protocol) : OracleComp PublicSpec _) >>= fun answer =>
        pure (answer, (RegistrationNativeIdentityCensorPolicySource.update selected protocol answer before.1, before.2))) Allowed
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr allowed) (fun _ => allQueriesSatisfy_pure _ _)
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _
  · exact RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ (coins_safe _)

/-- Actual compilation to the public successful-reply policy and symbolic cache preserves the source's structural no-reveal restriction. -/
theorem template_program (selected : Nat) (work : OracleComp RegistrationNativeIdentityTemplateCensorRecognition.Spec A)
    (allowed : work.AllQueriesSatisfy TemplateAllowed) (before : RegistrationNativeIdentityTemplatePolicy.Public) :
    ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run before).AllQueriesSatisfy Allowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (template_query selected request first before) (fun result => ih result.1 (later result.1) result.2)

/-- The actual public policy/cache compiler has the same complete reserved-family source interpretation, including the selected ordinary challenger history and every independent hash draw. -/
theorem template (joint : Primitives) (target : Fin (count+1)) (seed : IdentitySeed) (others : Fin count → IdentitySeed)
    (reveals : List (Fin (count+1))) (work : OracleComp RegistrationNativeIdentityTemplateCensorRecognition.Spec A)
    (allowed : work.AllQueriesSatisfy TemplateAllowed) (publicBefore : RegistrationNativeIdentityTemplatePolicy.Public)
    (before : Auxiliary count × History) :
    Prod.map id (project target reveals) <$>
      (simulateQ (QueryImpl.Stateful.link (external joint target others (joint.publicKeys seed)) (jointImpl joint seed))
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler target.val) work).run publicBefore)).run before =
      (simulateQ (reserved joint (target.insertNth seed others))
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler target.val) work).run publicBefore)).run (project target reveals before) :=
  program joint target seed others reveals _ (template_program target.val work allowed publicBefore) before

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.template_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.template_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.template' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource.template
