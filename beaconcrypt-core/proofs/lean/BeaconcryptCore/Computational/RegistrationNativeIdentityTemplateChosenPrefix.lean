-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix

/-! Before the fixed public bundle position the actual marker tree has no selection query. The public successful-reply policy and the ordinary executable therefore retain every original protocol call, while independent hash draws remain outside the source audit. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityChosenPublicRouter (Auxiliary)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplateChosenSuffix (executable ordinary realize Permitted)
variable {count : Nat} {A : Type}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

def Allowed : Spec.Domain → Prop
  | .inl (.inl (.inr _)) => False
  | _ => True

/-- Without a selection request every actual optional reply and independent hash draw preserves the absent public target. -/
theorem query_none (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (request : Spec.Domain) (before : Public × Auxiliary count)
    (held : before.1.1.target = none) (allowed : Allowed request) (result : Spec.Range request × (Public × Auxiliary count))
    (reached : result ∈ support ((executable joint target others identity request).run before)) :
    result.2.1.1.target = none := by
  rcases before with ⟨⟨policy, ⟨cache, journal⟩⟩, auxiliary⟩
  unfold executable at reached
  rw [QueryImpl.Stateful.link_impl_apply_run] at reached
  rcases request with ((protocol | selection) | scanned) | described
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, simulateQ_map,
      simulateQ_spec_query, bind_pure_comp, map_apply,
      RegistrationNativeIdentityTemplateChosenSuffix.external, Functor.map_map, support_map] at reached
    obtain ⟨actual, _called, rfl⟩ := reached
    exact held
  · exact False.elim allowed
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, StateT.run_pure, simulateQ_pure, map_pure,
      support_pure, Set.mem_singleton_iff] at reached
    cases reached
    exact held
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, simulateQ_map, map_apply,
      Functor.map_map, support_map] at reached
    obtain ⟨actual, _called, rfl⟩ := reached
    exact held

/-- The complete unselected public prefix has the exact ordinary weak-EUF executable interpretation. No original signing call or failed optional reply is suppressed. -/
theorem program (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (placeholder : Ed25519Signature) (work : OracleComp Spec A)
    (before : Public × Auxiliary count) (held : before.1.1.target = none) (allowed : work.AllQueriesSatisfy Allowed) :
    Prod.map id realize <$> (simulateQ (executable joint target others identity) work).run before =
      (simulateQ (ordinary joint target others identity placeholder) work).run (realize before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    have permitted : Permitted target before.1.1 request := by
      rcases request with ((protocol | selection) | scanned) | described
      · intro selected selectedEq
        rw [held] at selectedEq
        cases selectedEq
      all_goals trivial
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← RegistrationNativeIdentityTemplateChosenSuffix.query joint target others identity placeholder request before permitted]
    rw [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 result.2 (query_none joint target others identity request before held first result reached) (later result.1)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix.query_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix.query_none

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenPrefix.program
