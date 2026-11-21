-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateLateIdentity
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy

/-! The actual public-key registry commutes with the public template compiler by swapping the two bookkeeping states. Protocol replies are unchanged; symbolic hash coins never create a registry entry. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec coins)
open RegistrationNativeIdentityTemplatePolicy (Public)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry)
variable {A : Type}

private theorem coins_record (work : ProbComp A) (before : Registry) :
    (simulateQ RegistrationNativeIdentityTemplatePublicRegistry.record (simulateQ coins work)).run before =
      (fun answer => (answer,before)) <$> simulateQ coins work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
      change (do
        let answer ← (PublicSpec.query (.inr query) : OracleComp PublicSpec _)
        (simulateQ RegistrationNativeIdentityTemplatePublicRegistry.record (simulateQ coins (next answer))).run before) = _
      rw [map_bind]
      exact bind_congr (fun answer => ih answer before)

private theorem coins_apply (work : ProbComp A) (before : Registry) :
    (simulateQ RegistrationNativeIdentityTemplatePublicRegistry.record (simulateQ coins work)) before =
      (fun answer => (answer,before)) <$> simulateQ coins work := coins_record work before

private theorem map_apply {State X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT State m X) (before : State) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

/-- The literal registry observer and template-policy compiler commute without a source or key-table premise. -/
theorem query (selected : Nat) (request : Spec.Domain) (publicBefore : Public) (registry : Registry) :
    Prod.map id Prod.swap <$>
      (QueryImpl.Stateful.link (RegistrationNativeIdentityTemplatePolicy.handler selected)
        RegistrationNativeIdentityTemplatePublicRegistry.record request).run (publicBefore,registry) =
      (QueryImpl.Stateful.link RegistrationNativeIdentityTemplateLateIdentity.record
        (RegistrationNativeIdentityTemplatePolicy.handler selected) request).run (registry,publicBefore) := by
  rw [QueryImpl.Stateful.link_impl_apply_run,QueryImpl.Stateful.link_impl_apply_run]
  simp only [QueryImpl.Stateful.Frame.prod]
  rcases request with ((protocol | message) | scan) | described
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler,RegistrationNativeIdentityTemplateLateIdentity.record,
      simulateQ_spec_query,StateT.run,bind_pure_comp,
      simulateQ_map,Functor.map_map,Prod.map_def,id_eq,
      RegistrationNativeIdentityTemplateLateIdentity.note]
    rfl
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler,RegistrationNativeIdentityTemplateLateIdentity.record,
      simulateQ_pure,StateT.run,bind_pure_comp,
      RegistrationNativeIdentityTemplateLateIdentity.note,Prod.map_def,id_eq]
    rfl
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler,RegistrationNativeIdentityTemplateLateIdentity.record,
      StateT.run,bind_pure_comp,RegistrationNativeIdentityTemplateLateIdentity.note,Prod.map_def,id_eq]
    rfl
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler,RegistrationNativeIdentityTemplateLateIdentity.record,
      simulateQ_spec_query,simulateQ_map,StateT.run,bind_pure_comp,
      RegistrationNativeIdentityTemplateLateIdentity.note,map_apply,Functor.map_map]
    rw [coins_apply]
    simp only [Functor.map_map,Prod.map_def,id_eq]
    rfl

/-- The state swap holds for every adaptive marker-spec client, retaining every original public reply and both final bookkeeping states. -/
theorem program (selected : Nat) (work : OracleComp Spec A) (publicBefore : Public) (registry : Registry) :
    Prod.map id Prod.swap <$>
      (simulateQ (QueryImpl.Stateful.link (RegistrationNativeIdentityTemplatePolicy.handler selected)
        RegistrationNativeIdentityTemplatePublicRegistry.record) work).run (publicBefore,registry) =
      (simulateQ (QueryImpl.Stateful.link RegistrationNativeIdentityTemplateLateIdentity.record
        (RegistrationNativeIdentityTemplatePolicy.handler selected)) work).run (registry,publicBefore) := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.swap
    (fun request before => query selected request before.1 before.2) work (publicBefore,registry)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler.program
