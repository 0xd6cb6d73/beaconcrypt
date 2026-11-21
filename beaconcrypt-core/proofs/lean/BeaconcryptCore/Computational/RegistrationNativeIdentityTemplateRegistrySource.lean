-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePublicRegistry
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistryCompiler
/-! The public create-reply registry has an exact joint source marginal. The generated seed table remains in the source interpreter while the observer contains public identities only. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource
open PqxdhJointIdentity (Primitives)
open PqxdhDynamicIdentityPool (SourceState)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
open RegistrationNativeIdentityTemplatePublicRegistry (Registry record keys)
variable {A : Type}

private theorem map_apply {State X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT State m X) (before : State) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem erase_query (joint : Primitives) (query : PublicSpec.Domain) (before : Registry × SourceState) :
    Prod.map id Prod.snd <$> (QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint) query).run before =
      (RegistrationNativeIdentityTemplateProtocol.source joint query).run before.2 := by
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [record,StateT.run,bind_pure_comp,simulateQ_map,simulateQ_spec_query,map_apply,Functor.map_map,
    QueryImpl.Stateful.Frame.prod,Prod.map_def,id_eq]
  exact id_map _

/-- Erasing only the public observer preserves the complete source result, pool and chronological audit. -/
theorem erasure (joint : Primitives) (work : OracleComp PublicSpec A) (before : Registry × SourceState) :
    Prod.map id Prod.snd <$>
      (simulateQ (QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint)) work).run before =
    (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd (erase_query joint) work before

def graph (joint : Primitives) (result : A × SourceState) : A × (Registry × SourceState) :=
  (result.1,(keys joint result.2,result.2))

/-- The reached public registry is exactly the public projection of the SAME final source rows, jointly with every client/local value and the full source audit. -/
theorem complete (joint : Primitives) (work : OracleComp PublicSpec A) (before : SourceState) :
    (simulateQ (QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint)) work).run
      (keys joint before,before) =
    graph joint <$> (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint) work).run before := by
  rw [←erasure joint work (keys joint before,before),Functor.map_map]
  conv_lhs => rw [←id_map ((simulateQ (QueryImpl.Stateful.link record (RegistrationNativeIdentityTemplateProtocol.source joint)) work).run
    (keys joint before,before))]
  rw [map_eq_bind_pure_comp,map_eq_bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result supported
  have aligned := RegistrationNativeIdentityTemplatePublicRegistry.source_program joint work (keys joint before,before) rfl result supported
  apply congrArg pure
  simpa only [graph,Prod.map_def,id_eq,Prod.eta] using congrArg (fun registry => (result.1,(registry,result.2.2))) aligned

/-- Public registry tracking may be moved through the actual template compiler and reconstructed from the SAME source rows, retaining every cache/policy/client coordinate. -/
theorem policy_complete (joint : Primitives) (selected : Nat)
    (work : OracleComp RegistrationNativeIdentityTemplateCensorRecognition.Spec A)
    (publicBefore : RegistrationNativeIdentityTemplatePolicy.Public) (before : SourceState) :
    (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
      ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
        ((simulateQ RegistrationNativeIdentityTemplateLateIdentity.record work).run (keys joint before))).run publicBefore)).run before =
    (fun result => (((result.1.1,keys joint result.2),result.1.2),result.2)) <$>
      (simulateQ (RegistrationNativeIdentityTemplateProtocol.source joint)
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run publicBefore)).run before := by
  have commuted := RegistrationNativeIdentityTemplateRegistryCompiler.program selected work publicBefore (keys joint before)
  have shaped := congrArg (Functor.map (fun result : A × (Registry × RegistrationNativeIdentityTemplatePolicy.Public) =>
    ((result.1,result.2.1),result.2.2))) commuted
  rw [QueryImpl.Stateful.simulateQ_link_run,QueryImpl.Stateful.simulateQ_link_run] at shaped
  simp only [Functor.map_map,QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst_put,PFunctor.Lens.State.snd_put,Prod.map_def,id_eq,Prod.eta] at shaped
  have free : ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
        ((simulateQ RegistrationNativeIdentityTemplateLateIdentity.record work).run (keys joint before))).run publicBefore) =
      (fun result => ((result.1.1,result.2),result.1.2)) <$>
        (simulateQ record ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run publicBefore)).run (keys joint before) := by
    simpa only [Prod.swap,show (fun value : (A × Registry) × RegistrationNativeIdentityTemplatePolicy.Public => value) = id from rfl,id_map] using shaped.symm
  rw [free,simulateQ_map,StateT.run_map]
  have tracked := complete joint ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run publicBefore) before
  rw [QueryImpl.Stateful.simulateQ_link_run] at tracked
  have observed := congrArg (Functor.map (fun result : (A × RegistrationNativeIdentityTemplatePolicy.Public) × (Registry × SourceState) =>
    (((result.1.1,result.2.1),result.1.2),result.2.2))) tracked
  simpa only [Functor.map_map,graph,QueryImpl.Stateful.Frame.prod,QueryImpl.Stateful.Frame.linkReshape,
    PFunctor.Lens.State.fst_put,PFunctor.Lens.State.snd_put,Prod.map_def,id_eq] using observed

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource.erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource.erasure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource.policy_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRegistrySource.policy_complete
