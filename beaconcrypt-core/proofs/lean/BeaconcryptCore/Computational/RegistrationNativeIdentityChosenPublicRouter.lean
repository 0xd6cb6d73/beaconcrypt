-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity History AdversarySpec jointImpl)
open PqxdhJointIdentityFamily (FamilyHistory familyPublic familyImpl reductionImpl combineHistory)
open PqxdhJointIdentityFreshness (GlobalState sourceImpl)
open PqxdhDynamicIdentityPool (DynamicSpec)
open PqxdhDynamicIdentityRouting (PublicState)
open PqxdhJointPhase1Reports (ProtocolSpec)
open RegistrationNativeIdentityMainNoRevealCore (Allowed)
open RegistrationNativeIdentityPublicRouter (route familySource source family_program)
variable {count : Nat} {A : Type}
abbrev Auxiliary (count : Nat) := PublicState × FamilyHistory count

def keys (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed) (identity : PublicIdentity) :
    Fin (count+1) → PublicIdentity := target.insertNth identity (familyPublic joint others)

/-- This executable interface receives the challenged public identity and independent known other seeds only; the challenged seed is not an argument. -/
def protocol (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed) (identity : PublicIdentity) :
    QueryImpl ProtocolSpec (StateT (Auxiliary count) (OracleComp AdversarySpec)) := fun query before =>
  match query with
  | .inl query =>
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (reductionImpl joint target others) ((route (keys joint target others identity) query).run before.1)).run before.2
  | .inr _ => pure ((), before)

/-- Only the private interpretation recombines the exact challenger history and locally held other histories. -/
def project (target : Fin (count+1)) (reveals : List (Fin (count+1))) (before : Auxiliary count × History) :
    PublicState × GlobalState (count+1) :=
  (before.1.1, ⟨combineHistory target (before.1.2, before.2), reveals⟩)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem family_run (joint : Primitives) (seeds : Fin (count+1) → IdentitySeed)
    (query : DynamicSpec.Domain) (before : PublicState × GlobalState (count+1)) :
    (familySource joint seeds (.inl query)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (fun request => sourceImpl joint seeds (.inl request))
          ((route (familyPublic joint seeds) query).run before.1)).run before.2 := by
  rcases before with ⟨routerState, history⟩
  change (QueryImpl.Stateful.link (route (familyPublic joint seeds)) (fun request => sourceImpl joint seeds (.inl request)) query).run
    (routerState, history) = _
  rw [QueryImpl.Stateful.link_impl_apply_run]
  rfl

/-- The actual ordinary challenger interpretation retains the exact reply, public router state and every separate target/non-target history. -/
theorem query_source (joint : Primitives) (target : Fin (count+1)) (targetSeed : IdentitySeed)
    (others : Fin count → IdentitySeed) (reveals : List (Fin (count+1))) (query : ProtocolSpec.Domain)
    (before : Auxiliary count × History) :
    Prod.map id (project target reveals) <$>
      (QueryImpl.Stateful.link (protocol joint target others (joint.publicKeys targetSeed)) (jointImpl joint targetSeed) query).run before =
      (familySource joint (target.insertNth targetSeed others) query).run (project target reveals before) := by
  rcases before with ⟨⟨routerState, localHistory⟩, targetHistory⟩
  cases query with
  | inr report =>
      rw [QueryImpl.Stateful.link_impl_apply_run]
      simp only [protocol, familySource, StateT.run, simulateQ_pure]
      rfl
  | inl query =>
      rw [family_run, family_program]
      rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
      simp only [protocol, StateT.run, simulateQ_map]
      have routed := PqxdhJointIdentityFamily.targetRouting_complete joint target targetSeed others
        ((route (keys joint target others (joint.publicKeys targetSeed)) query).run routerState) localHistory targetHistory
      have observed := congrArg (Functor.map (fun result : (DynamicSpec.Range query × PublicState) × FamilyHistory (count+1) =>
        (result.1.1, (result.1.2, (⟨result.2, reveals⟩ : GlobalState (count+1)))))) routed
      simpa only [StateT.run, map_apply, Functor.map_map, Prod.map_def, id_eq, QueryImpl.Stateful.Frame.linkReshape,
        QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, project, keys, PqxdhJointIdentityFamily.familyPublic_insertNth] using observed

/-- Complete adaptive ordinary-challenger routing retains the public state and every actual prior and future identity service observation. -/
theorem family_complete (joint : Primitives) (target : Fin (count+1)) (targetSeed : IdentitySeed)
    (others : Fin count → IdentitySeed) (reveals : List (Fin (count+1))) (work : OracleComp ProtocolSpec A)
    (before : Auxiliary count × History) :
    (fun result => (result.1.1, project target reveals (result.1.2, result.2))) <$>
      (simulateQ (jointImpl joint targetSeed)
        ((simulateQ (protocol joint target others (joint.publicKeys targetSeed)) work).run before.1)).run before.2 =
      (simulateQ (familySource joint (target.insertNth targetSeed others)) work).run (project target reveals before) := by
  have complete := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (QueryImpl.Stateful.link (protocol joint target others (joint.publicKeys targetSeed)) (jointImpl joint targetSeed))
    (familySource joint (target.insertNth targetSeed others)) (project target reveals)
    (query_source joint target targetSeed others reveals) work before
  rw [QueryImpl.Stateful.simulateQ_link_run, Functor.map_map] at complete
  exact complete

/-- On the actual no-reveal protocol trees the seed-free executable router has the exact reserved source interpretation, including its complete public transcript and target/non-target histories. -/
theorem source_complete (joint : Primitives) (target : Fin (count+1)) (targetSeed : IdentitySeed)
    (others : Fin count → IdentitySeed) (reveals : List (Fin (count+1))) (work : OracleComp ProtocolSpec A)
    (allowed : AllQueriesSatisfy work Allowed) (before : Auxiliary count × History) :
    (fun result => (result.1.1, project target reveals (result.1.2, result.2))) <$>
      (simulateQ (jointImpl joint targetSeed)
        ((simulateQ (protocol joint target others (joint.publicKeys targetSeed)) work).run before.1)).run before.2 =
      (simulateQ (source joint (target.insertNth targetSeed others)) work).run (project target reveals before) :=
  (family_complete joint target targetSeed others reveals work before).trans
    (RegistrationNativeIdentityPublicRouter.program_source joint (target.insertNth targetSeed others) work allowed (project target reveals before))

end BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter.family_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter.family_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter.source_complete
