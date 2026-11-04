-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDynamicIdentityRouting
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainNoRevealCore
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity History)
open PqxdhJointIdentityFamily (FamilyAdversarySpec FamilyHistory familyImpl familyPublic)
open PqxdhJointIdentityFreshness (GlobalState sourceImpl)
open PqxdhDynamicIdentityPool (DynamicSpec)
open PqxdhDynamicIdentityRouting (PublicState appendObservation)
open PqxdhJointPhase1Reports (ProtocolSpec)
open RegistrationNativeIdentityMainNoRevealCore (Allowed)
variable {count : Nat} {A : Type}

/-- The executable public router publishes only reserved public keys and rejects every reveal before any private oracle request. -/
def route (keys : Fin count → PublicIdentity) :
    QueryImpl DynamicSpec (StateT PublicState (OracleComp (FamilyAdversarySpec count))) := fun query before =>
  match query with
  | .inl coin => do
      let reply ← (FamilyAdversarySpec count).query (.inl coin)
      pure (reply, appendObservation (.inl coin) reply before)
  | .inr .create =>
      if available : before.created < count then
        let reply := some (before.created, keys ⟨before.created, available⟩)
        pure (reply, appendObservation (.inr .create) reply { before with created := before.created + 1 })
      else pure (none, appendObservation (.inr .create) none before)
  | .inr (.service index request) =>
      if available : index < before.created ∧ index < count then do
        let reply ← (FamilyAdversarySpec count).query (.inr (⟨index, available.2⟩, request))
        pure (some reply, appendObservation (.inr (.service index request)) (some reply) before)
      else pure (none, appendObservation (.inr (.service index request)) none before)
  | .inr (.reveal index) => pure (none, appendObservation (.inr (.reveal index)) none before)

/-- Actual reserved source routing; candidate reports are source no-ops. -/
def source (joint : Primitives) (seeds : Fin count → IdentitySeed) :
    QueryImpl ProtocolSpec (StateT (PublicState × GlobalState count) ProbComp)
  | .inl query => QueryImpl.Stateful.link (PqxdhDynamicIdentityRouting.routeImpl (familyPublic joint seeds)) (sourceImpl joint seeds) query
  | .inr _ => pure ()

/-- The reveal-rejecting public router under the actual complete private family keeps every sign/DH history and the prior reveal audit. -/
def familySource (joint : Primitives) (seeds : Fin count → IdentitySeed) :
    QueryImpl ProtocolSpec (StateT (PublicState × GlobalState count) ProbComp)
  | .inl query => QueryImpl.Stateful.link (route (familyPublic joint seeds))
      (fun request => sourceImpl joint seeds (.inl request)) query
  | .inr _ => pure ()

/-- The public reveal-rejecting route is the literal reserved source on every permitted protocol request. -/
theorem query_source (joint : Primitives) (seeds : Fin count → IdentitySeed) (query : ProtocolSpec.Domain)
    (allowed : Allowed query) (before : PublicState × GlobalState count) :
    (familySource joint seeds query).run before = (source joint seeds query).run before := by
  rcases before with ⟨routerState, history⟩
  cases query with
  | inr report => rfl
  | inl query =>
      change (QueryImpl.Stateful.link (route (familyPublic joint seeds)) (fun request => sourceImpl joint seeds (.inl request)) query).run (routerState, history) =
        (QueryImpl.Stateful.link (PqxdhDynamicIdentityRouting.routeImpl (familyPublic joint seeds)) (sourceImpl joint seeds) query).run (routerState, history)
      simp only [QueryImpl.Stateful.link_impl_apply_run]
      cases query with
      | inl coin =>
          simp only [route, PqxdhDynamicIdentityRouting.routeImpl, StateT.run,
            simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
          rfl
      | inr query => cases query with
        | reveal index => exact False.elim allowed
        | create =>
            by_cases available : routerState.created < count
            · simp only [route, PqxdhDynamicIdentityRouting.routeImpl, StateT.run, dite_eq_left available, simulateQ_pure]
            · simp only [route, PqxdhDynamicIdentityRouting.routeImpl, StateT.run, dite_eq_right available, simulateQ_pure]
        | service index request =>
            by_cases available : index < routerState.created ∧ index < count
            · simp only [route, PqxdhDynamicIdentityRouting.routeImpl, StateT.run, dite_eq_left available,
                simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
              rfl
            · simp only [route, PqxdhDynamicIdentityRouting.routeImpl, StateT.run, dite_eq_right available, simulateQ_pure]


/-- Every adaptive reveal-free protocol tree retains the actual optional replies, public router state and complete reserved family audit. -/
theorem program_source (joint : Primitives) (seeds : Fin count → IdentitySeed) (work : OracleComp ProtocolSpec A)
    (allowed : AllQueriesSatisfy work Allowed) (before : PublicState × GlobalState count) :
    (simulateQ (familySource joint seeds) work).run before = (simulateQ (source joint seeds) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_source joint seeds query allowed.1 before]
      apply bind_congr
      intro reached
      exact ih reached.1 (allowed.2 reached.1) reached.2

/-- A service adapter keeps the previous reveal audit and changes only the exact chosen family history. -/
theorem family_query (joint : Primitives) (seeds : Fin count → IdentitySeed)
    (query : (FamilyAdversarySpec count).Domain) (before : GlobalState count) :
    (sourceImpl joint seeds (.inl query)).run before =
      (fun result => (result.1, { before with histories := result.2 })) <$>
        (familyImpl joint seeds query).run before.histories := by
  change ((familyImpl joint seeds query).run before.histories >>= fun result =>
    pure (result.1, { before with histories := result.2 })) = _
  rw [bind_pure_comp]

/-- An arbitrary adaptive family service program keeps every prior reveal record and the exact complete sign/DH histories. -/
theorem family_program (joint : Primitives) (seeds : Fin count → IdentitySeed)
    (work : OracleComp (FamilyAdversarySpec count) A) (before : GlobalState count) :
    (simulateQ (fun query => sourceImpl joint seeds (.inl query)) work).run before =
      (fun result => (result.1, { before with histories := result.2 })) <$>
        (simulateQ (familyImpl joint seeds) work).run before.histories := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [family_query joint seeds query before]
      simp only [bind_map_left]
      apply bind_congr
      intro reached
      exact ih reached.1 { before with histories := reached.2 }

end BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.query_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.program_source' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.family_query' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.family_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.family_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityPublicRouter.family_program
