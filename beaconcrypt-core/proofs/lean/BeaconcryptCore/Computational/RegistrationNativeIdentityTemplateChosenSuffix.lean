-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy
import BeaconcryptCore.Computational.RegistrationAgreementNestedState

/-! The public symbolic-table continuation and the ordinary challenged-key executable have the same actual replies after selection. The chronological symbolic-key journal is ghost bookkeeping; the ordinary challenger owns every genuine selected-key observation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix
open PqxdhJointIdentity (Primitives IdentitySeed PublicIdentity AdversarySpec)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec Cache)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
open RegistrationNativeIdentityChosenPublicRouter (Auxiliary)
open RegistrationNativeIdentityTemplatePolicy (Public)
variable {count : Nat} {A B : Type}

def primitiveCoins : QueryImpl unifSpec (OracleComp AdversarySpec) := fun query => AdversarySpec.query (.inl query)

def external (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed) (identity : PublicIdentity) :
    QueryImpl PublicSpec (StateT (Auxiliary count) (OracleComp AdversarySpec))
  | .inl query => RegistrationNativeIdentityChosenPublicRouter.protocol joint target others identity query
  | .inr query => StateT.lift (primitiveCoins query)

noncomputable def executable (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed) (identity : PublicIdentity) :
    QueryImpl Spec (StateT (Public × Auxiliary count) (OracleComp AdversarySpec)) :=
  QueryImpl.Stateful.link (RegistrationNativeIdentityTemplatePolicy.handler target.val) (external joint target others identity)

noncomputable def client (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed) (identity : PublicIdentity) :
    QueryImpl Spec (StateT (Cache × Auxiliary count) (OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec)) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((RegistrationNativeIdentityTemplateCensorRecognition.handler
      (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others identity) query).run before.1).run before.2

noncomputable def ordinary (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (placeholder : Ed25519Signature) :
    QueryImpl Spec (StateT ((Cache × Auxiliary count) × Policy) (OracleComp AdversarySpec)) :=
  QueryImpl.Stateful.link (client joint target others identity) (RegistrationNativeIdentityAdaptiveCensor.implementation placeholder)

def realize (before : Public × Auxiliary count) : (Cache × Auxiliary count) × Policy :=
  ((before.1.2.1, before.2), before.1.1)

def Allowed (selected : Nat) (target : Pqxdh.Bytes) : Spec.Domain → Prop
  | .inl (.inl (.inl query)) => RegistrationNativeIdentityCensorForwardScope.ProtocolAllowed selected target query
  | _ => True

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem public_coins (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (work : ProbComp A) (before : Auxiliary count) :
    (simulateQ (external joint target others identity) (simulateQ RegistrationNativeIdentityTemplateProtocol.coins work)).run before =
      (fun value => (value, before)) <$> simulateQ primitiveCoins work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityTemplateProtocol.coins,
      external, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
    exact bind_congr (fun answer => ih answer before)

private theorem ordinary_coins (work : ProbComp A) (before : Auxiliary count) (policy : Policy) (placeholder : Ed25519Signature) :
    (simulateQ (RegistrationNativeIdentityAdaptiveCensor.implementation placeholder)
      ((simulateQ (fun query => StateT.lift
        (RegistrationNativeIdentityAdaptiveCensor.Spec.query (.inl (.inl query)) : OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec _)) work).run before)).run policy =
      (fun value => ((value, before), policy)) <$> simulateQ primitiveCoins work := by
  induction work using OracleComp.inductionOn generalizing before policy with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_lift,
      RegistrationNativeIdentityAdaptiveCensor.implementation, bind_assoc, pure_bind, map_bind]
    exact bind_congr (fun answer => ih answer before policy)

private theorem public_coins_apply (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (work : ProbComp A) (before : Auxiliary count) :
    simulateQ (external joint target others identity) (simulateQ RegistrationNativeIdentityTemplateProtocol.coins work) before =
      (fun value => (value, before)) <$> simulateQ primitiveCoins work := public_coins joint target others identity work before

private theorem ordinary_coins_apply (work : ProbComp A) (before : Auxiliary count) (policy : Policy) (placeholder : Ed25519Signature) :
    simulateQ (RegistrationNativeIdentityAdaptiveCensor.implementation placeholder)
      (simulateQ (fun query => StateT.lift
        (RegistrationNativeIdentityAdaptiveCensor.Spec.query (.inl (.inl query)) : OracleComp RegistrationNativeIdentityAdaptiveCensor.Spec _)) work before) policy =
      (fun value => ((value, before), policy)) <$> simulateQ primitiveCoins work := ordinary_coins work before policy placeholder

def Permitted (selected : Fin (count+1)) (policy : Policy) : Spec.Domain → Prop
  | .inl (.inl (.inl query)) => RegistrationNativeIdentityCensorChosenPolicy.Permitted selected policy query
  | _ => True

/-- Each permitted public-template query is exactly the ordinary challenged-key query; only the chronological symbolic-key journal is omitted from the reduction's local state. -/
theorem query (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (placeholder : Ed25519Signature)
    (request : Spec.Domain) (before : Public × Auxiliary count)
    (allowed : Permitted target before.1.1 request) :
    Prod.map id realize <$> (executable joint target others identity request).run before =
      (ordinary joint target others identity placeholder request).run (realize before) := by
  rcases before with ⟨⟨policy, ⟨cache, journal⟩⟩, auxiliary⟩
  unfold executable ordinary
  simp only [realize]
  rw [QueryImpl.Stateful.link_impl_apply_run, QueryImpl.Stateful.link_impl_apply_run]
  rcases request with ((protocol | selection) | scanned) | described
  · have law := RegistrationNativeIdentityCensorChosenPolicy.protocol joint target others identity placeholder protocol auxiliary policy allowed
    have observed := congrArg (Functor.map (fun result : (PqxdhJointPhase1Reports.ProtocolSpec.Range protocol × Auxiliary count) × Policy =>
      (result.1.1, ((cache, result.1.2), result.2)))) law
    simp only [RegistrationNativeIdentityTemplatePolicy.handler, client,
      RegistrationNativeIdentityTemplateCensorRecognition.handler, StateT.run, lift_apply,
      simulateQ_spec_query, simulateQ_map, map_apply,
      external, bind_pure_comp, Functor.map_map, RegistrationNativeIdentityCensorChosenPolicy.run,
      QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, realize, Prod.map_def, id_eq] at observed ⊢
    convert observed.symm using 1 <;> rfl
  · by_cases eligible : policy.target = none ∧ selection ∉ policy.forwarded
    all_goals simp [RegistrationNativeIdentityTemplatePolicy.handler,
      RegistrationNativeIdentityCensorPolicySource.choose, client,
      RegistrationNativeIdentityTemplateCensorRecognition.handler, StateT.run,
      lift_apply, pure_apply, map_apply, simulateQ_pure, simulateQ_map, Functor.map_map,
      RegistrationNativeIdentityAdaptiveCensor.implementation, eligible, map_pure,
      QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, realize, Prod.map_def, id_eq]
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, client,
      RegistrationNativeIdentityTemplateCensorRecognition.handler,
      StateT.run, pure_apply, simulateQ_pure, map_pure,
      QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, realize, Prod.map_def, id_eq]
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, client,
      RegistrationNativeIdentityTemplateCensorRecognition.handler, RegistrationNativeIdentityReindexedCtx.implementation,
      StateT.run, simulateQ_map, map_apply, public_coins_apply, ordinary_coins_apply, Functor.map_map,
      QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put, realize, Prod.map_def, id_eq]
    rfl

/-- Every possible public query reply preserves an already chosen target, including optional service rejection and all independent hash draws. -/
theorem query_target (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (message : Pqxdh.Bytes) (request : Spec.Domain) (before : Public × Auxiliary count)
    (held : before.1.1.target = some message) (result : Spec.Range request × (Public × Auxiliary count))
    (reached : result ∈ support ((executable joint target others identity request).run before)) :
    result.2.1.1.target = some message := by
  rcases before with ⟨⟨policy, ⟨cache, journal⟩⟩, auxiliary⟩
  change policy.target = some message at held
  unfold executable at reached
  rw [QueryImpl.Stateful.link_impl_apply_run] at reached
  rcases request with ((protocol | selection) | scanned) | described
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, simulateQ_map,
      simulateQ_spec_query, bind_pure_comp, map_apply, external, Functor.map_map, support_map] at reached
    obtain ⟨actual, _called, rfl⟩ := reached
    exact held
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, RegistrationNativeIdentityCensorPolicySource.choose,
      held, reduceCtorEq, false_and, ite_false, StateT.run, simulateQ_pure] at reached
    cases reached
    exact held
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, StateT.run_pure, simulateQ_pure, map_pure,
      support_pure, Set.mem_singleton_iff] at reached
    cases reached
    exact held
  · simp only [RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, simulateQ_map, map_apply,
      Functor.map_map, support_map] at reached
    obtain ⟨actual, _called, rfl⟩ := reached
    exact held

/-- The complete adaptive postselection continuation has the literal ordinary weak-EUF executable interpretation. The hypothesis restricts only forwarded requests, as supplied by actual operational lowering. -/
theorem program (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes)
    (work : OracleComp Spec A) (before : Public × Auxiliary count) (held : before.1.1.target = some message)
    (allowed : work.AllQueriesSatisfy (Allowed target.val message)) :
    Prod.map id realize <$> (simulateQ (executable joint target others identity) work).run before =
      (simulateQ (ordinary joint target others identity placeholder) work).run (realize before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    have permitted : Permitted target before.1.1 request := by
      rcases request with ((protocol | selection) | scanned) | described
      · intro selected selectedEq
        have equal := Option.some.inj (held.symm.trans selectedEq)
        subst selected
        exact first
      all_goals trivial
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    conv_rhs => rw [← query joint target others identity placeholder request before permitted]
    rw [bind_map_left]
    apply bind_congr_of_forall_mem_support
    intro result reached
    exact ih result.1 result.2 (query_target joint target others identity message request before held result reached) (later result.1)

private theorem client_program (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (work : OracleComp Spec A) (before : Cache × Auxiliary count) :
    (simulateQ (client joint target others identity) work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.handler
          (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others identity)) work).run before.1).run before.2 := by
  exact RegistrationAgreementNestedState.program _ work before

/-- Reassociation of the actual ordinary executable preserves its value, hash cache, independent-key router and censor policy. -/
theorem ordinary_program (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (placeholder : Ed25519Signature) (work : OracleComp Spec A)
    (cache : Cache) (auxiliary : Auxiliary count) (policy : Policy) :
    (simulateQ (ordinary joint target others identity placeholder) work).run ((cache, auxiliary), policy) =
      (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
        (simulateQ (RegistrationNativeIdentityAdaptiveCensor.implementation placeholder)
          (((simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.handler
            (RegistrationNativeIdentityChosenPublicRouter.protocol joint target others identity)) work).run cache).run auxiliary)).run policy := by
  unfold ordinary
  rw [QueryImpl.Stateful.simulateQ_link_run, client_program]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map,
    QueryImpl.Stateful.Frame.linkReshape, QueryImpl.Stateful.Frame.prod,
    PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put]

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.query_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.query_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.ordinary_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSuffix.ordinary_program
