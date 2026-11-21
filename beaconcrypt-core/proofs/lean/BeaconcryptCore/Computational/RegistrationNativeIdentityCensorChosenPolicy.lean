-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityChosenPublicRouter
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorForwardScope

/-! The actual chosen public router's primitive calls update the ordinary censor policy by exactly the public successful optional-reply rule. Only a forbidden selected-target signing request can differ; actual source lowering excludes that request after selection. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open PqxdhJointIdentity (Primitives PublicIdentity IdentitySeed JointSpec AdversarySpec)
open PqxdhEd25519EufCma (Ed25519Signature)
open PqxdhJointIdentityFamily (FamilyHistory reductionImpl)
open PqxdhJointPhase1Reports (ProtocolSpec)
open RegistrationNativeIdentityCensorPolicySource (update)
variable {count : Nat} {A B : Type}

noncomputable def run (placeholder : Ed25519Signature) (work : OracleComp AdversarySpec A) (before : Policy) :
    OracleComp AdversarySpec (A × Policy) :=
  (simulateQ (RegistrationNativeIdentityAdaptiveCensor.implementation placeholder)
    (simulateQ RegistrationNativeIdentityAdaptiveCensor.ordinary work)).run before

def primitiveAllowed (before : Policy) : AdversarySpec.Domain → Prop
  | .inr (.sign message) => before.target ≠ some message
  | _ => True

def primitiveUpdate : AdversarySpec.Domain → Policy → Policy
  | .inr (.sign message), before => {before with forwarded := before.forwarded ++ [message]}
  | _, before => before

private theorem run_bind (placeholder : Ed25519Signature) (work : OracleComp AdversarySpec A)
    (next : A → OracleComp AdversarySpec B) (before : Policy) :
    run placeholder (work >>= next) before = (do
      let result ← run placeholder work before
      run placeholder (next result.1) result.2) := by
  simp only [run, simulateQ_bind, StateT.run_bind]

/-- Every permitted genuine primitive request retains its exact reply and actual ordinary signing-history update. -/
theorem primitive (placeholder : Ed25519Signature) (request : AdversarySpec.Domain) (before : Policy)
    (allowed : primitiveAllowed before request) :
    run placeholder (AdversarySpec.query request) before =
      (do let reply ← (AdversarySpec.query request : OracleComp AdversarySpec _)
          pure (reply, primitiveUpdate request before)) := by
  cases request with
  | inl coin =>
    simp only [run, RegistrationNativeIdentityAdaptiveCensor.ordinary, simulateQ_spec_query,
      RegistrationNativeIdentityAdaptiveCensor.implementation, primitiveUpdate, StateT.run_lift]
  | inr request => cases request with
    | staticDh peer =>
      simp only [run, RegistrationNativeIdentityAdaptiveCensor.ordinary, simulateQ_spec_query,
        RegistrationNativeIdentityAdaptiveCensor.implementation, primitiveUpdate, StateT.run_lift]
    | sign message =>
      change before.target ≠ some message at allowed
      simp only [run, RegistrationNativeIdentityAdaptiveCensor.ordinary, simulateQ_spec_query,
        RegistrationNativeIdentityAdaptiveCensor.implementation, StateT.run, allowed, ite_false, primitiveUpdate]

def ServiceAllowed (target : Fin (count+1)) (before : Policy) (index : Fin (count+1)) : JointSpec.Domain → Prop
  | .sign message => index = target → before.target ≠ some message
  | .staticDh _ => True

/-- Routing a permitted indexed service updates the ordinary policy only for an actual selected-handle signing reply. Independent other-key computations retain all their local histories. -/
theorem service (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (placeholder : Ed25519Signature) (index : Fin (count+1)) (request : JointSpec.Domain)
    (before : FamilyHistory count) (policy : Policy) (allowed : ServiceAllowed target policy index request) :
    run placeholder ((reductionImpl joint target others (.inr (index, request))).run before) policy =
      (fun result => (result, update target.val (.inl (.inr (.service index.val request))) (some result.1) policy)) <$>
        ((reductionImpl joint target others (.inr (index, request))).run before) := by
  induction index using Fin.succAboveCases target with
  | x =>
    have permitted : primitiveAllowed policy (.inr request) := by
      cases request with
      | sign message => exact allowed rfl
      | staticDh peer => trivial
    simp only [reductionImpl, StateT.run, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same]
    rw [run_bind, primitive placeholder (.inr request) policy permitted]
    simp only [run, simulateQ_pure, StateT.run_pure, bind_pure_comp, Functor.map_map]
    cases request <;> simp [primitiveUpdate, update, RegistrationNativeIdentityCensorPolicySource.newMessage]

  | p other =>
    have different : (target.succAbove other).val ≠ target.val := fun equal => Fin.succAbove_ne target other (Fin.ext equal)
    cases request <;>
      simp only [reductionImpl, StateT.run, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove, run,
        simulateQ_pure, update, RegistrationNativeIdentityCensorPolicySource.newMessage,
        different, ite_false, Option.toList_none, List.append_nil, map_pure]
    all_goals rfl

private theorem run_map (placeholder : Ed25519Signature) (observe : A → B) (work : OracleComp AdversarySpec A) (before : Policy) :
    run placeholder (observe <$> work) before = Prod.map observe id <$> run placeholder work before := by
  simp only [run, simulateQ_map, StateT.run_map, Prod.map_def, id_eq]

private theorem run_pure (placeholder : Ed25519Signature) (value : A) (before : Policy) :
    run placeholder (pure value) before = pure (value, before) := by
  simp only [run, simulateQ_pure, StateT.run_pure]

private theorem map_apply {S X Y : Type} (observe : X → Y) (work : StateT S (OracleComp AdversarySpec) X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem pure_apply {S X : Type} (value : X) (before : S) :
    (pure value : StateT S (OracleComp AdversarySpec) X) before = pure (value, before) := rfl

def Permitted (target : Fin (count+1)) (before : Policy) (request : ProtocolSpec.Domain) : Prop :=
  ∀ message, before.target = some message →
    RegistrationNativeIdentityCensorForwardScope.ProtocolAllowed target.val message request

/-- The literal chosen router preserves every reply and all local histories while updating the ordinary censor from the actual successful optional selected-handle reply. -/
theorem protocol (joint : Primitives) (target : Fin (count+1)) (others : Fin count → IdentitySeed)
    (identity : PublicIdentity) (placeholder : Ed25519Signature) (query : ProtocolSpec.Domain)
    (before : RegistrationNativeIdentityChosenPublicRouter.Auxiliary count) (policy : Policy)
    (allowed : Permitted target policy query) :
    run placeholder ((RegistrationNativeIdentityChosenPublicRouter.protocol joint target others identity query).run before) policy =
      (fun result => (result, update target.val query result.1 policy)) <$>
        ((RegistrationNativeIdentityChosenPublicRouter.protocol joint target others identity query).run before) := by
  rcases before with ⟨routerState, history⟩
  cases query with
  | inr report =>
    simp only [RegistrationNativeIdentityChosenPublicRouter.protocol, StateT.run, run_pure, map_pure,
      update, RegistrationNativeIdentityCensorPolicySource.newMessage, Option.toList_none, List.append_nil]
  | inl query => cases query with
    | inl coin =>
      simp only [RegistrationNativeIdentityChosenPublicRouter.protocol, StateT.run,
        RegistrationNativeIdentityPublicRouter.route, simulateQ_spec_query,
        reductionImpl, bind_pure_comp, simulateQ_map, map_apply, run_map]
      rw [primitive placeholder (.inl coin) policy trivial]
      simp only [bind_pure_comp, Functor.map_map, primitiveUpdate, update,
        RegistrationNativeIdentityCensorPolicySource.newMessage, Option.toList_none, List.append_nil]
      rfl
    | inr query => cases query with
      | create =>
        simp only [RegistrationNativeIdentityChosenPublicRouter.protocol, StateT.run,
          RegistrationNativeIdentityPublicRouter.route]
        split_ifs with available <;> simp only [simulateQ_pure, pure_apply, map_pure, run_pure, update,
          RegistrationNativeIdentityCensorPolicySource.newMessage, Option.toList_none, List.append_nil]
      | reveal index =>
        simp only [RegistrationNativeIdentityChosenPublicRouter.protocol, StateT.run,
          RegistrationNativeIdentityPublicRouter.route, simulateQ_pure, pure_apply, map_pure, run_pure, update,
          RegistrationNativeIdentityCensorPolicySource.newMessage, Option.toList_none, List.append_nil]
      | service index request =>
        simp only [RegistrationNativeIdentityChosenPublicRouter.protocol, StateT.run,
          RegistrationNativeIdentityPublicRouter.route]
        split_ifs with available
        · have permitted : ServiceAllowed target policy ⟨index, available.2⟩ request := by
            cases request with
            | sign message =>
              intro same suppressed
              exact (allowed message suppressed (congrArg Fin.val same)) rfl
            | staticDh peer => trivial
          simp only [simulateQ_spec_query, bind_pure_comp, simulateQ_map, map_apply, run_map, Functor.map_map]
          have routed := service joint target others placeholder ⟨index, available.2⟩ request history policy permitted
          simp only [StateT.run] at routed
          rw [routed]
          simp only [Functor.map_map]
          cases request <;> rfl
        · simp only [simulateQ_pure, pure_apply, map_pure, run_pure, update,
            RegistrationNativeIdentityCensorPolicySource.newMessage]
          cases request <;> simp

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy.primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy.primitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy.service

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy.protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenPolicy.protocol
