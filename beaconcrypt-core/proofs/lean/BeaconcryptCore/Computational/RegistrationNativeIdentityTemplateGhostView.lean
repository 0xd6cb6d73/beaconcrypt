-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition

/-! After public target selection, the canonical source audit is ghost data for the template-indexed continuation. This quotient retains all actual source seed rows as private interpreter state, and every symbolic ROM key/journal/cost. It is not a constructor capturing those seeds in executable E. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView
open RegistrationNativeIdentityTemplateSource (State Private Spec)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}

def poolView (before : PqxdhDynamicIdentityPool.SourceState) : PqxdhDynamicIdentityPool.SourceState :=
  {before with transcript := []}

def view (before : State) : State :=
  ({before.1 with pool := poolView before.1.pool, hash := (⟨fun _ => none⟩, []), canonical := none, framing := none}, before.2)

private theorem pool_query (joint : PqxdhJointIdentity.Primitives) (query : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (before : PqxdhDynamicIdentityPool.SourceState) :
    Prod.map id poolView <$> (RegistrationNativeIdentityMainSource.implementation joint query).run before =
      Prod.map id poolView <$> (RegistrationNativeIdentityMainSource.implementation joint query).run (poolView before) := by
  cases query with
  | inr report => simp only [RegistrationNativeIdentityMainSource.implementation, StateT.run_pure, map_pure, Prod.map_def, id_eq, poolView]
  | inl query => cases query with
    | inl coin =>
      simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
        PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_bind, map_pure, PqxdhDynamicIdentityPool.record, poolView, Prod.map_def, id_eq]
    | inr query => cases query with
      | create =>
        simp only [RegistrationNativeIdentityMainSource.implementation]
        rw [PqxdhDynamicIdentityPool.lazyImpl_create, PqxdhDynamicIdentityPool.lazyImpl_create]
        simp only [Functor.map_map, Prod.map_def, id_eq, PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record, poolView]
      | service handle request | reveal handle =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_pure, PqxdhDynamicIdentityPool.record, poolView, Prod.map_def, id_eq]

private theorem bind_apply {Local A B : Type} {m : Type → Type} [Monad m]
    (work : StateT Local m A) (next : A → StateT Local m B) (before : Local) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {Local A : Type} {m : Type → Type} [Monad m] (value : A) (before : Local) :
    (pure value : StateT Local m A) before = pure (value, before) := rfl

def observed {A : Type} (result : A × State) := (result.1, (view result.2, result.2.1.target))
def fixed {A : Type} (target : Option Pqxdh.Bytes) (result : A × State) := (result.1, (view result.2, target))

/-- The normalized omitted marker performs no signing request at all: its literal reply is the known placeholder and its remaining observable private-oracle/table state is unchanged. -/
theorem omitted (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (message : Pqxdh.Bytes)
    (placeholder : Ed25519Signature) (before : State) :
    observed <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder (.inr (.omitted handle message))).run before =
      pure (some placeholder, (view before, before.1.target)) := by
  simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
    RegistrationNativeIdentityCensorSource.censored, bind_apply, RegistrationNativeIdentityCensorSource.omitted,
    StateT.run, pure_apply, bind_pure_comp, map_pure, observed, view, poolView,
    RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
    PqxdhDynamicIdentityPool.poolImpl, PqxdhDynamicIdentityPool.record]

private theorem fixed_map {A : Type} (target : Option Pqxdh.Bytes) (work : ProbComp (A × State)) :
    fixed target <$> work = (fun result : A × (State × Option Pqxdh.Bytes) => (result.1, (result.2.1, target))) <$> observed <$> work := by
  rw [Functor.map_map]
  rfl

private theorem omitted_compare {A : Type} (reply : A) (before : State) (target : Pqxdh.Bytes)
    (held : before.1.target = some target) (left right : ProbComp (A × State))
    (leftRun : observed <$> left = pure (reply, (view before, before.1.target)))
    (rightRun : observed <$> right = pure (reply, (view (view before), (view before).1.target))) :
    observed <$> left = fixed (some target) <$> right := by
  rw [leftRun, fixed_map, rightRun, map_pure]
  simp only [held, view, poolView]

private theorem query_observed (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (target : Pqxdh.Bytes) (request : Spec.Domain) (before : State) (held : before.1.target = some target) :
    observed <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run before =
      fixed (some target) <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run (view before) := by
  rcases request with (((protocol | message) | scanned) | described) | marker
  · have law := congrArg (fun distribution => (fun result =>
        (result.1, (({(view before).1 with pool := result.2}, before.2), some target))) <$> distribution)
      (pool_query joint protocol before.1.pool)
    simpa only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, StateT.run, Functor.map_map, Prod.map_def, id_eq,
      observed, fixed, view, poolView, held] using law
  · simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.select, StateT.run, view, held, reduceCtorEq, false_and, ite_false,
      map_pure, observed, fixed, poolView]
  · simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      StateT.run, pure_apply, map_pure, observed, fixed, view, poolView, held]
  · simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.hash,
      StateT.run, Functor.map_map, observed, fixed, view, poolView, held]
  · cases marker with
    | template handle message leading trailing =>
      simp only [RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.template,
        RegistrationNativeIdentityTemplateSource.hash, StateT.run, Functor.map_map, observed, fixed, view, poolView, held]
    | omitted handle message =>
      exact omitted_compare (some placeholder) before target held _ _
        (omitted joint selected handle message placeholder before)
        (omitted joint selected handle message placeholder (view before))

private theorem erase_observed {A : Type} (target : Option Pqxdh.Bytes) (left right : ProbComp (A × State))
    (law : observed <$> left = fixed target <$> right) :
    Prod.map id view <$> left = Prod.map id view <$> right := by
  have erased := congrArg (fun distribution => (fun result : A × (State × Option Pqxdh.Bytes) => (result.1, result.2.1)) <$> distribution) law
  simpa only [Functor.map_map, observed, fixed, Prod.map_def, id_eq] using erased

private theorem target_observed {A : Type} (target : Option Pqxdh.Bytes) (left right : ProbComp (A × State))
    (law : observed <$> left = fixed target <$> right) (result : A × State) (reached : result ∈ support left) :
    result.2.1.target = target := by
  have mapped : observed result ∈ support (observed <$> left) := by
    rw [support_map]
    exact ⟨result, reached, rfl⟩
  rw [law, support_map] at mapped
  obtain ⟨actual, _called, same⟩ := mapped
  exact (congrArg (fun returned : A × (State × Option Pqxdh.Bytes) => returned.2.2) same).symm

/-- After target selection, clearing canonical receipts, the obsolete physical cache/framing, and the source audit commutes with every actual symbolic-source query. Every current reply, private source row and symbolic hash effect remains literal. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (target : Pqxdh.Bytes) (request : Spec.Domain) (before : State) (held : before.1.target = some target) :
    Prod.map id view <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run before =
      Prod.map id view <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run (view before) :=
  erase_observed (some target) _ _ (query_observed joint selected placeholder target request before held)

private theorem query_target (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (target : Pqxdh.Bytes) (request : Spec.Domain) (before : State) (held : before.1.target = some target)
    (result : Spec.Range request × State)
    (reached : result ∈ support ((RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run before)) :
    result.2.1.target = some target :=
  target_observed (some target) _ _ (query_observed joint selected placeholder target request before held) result reached

noncomputable def normalized (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) :
    QueryImpl Spec (StateT State ProbComp) := fun request before =>
  Prod.map id view <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run before

/-- Arbitrary adaptive postselection work can erase that complete canonical source audit online. Only private oracle seed rows and the public symbolic table/journal remain; no challenged secret is passed to an executable constructor here. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (target : Pqxdh.Bytes) (work : OracleComp Spec Value) (before : State) (held : before.1.target = some target) :
    Prod.map id view <$>
      (simulateQ (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder) work).run before =
    (simulateQ (normalized joint selected placeholder) work).run (view before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder) (normalized joint selected placeholder)
    (fun current => current.1.target = some target) view
  · intro request current prior result reached
    exact query_target joint selected placeholder target request current prior result reached
  · intro request current prior
    exact query joint selected placeholder target request current prior
  · exact held

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView.omitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView.omitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView.program
