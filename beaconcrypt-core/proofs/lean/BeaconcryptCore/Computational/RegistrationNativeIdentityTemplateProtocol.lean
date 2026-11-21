-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure
import BeaconcryptCore.Computational.RegistrationNativeIdentityIndependentSource

/-! After selection, the public template compiler needs only its symbolic cache and journal. The private key table and genuine service history are owned by a separate protocol interpreter; canonical omitted observations are absent from the executable query tree. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol
open RegistrationNativeIdentityTemplateCensorRecognition (Spec)
open PqxdhJointPhase1Reports (ProtocolSpec)
open PqxdhDynamicIdentityPool (SourceState)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityReindexedCtx (State)
open RegistrationNativeIdentityTemplateAddress (Key)
variable {Value : Type}

abbrev PublicSpec := ProtocolSpec + unifSpec

def coins : QueryImpl unifSpec (OracleComp PublicSpec) := fun query => PublicSpec.query (.inr query)

/-- No selected seed, canonical signature, physical address or source audit is an executable local-state field. -/
noncomputable def handler : QueryImpl Spec (StateT (State Key) (OracleComp PublicSpec))
  | .inl (.inl (.inl query)) => StateT.lift (PublicSpec.query (.inl query) : OracleComp PublicSpec _)
  | .inl (.inl (.inr _)) => pure false
  | .inl (.inr _) => pure ()
  | .inr described => fun before => simulateQ coins ((RegistrationNativeIdentityReindexedCtx.implementation described.input).run before)

/-- Independent hash draws do not add a protocol-pool observation. -/
def source (joint : PqxdhJointIdentity.Primitives) : QueryImpl PublicSpec (StateT SourceState ProbComp)
  | .inl query => RegistrationNativeIdentityMainSource.implementation joint query
  | .inr query => StateT.lift (unifSpec.query query : ProbComp _)

noncomputable def realize (target : Pqxdh.Bytes) (before : State Key × SourceState) : RegistrationNativeIdentityTemplateSource.State :=
  (⟨RegistrationNativeIdentityTemplateGhostView.poolView before.2, (∅, []), some target, none, none⟩, before.1)

private theorem pool_query (joint : PqxdhJointIdentity.Primitives) (query : ProtocolSpec.Domain) (before : SourceState) :
    Prod.map id RegistrationNativeIdentityTemplateGhostView.poolView <$>
      (RegistrationNativeIdentityMainSource.implementation joint query).run before =
    Prod.map id RegistrationNativeIdentityTemplateGhostView.poolView <$>
      (RegistrationNativeIdentityMainSource.implementation joint query).run (RegistrationNativeIdentityTemplateGhostView.poolView before) := by
  cases query with
  | inr report => simp only [RegistrationNativeIdentityMainSource.implementation, StateT.run_pure, map_pure,
      Prod.map_def, id_eq, RegistrationNativeIdentityTemplateGhostView.poolView]
  | inl query => cases query with
    | inl coin =>
      simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
        PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_bind, map_pure, PqxdhDynamicIdentityPool.record,
        RegistrationNativeIdentityTemplateGhostView.poolView, Prod.map_def, id_eq]
    | inr query => cases query with
      | create =>
        simp only [RegistrationNativeIdentityMainSource.implementation]
        rw [PqxdhDynamicIdentityPool.lazyImpl_create, PqxdhDynamicIdentityPool.lazyImpl_create]
        simp only [Functor.map_map, Prod.map_def, id_eq, PqxdhDynamicIdentityPool.createdReply,
          PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityTemplateGhostView.poolView]
      | service handle request | reveal handle =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, StateT.run, map_pure, PqxdhDynamicIdentityPool.record,
          RegistrationNativeIdentityTemplateGhostView.poolView, Prod.map_def, id_eq]

private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem coins_source (joint : PqxdhJointIdentity.Primitives) (work : ProbComp Value) (before : SourceState) :
    (simulateQ (source joint) (simulateQ coins work)).run before = (fun value => (value, before)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin current
  change (do let answer ← unifSpec.query coin; pure (answer, current) : ProbComp _) = _
  simp only [bind_pure_comp]

private theorem coins_apply (joint : PqxdhJointIdentity.Primitives) (work : ProbComp Value) (before : SourceState) :
    (simulateQ (source joint) (simulateQ coins work)) before = (fun value => (value, before)) <$> work :=
  coins_source joint work before

private theorem scan_run (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (scan : Pqxdh.Bytes × List Pqxdh.Bytes) (before : RegistrationNativeIdentityTemplateSource.State) :
    (RegistrationNativeIdentityTemplateErasure.sourceHandler joint selected placeholder (.inl (.inr scan))).run before =
      pure ((), RegistrationNativeIdentityTemplateGhostView.view before) := rfl

/-- The explicit public compiler has exactly the private template source interpretation after selection, with the genuine source pool and its complete audit retained outside the compiler. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) (target : Pqxdh.Bytes)
    (request : Spec.Domain) (before : State Key × SourceState) :
    Prod.map id (realize target) <$>
      (QueryImpl.Stateful.link handler (source joint) request).run before =
      (RegistrationNativeIdentityTemplateErasure.sourceHandler joint selected placeholder request).run (realize target before) := by
  rw [QueryImpl.Stateful.link_impl_apply_run]
  simp only [QueryImpl.Stateful.Frame.prod]
  rcases request with ((protocol | message) | scan) | described
  · simp only [handler, StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query, source,
      Functor.map_map]
    rw [StateT.run_map, Functor.map_map]
    have law := congrArg (fun distribution => (fun result => (result.1,
      ((⟨result.2, (∅, []), some target, none, none⟩ : RegistrationNativeIdentityCensorSource.State), before.1))) <$> distribution) (pool_query joint protocol before.2)
    simp only [RegistrationNativeIdentityTemplateErasure.sourceHandler, RegistrationNativeIdentityTemplateGhostView.normalized,
      RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.protocol, StateT.run, Functor.map_map, Prod.map_def, id_eq,
      realize, RegistrationNativeIdentityTemplateGhostView.view, RegistrationNativeIdentityTemplateGhostView.poolView,
      PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put] at law ⊢
    convert law using 1 <;> rfl
  · simp only [handler, simulateQ_pure, map_pure, Prod.map_def, id_eq,
      RegistrationNativeIdentityTemplateErasure.sourceHandler, RegistrationNativeIdentityTemplateGhostView.normalized,
      RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.unchanged,
      RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.select, realize, StateT.run, reduceCtorEq, false_and, ite_false,
      pure_apply, RegistrationNativeIdentityTemplateGhostView.view, RegistrationNativeIdentityTemplateGhostView.poolView]
    rfl
  · rw [scan_run]
    simp only [handler, StateT.run_pure, simulateQ_pure, map_pure, Prod.map_def, id_eq,
      realize, RegistrationNativeIdentityTemplateGhostView.view, RegistrationNativeIdentityTemplateGhostView.poolView]
    rfl
  · simp only [handler, StateT.run, coins_apply, Functor.map_map, Prod.map_def, id_eq,
      RegistrationNativeIdentityTemplateErasure.sourceHandler, RegistrationNativeIdentityTemplateSource.hash,
      realize, RegistrationNativeIdentityTemplateGhostView.view, RegistrationNativeIdentityTemplateGhostView.poolView]
    rfl

/-- The entire adaptive erased continuation has a public-table/protocol compiler interpretation. The complete genuine source pool remains external, and only its private realization clears the unread audit. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) (target : Pqxdh.Bytes)
    (work : OracleComp Spec Value) (before : State Key × SourceState) :
    (fun result => (result.1.1, realize target (result.1.2, result.2))) <$>
      (simulateQ (source joint) ((simulateQ handler work).run before.1)).run before.2 =
      (simulateQ (RegistrationNativeIdentityTemplateErasure.sourceHandler joint selected placeholder) work).run (realize target before) := by
  have complete := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (QueryImpl.Stateful.link handler (source joint))
    (RegistrationNativeIdentityTemplateErasure.sourceHandler joint selected placeholder) (realize target)
    (query joint selected placeholder target) work before
  rw [QueryImpl.Stateful.simulateQ_link_run, Functor.map_map] at complete
  exact complete

/-- The public language separates original pool coins from independent hash coins and discards only the source-no-op report leaf. -/
def independent : QueryImpl PublicSpec (OracleComp RegistrationNativeIdentityIndependentSource.Spec)
  | .inl (.inl query) => RegistrationNativeIdentityIndependentSource.Spec.query (.inl query)
  | .inl (.inr _) => pure ()
  | .inr coin => RegistrationNativeIdentityIndependentSource.Spec.query (.inr coin)

/-- This exact source-language equality allows the existing bounded lazy/eager reserved-family transport, without adding hash draws to the pool transcript. -/
theorem independent_source (joint : PqxdhJointIdentity.Primitives) (work : OracleComp PublicSpec Value) :
    simulateQ (RegistrationNativeIdentityIndependentSource.lazyImpl joint) (simulateQ independent work) =
      simulateQ (source joint) work := by
  rw [← QueryImpl.simulateQ_compose]
  have leaves : RegistrationNativeIdentityIndependentSource.lazyImpl joint ∘ₛ independent = source joint := by
    funext request
    rcases request with (dynamic | report) | coin
    · simp only [QueryImpl.apply_compose, independent, simulateQ_spec_query, source,
        RegistrationNativeIdentityMainSource.implementation, RegistrationNativeIdentityIndependentSource.lazyImpl]
    · simp only [QueryImpl.apply_compose, independent, simulateQ_pure, source, RegistrationNativeIdentityMainSource.implementation]
    · rfl
  rw [leaves]

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol.independent_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateProtocol.independent_source
