-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGhostView

/-! The actual postselection source quotient is the private interpretation of the explicit template-preserving executable marker erasure. Canonical omitted-sign receipts make no executable query. Source key rows remain private oracle state; chosen reserved-key/challenger interpretation is a separate boundary. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure
open RegistrationNativeIdentityTemplateSource (State Spec)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityTemplateGhostView (view normalized)
variable {Value : Type}

/-- This is a private source interpretation of the public template language, not an executable client with source seed rows. -/
noncomputable def sourceHandler (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) :
    QueryImpl RegistrationNativeIdentityTemplateCensorRecognition.Spec (StateT State ProbComp)
  | .inl query => normalized joint selected placeholder (.inl (.inl query))
  | .inr described => fun before => Prod.map id view <$> (RegistrationNativeIdentityTemplateSource.hash described.input).run before

private theorem clipped {A : Type} (reply : A) (before : State) (work : ProbComp (A × State))
    (law : RegistrationNativeIdentityTemplateGhostView.observed <$> work = pure (reply, (view before, before.1.target))) :
    Prod.map id view <$> work = pure (reply, view before) := by
  have erased := congrArg (fun distribution => (fun result : A × (State × Option Pqxdh.Bytes) => (result.1, result.2.1)) <$> distribution) law
  simpa only [Functor.map_map, map_pure, RegistrationNativeIdentityTemplateGhostView.observed, Prod.map_def, id_eq] using erased

private theorem omitted (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat) (message : Pqxdh.Bytes)
    (placeholder : Ed25519Signature) (before : State) :
    (normalized joint selected placeholder (.inr (.omitted handle message))).run before = pure (some placeholder, view before) :=
  clipped (some placeholder) before _ (RegistrationNativeIdentityTemplateGhostView.omitted joint selected handle message placeholder before)

private theorem clean_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : Spec.Domain) (scope : RegistrationNativeIdentityCensorTemplateScope.Allowed request) (before : State) (clean : view before = before) :
    (normalized joint selected placeholder request).run before =
      (simulateQ (sourceHandler joint selected placeholder) (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder request)).run before := by
  rcases request with query | marker
  · cases query with
    | inl query => simp only [RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_spec_query, sourceHandler]
    | inr described =>
      cases indexed : described.input with
      | none => simp only [RegistrationNativeIdentityCensorTemplateScope.Allowed, indexed, Option.isSome_none, Bool.false_eq_true] at scope
      | some input =>
        simp only [RegistrationNativeIdentityTemplateCensorRecognition.erase, indexed, simulateQ_spec_query,
          sourceHandler, normalized, RegistrationNativeIdentityTemplateSource.implementation, StateT.run, Option.getD_some]
  · cases marker with
    | template handle message leading trailing =>
      simp only [RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_spec_query,
        sourceHandler, normalized, RegistrationNativeIdentityTemplateSource.implementation, RegistrationNativeIdentityTemplateSource.template,
        StateT.run, Functor.map_map, Prod.map_def, id_eq, view, RegistrationNativeIdentityTemplateGhostView.poolView]
      rfl
    | omitted handle message =>
      simpa only [RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure, StateT.run_pure, clean] using
        omitted joint selected handle message placeholder before

/-- Each actual admitted postselection source step is the source interpretation of its public marker-erasure program. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (target : Pqxdh.Bytes) (request : Spec.Domain) (scope : RegistrationNativeIdentityCensorTemplateScope.Allowed request)
    (before : State) (held : before.1.target = some target) :
    Prod.map id view <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run before =
      (simulateQ (sourceHandler joint selected placeholder) (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder request)).run (view before) := by
  rw [RegistrationNativeIdentityTemplateGhostView.query joint selected placeholder target request before held]
  exact clean_query joint selected placeholder request scope (view before) rfl

private theorem keeps_clean (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (request : Spec.Domain) (before : State) (result : Spec.Range request × State)
    (reached : result ∈ support ((normalized joint selected placeholder request).run before)) : view result.2 = result.2 := by
  change result ∈ support (Prod.map id view <$> (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder request).run before) at reached
  rw [support_map] at reached
  obtain ⟨actual, _called, rfl⟩ := reached
  rfl

private theorem normalized_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Spec Value) (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (before : State) (clean : view before = before) :
    (simulateQ (normalized joint selected placeholder) work).run before =
      (simulateQ (sourceHandler joint selected placeholder) (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp scope
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    conv_rhs => rw [← clean_query joint selected placeholder request first before clean]
    apply bind_congr_of_forall_mem_support
    intro middle reached
    exact ih middle.1 (later middle.1) middle.2 (keeps_clean joint selected placeholder request before middle reached)

/-- Complete adaptive postselection source execution erases its canonical audit into the explicit public template client, preserving current replies, source-oracle rows, symbolic cache/journal and true costs. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (target : Pqxdh.Bytes) (work : OracleComp Spec Value)
    (scope : work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed)
    (before : State) (held : before.1.target = some target) :
    Prod.map id view <$>
      (simulateQ (RegistrationNativeIdentityTemplateSource.implementation joint selected placeholder) work).run before =
      (simulateQ (sourceHandler joint selected placeholder) (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work)).run (view before) := by
  rw [RegistrationNativeIdentityTemplateGhostView.program joint selected placeholder target work before held]
  exact normalized_program joint selected placeholder work scope (view before) rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure.program
