-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognitionJournal

/-! Before target selection, the executable client can record the inputs of its own explicit CTX calls. This list is not inferred to be public from the physical journal type: the recorder forwards every literal request and derives equality with that private analysis journal on the same execution. Erasing the recorder retains the entire original source state and every original draw. After suppression starts, internal symbolic-token queries require their separate private realization and are not asserted to reveal physical addresses. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal
open RegistrationNativePlatformIdentityCtxCompiler (Spec)
open RegistrationNativePlatformIdentityCtxSource (State implementation)
variable {Value : Type}

/-- The client knows this request value because it is issuing the actual explicit query. -/
def record : QueryImpl Spec (StateT (List Pqxdh.Bytes) (OracleComp Spec)) := fun query before => do
  let reply ← Spec.query query
  pure (reply, match query with | .inl _ => before | .inr bytes => before ++ [bytes])

noncomputable def handler (primitives : PqxdhJointIdentity.Primitives) :
    QueryImpl Spec (StateT (List Pqxdh.Bytes × State) ProbComp) :=
  QueryImpl.Stateful.link record (implementation primitives)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem query (primitives : PqxdhJointIdentity.Primitives) (request : Spec.Domain)
    (before : List Pqxdh.Bytes × State) :
    (handler primitives request).run before =
      (fun result => (result.1, ((match request with | .inl _ => before.1 | .inr bytes => before.1 ++ [bytes]), result.2))) <$>
        (implementation primitives request).run before.2 := by
  rw [handler, QueryImpl.Stateful.link_impl_apply_run]
  simp only [record, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map]
  cases request <;> rfl

/-- Instrumenting client-computed inputs does not change a reply, draw, private generated pool, cache or physical journal. -/
theorem erase (primitives : PqxdhJointIdentity.Primitives) (work : OracleComp Spec Value)
    (before : List Pqxdh.Bytes × State) :
    Prod.map id Prod.snd <$> (simulateQ (handler primitives) work).run before =
      (simulateQ (implementation primitives) work).run before.2 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq (handler primitives) (implementation primitives) Prod.snd
  intro request current
  rw [query]
  simp only [Functor.map_map, Prod.map_def, id_eq, Prod.eta]
  exact id_map _

private theorem step (primitives : PqxdhJointIdentity.Primitives) (request : Spec.Domain)
    (before : List Pqxdh.Bytes × State) (prior : before.1 = before.2.2.2)
    (after : Spec.Range request × (List Pqxdh.Bytes × State))
    (reached : after ∈ support ((handler primitives request).run before)) :
    after.2.1 = after.2.2.2.2 := by
  rw [query, support_map] at reached
  obtain ⟨result, called, same⟩ := reached
  cases same
  cases request with
  | inl request =>
    simp only [implementation, StateT.run, support_map] at called
    obtain ⟨reply, _supported, same⟩ := called
    cases same
    exact prior
  | inr input =>
    simp only [implementation, StateT.run, support_map] at called
    obtain ⟨reply, supported, same⟩ := called
    cases same
    rw [RegistrationNativePlatformCtxBackend.physical_journal input before.2.2 reply supported, prior]

/-- The full adaptive source prefix derives equality of the client-computed list and the private physical analysis journal. -/
theorem synchronized (primitives : PqxdhJointIdentity.Primitives) (work : OracleComp Spec Value)
    (before : List Pqxdh.Bytes × State) (prior : before.1 = before.2.2.2)
    (after : Value × (List Pqxdh.Bytes × State))
    (reached : after ∈ support ((simulateQ (handler primitives) work).run before)) :
    after.2.1 = after.2.2.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query (handler primitives)
    (fun current => current.1 = current.2.2.2) (step primitives) work before prior after reached

/-- Retrospective recognition uses the actual client list, with physical cache coverage derived from the same original source run. -/
theorem cache_absent (primitives : PqxdhJointIdentity.Primitives) (work : OracleComp Spec Value)
    (before : List Pqxdh.Bytes × State) (prior : before.1 = before.2.2.2)
    (provenance : RegistrationNativePlatformCtxProvenance.Provenance before.2.2)
    (after : Value × (List Pqxdh.Bytes × State))
    (reached : after ∈ support ((simulateQ (handler primitives) work).run before))
    (publicKey : PqxdhEd25519EufCma.Ed25519PublicKey) (message leading trailing : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature)
    (verified : primitives.verify publicKey message signature = true)
    (unrecognized : RegistrationNativeIdentityRecognitionJournal.scan primitives.verify publicKey message after.2.1 = none) :
    after.2.2.2.1 ((), leading ++ signature.toList ++ trailing) = none := by
  have equal := synchronized primitives work before prior after reached
  have actual : (after.1, after.2.2) ∈ support ((simulateQ (implementation primitives) work).run before.2) := by
    rw [← erase primitives work before, support_map]
    exact ⟨after, reached, rfl⟩
  exact RegistrationNativeIdentityRecognitionJournal.cache_absent primitives.verify publicKey message leading trailing signature after.2.2.2
    (RegistrationNativeIdentityRecognitionJournal.complete primitives work before.2 provenance _ actual) verified (equal ▸ unrecognized)

end BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal.synchronized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal.synchronized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal.cache_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityClientHashJournal.cache_absent
