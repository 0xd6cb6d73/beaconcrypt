-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame
/-! After selection the whole before-accept traversal preserves its target and never forwards a genuine signing request for that target. This is derived from every actual lowering step, including later failed callbacks and early public stops. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPublicClient (ClientState)
open PqxdhEd25519EufCma (Ed25519Signature)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
variable {S A : Type}

private theorem bind_scoped {X Y : Type} (predicate : Old.Domain → Prop) (work : OracleComp Old X)
    (next : X → OracleComp Old Y) (prior : work.AllQueriesSatisfy predicate)
    (later : ∀ value ∈ support work, (next value).AllQueriesSatisfy predicate) :
    (work >>= next).AllQueriesSatisfy predicate := by
  induction work using OracleComp.inductionOn with
  | pure value => exact later value (by simp only [mem_support_pure_iff])
  | query_bind query rest ih =>
    obtain ⟨first,following⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [bind_assoc,allQueriesSatisfy_query_bind_iff]
    refine ⟨first,fun reply => ih reply (following reply) ?_⟩
    intro value supported
    apply later value
    rw [mem_support_bind_iff]
    exact ⟨reply,by simp only [support_query,Set.mem_univ],supported⟩

private theorem enter_target (bundle : Nat) (query : TypedSpec.Domain) (mode : Mode) :
    (RegistrationNativeIdentityCensorCompiler.enter bundle query mode).target = mode.target := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

private theorem callback_scope (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain)
    (message : Pqxdh.Bytes) (before : S × Mode) (held : before.2.target = some message) :
    ((RegistrationNativeIdentityCensorPublicClient.callback selected bundle placeholder frontend query).run before).AllQueriesSatisfy
        (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorPublicClient.callback selected bundle placeholder frontend query).run before),
        result.2.2.target = some message := by
  have entered := (enter_target bundle query before.2).trans held
  have prior := RegistrationNativeIdentityCensorForwardScope.program selected placeholder message ((frontend query).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2) entered
  simp only [RegistrationNativeIdentityCensorPublicClient.callback,StateT.run,bind_pure_comp]
  refine ⟨RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ prior.1,?_⟩
  intro result reached
  rw [support_map] at reached
  obtain ⟨actual,called,rfl⟩ := reached
  exact prior.2 actual called

private theorem step_scope (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain)
    (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message) :
    ((RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend query).run before).AllQueriesSatisfy
        (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend query).run before),
        result.2.1.2.target = some message := by
  have prior := callback_scope selected bundle placeholder frontend query message before.1 held
  simp only [RegistrationNativeIdentityCensorPublicClient.step,StateT.run]
  refine ⟨RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ prior.1,?_⟩
  intro result reached
  rw [support_map] at reached
  obtain ⟨actual,called,rfl⟩ := reached
  exact prior.2 actual called

private theorem before_scope (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (query : TypedSpec.Domain)
    (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message) :
    ((RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before).AllQueriesSatisfy
        (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before),
        result.2.1.2.target = some message := by
  cases query with
  | inl coin => exact step_scope selected bundle placeholder frontend (.inl coin) message before held
  | inr command =>
    cases command with
    | accept packet =>
      by_cases current : before.2 = accept
      · simp only [RegistrationNativeIdentityCensorBeforeAccept.step,StateT.run,current,ite_true]
        refine ⟨allQueriesSatisfy_pure _ _,?_⟩
        intro result reached
        obtain rfl := eq_of_mem_support_pure _ reached
        exact held
      · simpa only [RegistrationNativeIdentityCensorBeforeAccept.step,StateT.run,current,ite_false] using
          step_scope selected bundle placeholder frontend (.inr (.accept packet)) message before held
    | create ed ml key | bundle owner | build token application | finish owner packet | hmac key input | hash input | serverSend key payload | serverRaw bytes | beaconSend owner payload | beaconRaw owner bytes =>
        exact step_scope selected bundle placeholder frontend _ message before held

private theorem visit_query (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : ClientState S) :
    RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (TypedSpec.query query >>= next) before = (do
      let result ← (RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before
      match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before result.1 result.2 with
      | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next result.1) result.2
      | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason)) := rfl

/-- The actual whole adaptive traversal never submits a genuine signing request for its existing selected target. -/
theorem visit (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message) :
    (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before).AllQueriesSatisfy
      (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    rw [visit_query]
    have prior := before_scope selected bundle accept placeholder frontend defaults query message before held
    apply bind_scoped _ _ _ prior.1
    intro result reached
    cases RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before result.1 result.2 with
    | none => exact ih result.1 result.2 (prior.2 result reached)
    | some reason => exact allQueriesSatisfy_pure _ _

/-- Any packet returned by the actual postselection visitor carries exactly its existing selected message. Public publication stops return none. -/
theorem returned (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message)
    (found : Option RegistrationNativeIdentityCensorPacketClient.Found)
    (supported : found ∈ support (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)) :
    ∀ target packet, found = some (target,packet) → target = message := by
  induction work using OracleComp.inductionOn generalizing before found with
  | pure value =>
    obtain rfl := eq_of_mem_support_pure _ supported
    intro target packet impossible
    cases impossible
  | query_bind query next ih =>
    rw [visit_query,mem_support_bind_iff] at supported
    obtain ⟨result,called,continued⟩ := supported
    have heldAfter := (before_scope selected bundle accept placeholder frontend defaults query message before held).2 result called
    cases observed : RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before result.1 result.2 with
    | none =>
      rw [observed] at continued
      exact ih result.1 result.2 heldAfter found continued
    | some reason =>
      rw [observed] at continued
      obtain rfl := eq_of_mem_support_pure _ continued
      rw [heldAfter]
      cases reason with
      | published => intro target packet impossible; cases impossible
      | attempted original reply =>
        intro target packet same
        exact (Prod.mk.inj (Option.some.inj same)).1.symm

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward.visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward.visit
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward.returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward.returned
