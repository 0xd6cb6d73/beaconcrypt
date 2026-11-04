-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionLoss
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorChosenReduction

/-! The executable fixed public bundle/accept client uses the original typed callback tree, with template-indexed hash addresses and no captured challenged secret. The whole stopped prefix and guarded first-selector continuation retain that same tree; initialized finite causal inclusion remains separate. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
open PqxdhJointIdentity (Primitives PublicIdentity)
open RegistrationNativeIdentityCensorPacketClient (Found)
open RegistrationNativeIdentityCensorPublicClient (ClientState)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev New := RegistrationNativeIdentityTemplateCensorRecognition.Spec
open RegistrationNativeIdentityTemplateSelectionCut.Original (Cut stop)
variable {S A : Type}

private def Scoped (selected : Nat) (message : Pqxdh.Bytes) (work : OracleComp Old A) : Prop :=
  work.AllQueriesSatisfy RegistrationNativeIdentityCensorTemplateScope.Allowed ∧
  work.AllQueriesSatisfy (RegistrationNativeIdentityCensorTargetAnnotations.Allowed selected message)

private theorem bind_scoped {X Y : Type} (scope : Old.Domain → Prop)
    (work : OracleComp Old X) (next : X → OracleComp Old Y)
    (prior : work.AllQueriesSatisfy scope)
    (later : ∀ value ∈ support work, (next value).AllQueriesSatisfy scope) :
    (work >>= next).AllQueriesSatisfy scope := by
  induction work using OracleComp.inductionOn with
  | pure value => exact later value (by simp only [mem_support_pure_iff])
  | query_bind request rest ih =>
    obtain ⟨first, continued⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [bind_assoc, allQueriesSatisfy_query_bind_iff]
    refine ⟨first, fun reply => ih reply (continued reply) ?_⟩
    intro value reached
    apply later value
    rw [mem_support_bind_iff]
    exact ⟨reply, by simp only [support_query, Set.mem_univ], reached⟩

private theorem enter_target (bundle : Nat) (query : TypedSpec.Domain) (mode : Mode) :
    (RegistrationNativeIdentityCensorCompiler.enter bundle query mode).target = mode.target := by
  cases query with
  | inl coin => rfl
  | inr command => cases command <;> rfl

private theorem callback_scope (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain)
    (message : Pqxdh.Bytes) (before : S × Mode) (held : before.2.target = some message) :
    Scoped selected message ((RegistrationNativeIdentityCensorPublicClient.callback selected bundle placeholder frontend query).run before) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorPublicClient.callback selected bundle placeholder frontend query).run before),
        result.2.2.target = some message := by
  have entered : (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2).target = some message :=
    (enter_target bundle query before.2).trans held
  have shape :=  RegistrationNativeIdentityCensorTemplateScope.program selected placeholder ((frontend query).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2)
  have annotated := RegistrationNativeIdentityCensorTargetAnnotations.program selected placeholder message ((frontend query).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter bundle query before.2) entered
  simp only [RegistrationNativeIdentityCensorPublicClient.callback, StateT.run, bind_pure_comp]
  refine ⟨⟨RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ shape,
    RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ annotated.1⟩, ?_⟩
  intro result reached
  rw [support_map] at reached
  obtain ⟨actual, called, rfl⟩ := reached
  exact annotated.2 actual called

private theorem step_scope (selected bundle : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source))) (query : TypedSpec.Domain)
    (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message) :
    Scoped selected message ((RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend query).run before) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend query).run before),
        result.2.1.2.target = some message := by
  have prior := callback_scope selected bundle placeholder frontend query message before.1 held
  simp only [RegistrationNativeIdentityCensorPublicClient.step, StateT.run]
  refine ⟨⟨RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ prior.1.1,
    RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ prior.1.2⟩, ?_⟩
  intro result reached
  rw [support_map] at reached
  obtain ⟨actual, called, rfl⟩ := reached
  exact prior.2 actual called

private theorem before_step_scope (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (query : TypedSpec.Domain)
    (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message) :
    Scoped selected message ((RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before) ∧
      ∀ result ∈ support ((RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before),
        result.2.1.2.target = some message := by
  cases query with
  | inl coin => exact step_scope selected bundle placeholder frontend (.inl coin) message before held
  | inr command =>
    cases command with
    | accept packet =>
      by_cases current : before.2 = accept
      · simp only [RegistrationNativeIdentityCensorBeforeAccept.step, StateT.run, current, ite_true]
        refine ⟨⟨allQueriesSatisfy_pure _ _, allQueriesSatisfy_pure _ _⟩, ?_⟩
        intro result reached
        obtain rfl := eq_of_mem_support_pure _ reached
        exact held
      · simpa only [RegistrationNativeIdentityCensorBeforeAccept.step, StateT.run, current, ite_false] using
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

private theorem visit_scope (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (message : Pqxdh.Bytes) (before : ClientState S) (held : before.1.2.target = some message) :
    Scoped selected message (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact ⟨allQueriesSatisfy_pure _ _, allQueriesSatisfy_pure _ _⟩
  | query_bind query next ih =>
    rw [visit_query]
    have prior := before_step_scope selected bundle accept placeholder frontend defaults query message before held
    constructor
    · apply bind_scoped _ _ _ prior.1.1
      intro result reached
      cases RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before result.1 result.2 with
      | none => exact (ih result.1 result.2 (prior.2 result reached)).1
      | some reason => exact allQueriesSatisfy_pure _ _
    · apply bind_scoped _ _ _ prior.1.2
      intro result reached
      cases RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before result.1 result.2 with
      | none => exact (ih result.1 result.2 (prior.2 result reached)).2
      | some reason => exact allQueriesSatisfy_pure _ _


private def joined (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : ClientState S) (current : (TypedSpec.Range query × S) × Mode) : OracleComp Old (Option Found) :=
  let after : ClientState S := ((current.1.2, current.2), before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
  match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
  | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) after
  | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason)

private theorem joined_scope (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : ClientState S) (message : Pqxdh.Bytes) (current : (TypedSpec.Range query × S) × Mode)
    (held : current.2.target = some message) :
    Scoped selected message (joined selected bundle accept placeholder frontend defaults query next before current) := by
  let after : ClientState S := ((current.1.2, current.2), before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
  change Scoped selected message (match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
    | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) after
    | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason))
  cases RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
  | none => exact visit_scope selected bundle accept placeholder frontend defaults (next current.1.1) message after held
  | some reason => exact ⟨allQueriesSatisfy_pure _ _, allQueriesSatisfy_pure _ _⟩

private theorem joined_stem (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : ClientState S) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old ((TypedSpec.Range query × S) × Mode))
    (prior : RegistrationNativeIdentityTemplateSelectionPrefixScope.GuardedStem selected message inputs continued) :
    RegistrationNativeIdentityTemplateSelectionLoss.Stem selected message inputs
      (fun reply => continued reply >>= joined selected bundle accept placeholder frontend defaults query next before) := by
  obtain ⟨rest, body, safe⟩ := prior
  refine ⟨fun answer => rest answer >>= joined selected bundle accept placeholder frontend defaults query next before, ?_, ?_⟩
  · simpa only [bind_assoc] using congrArg (fun code => code >>= joined selected bundle accept placeholder frontend defaults query next before) body
  · intro answer
    constructor
    · apply bind_scoped _ _ _ (safe answer).1
      intro current reached
      exact (joined_scope selected bundle accept placeholder frontend defaults query next before message current ((safe answer).2.2 current reached)).1
    · apply bind_scoped _ _ _ (safe answer).2.1
      intro current reached
      exact (joined_scope selected bundle accept placeholder frontend defaults query next before message current ((safe answer).2.2 current reached)).2


private theorem query_lower (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : ClientState S)
    (notCurrent : ∀ packet, query = .inr (.accept packet) → before.2 ≠ accept) :
    RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (TypedSpec.query query >>= next) before =
      (do let current ← (simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
            ((frontend query).run before.1.1)).run (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2)
          joined selected bundle accept placeholder frontend defaults query next before current) := by
  have stepEq : (RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before =
      (RegistrationNativeIdentityCensorPublicClient.step selected bundle placeholder frontend query).run before := by
    cases query with
    | inl coin => rfl
    | inr command => cases command with
      | accept packet => simp only [RegistrationNativeIdentityCensorBeforeAccept.step, StateT.run, notCurrent packet rfl, ite_false]
      | create ed ml key | bundle owner | build token app | finish owner packet | hmac key input | hash input | serverSend key payload | serverRaw bytes | beaconSend owner payload | beaconRaw owner bytes => rfl
  rw [visit_query, stepEq]
  simp only [RegistrationNativeIdentityCensorPublicClient.step, StateT.run,
    RegistrationNativeIdentityCensorPublicClient.callback, bind_pure_comp, bind_map_left]
  rfl

private theorem query_current (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (packet : beaconcrypt_core.registration.InitPacket)
    (next : TypedSpec.Range (.inr (.accept packet)) → OracleComp TypedSpec A) (before : ClientState S) (current : before.2 = accept) :
    RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (TypedSpec.query (.inr (.accept packet)) >>= next) before =
      pure (before.1.2.target.map fun message => (message, packet)) := by
  rw [visit_query]
  simp only [RegistrationNativeIdentityCensorBeforeAccept.step, StateT.run, current, ite_true,
    pure_bind, RegistrationNativeIdentityCensorPublicClient.observe, RegistrationNativeIdentityCensorPacketClient.finish]

private theorem enter_none (bundle : Nat) (query : TypedSpec.Domain) (mode : Mode) (missing : mode.target = none) :
    RegistrationNativeIdentityTemplateSelectionPrefixScope.Ready (RegistrationNativeIdentityCensorCompiler.enter bundle query mode) := by
  cases query with
  | inl coin => exact ⟨missing, rfl⟩
  | inr command => cases command <;> exact ⟨missing, rfl⟩

private theorem enter_journal (bundle : Nat) (query : TypedSpec.Domain) (mode : Mode)
    (before : RegistrationNativeIdentityCensorSource.State) (prior : RegistrationNativeIdentityCensorPrefixJournal.Aligned mode before) :
    RegistrationNativeIdentityCensorPrefixJournal.Aligned (RegistrationNativeIdentityCensorCompiler.enter bundle query mode) before := by
  cases query with
  | inl coin => exact prior
  | inr command => cases command <;> exact prior


private theorem first_scope (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : ClientState S) (missing : before.1.2.target = none) :
    (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)).AllQueriesSatisfy
      RegistrationNativeIdentityTemplateSelectionPrefixScope.BeforeSelection := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    by_cases current : ∃ packet, query = .inr (.accept packet) ∧ before.2 = accept
    · obtain ⟨packet, rfl, chosen⟩ := current
      rw [query_current selected bundle accept placeholder frontend defaults packet next before chosen]
      exact allQueriesSatisfy_pure _ _
    · have notCurrent : ∀ packet, query = .inr (.accept packet) → before.2 ≠ accept := by
        intro packet same selectedAccept
        exact current ⟨packet, same, selectedAccept⟩
      rw [query_lower selected bundle accept placeholder frontend defaults query next before notCurrent,
        RegistrationNativeIdentityTemplateSelectionCut.Original.bind]
      have prior := RegistrationNativeIdentityTemplateSelectionPrefixScope.program selected placeholder ((frontend query).run before.1.1)
        (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) (enter_none bundle query before.1.2 missing)
      have tagged := RegistrationNativeIdentityTemplateSelectionPrefixScope.before_selection selected placeholder ((frontend query).run before.1.1)
        (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) (enter_none bundle query before.1.2 missing)
      apply bind_scoped _ _ _ tagged
      intro cut reached
      cases cut with
      | returned current =>
        let after : ClientState S := ((current.1.2, current.2), before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
        change (stop (match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
          | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) after
          | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason))).AllQueriesSatisfy _
        cases RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
        | none => exact ih current.1.1 after (prior.2 current.1 current.2 reached).1
        | some reason => exact allQueriesSatisfy_pure _ _
      | selected message continued => exact allQueriesSatisfy_pure _ _


private theorem returned_pure (value expected : Option Found)
    (reached : Cut.returned value ∈ support (stop (pure expected))) : value = expected := by
  change Cut.returned value ∈ support (pure (Cut.returned expected)) at reached
  exact Cut.returned.inj (eq_of_mem_support_pure _ reached)

/-- If the literal before-accept client returns before encountering any selector, its public packet observation is none. This holds for every arbitrary source reply, before any private interpretation or security assumption. -/
theorem returned_none (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none) (value : Option Found)
    (reached : Cut.returned value ∈ support (stop (RegistrationNativeIdentityCensorPacketClient.visit
      selected bundle accept placeholder frontend defaults work before))) : value = none := by
  induction work using OracleComp.inductionOn generalizing before value with
  | pure returned => exact returned_pure value none reached
  | query_bind query next ih =>
    by_cases current : ∃ packet, query = .inr (.accept packet) ∧ before.2 = accept
    · obtain ⟨packet,rfl,chosen⟩ := current
      rw [query_current selected bundle accept placeholder frontend defaults packet next before chosen,missing] at reached
      exact returned_pure value none reached
    · have notCurrent : ∀ packet, query = .inr (.accept packet) → before.2 ≠ accept := by
        intro packet same chosen
        exact current ⟨packet,same,chosen⟩
      rw [query_lower selected bundle accept placeholder frontend defaults query next before notCurrent,
        RegistrationNativeIdentityTemplateSelectionCut.Original.bind,mem_support_bind_iff] at reached
      obtain ⟨cut,called,continued⟩ := reached
      cases cut with
      | selected message nextCut =>
        simp only [mem_support_pure_iff,reduceCtorEq] at continued
      | returned current =>
        have ready := (RegistrationNativeIdentityTemplateSelectionPrefixScope.program selected placeholder ((frontend query).run before.1.1)
          (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) (enter_none bundle query before.1.2 missing)).2 current.1 current.2 called
        let after : ClientState S := ((current.1.2,current.2),before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
        change Cut.returned value ∈ support (stop (match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
          | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) after
          | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason))) at continued
        cases observed : RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
        | none =>
          simp only [observed] at continued
          exact ih current.1.1 after ready.1 value continued
        | some reason =>
          simp only [observed] at continued
          have empty : RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason = none := by
            rw [ready.1]
            cases reason <;> rfl
          rw [empty] at continued
          exact returned_pure value none continued

private theorem before_allowed (query : Old.Domain)
    (prior : RegistrationNativeIdentityTemplateSelectionPrefixScope.BeforeSelection query) :
    RegistrationNativeIdentityTemplatePublicPrefix.Allowed query := by
  rcases query with (((protocol | selection) | scanned) | described) | marker
  · trivial
  · exact False.elim prior
  · exact False.elim prior
  · exact prior.2
  · exact False.elim prior

/-- The literal executable packet visitor has the same entire physical and public first-selector prefix. The full original callback state and continuation stay attached to the actual cut. -/
theorem prefix_source (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State) :
    Prod.map (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder)
      RegistrationNativeIdentityTemplatePublicPrefix.project <$>
      (simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
        (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore =
      (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected)
        (RegistrationNativeIdentityTemplateSelectionCut.stop
          (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
            (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)))).run
        (RegistrationNativeIdentityTemplatePublicPrefix.project privateBefore) := by
  have coupled := RegistrationNativeIdentityTemplatePublicPrefix.program joint selected placeholder _
    ((first_scope selected bundle accept placeholder frontend defaults work before missing).mono before_allowed) privateBefore
  have observed := congrArg (Functor.map (Prod.map (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder) id)) coupled
  have erased := congrArg (fun code => (simulateQ (RegistrationNativeIdentityTemplatePublicPrefix.publicSource joint selected) code).run
    (RegistrationNativeIdentityTemplatePublicPrefix.project privateBefore))
      (RegistrationNativeIdentityTemplateSelectionCut.Original.erase_stop placeholder
        (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))
  simp only [simulateQ_map, StateT.run_map] at erased
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed.trans erased


private theorem visit_stem (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (Option Found))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore)) :
    RegistrationNativeIdentityTemplateSelectionLoss.Stem selected message after.2.hash.2 continued := by
  induction work using OracleComp.inductionOn generalizing before privateBefore message continued after with
  | pure value =>
    change (Cut.selected message continued, after) ∈ support (pure (Cut.returned none, privateBefore)) at reached
    obtain impossible := eq_of_mem_support_pure _ reached
    cases impossible
  | query_bind query next ih =>
    by_cases current : ∃ packet, query = .inr (.accept packet) ∧ before.2 = accept
    · obtain ⟨packet, rfl, chosen⟩ := current
      rw [query_current selected bundle accept placeholder frontend defaults packet next before chosen] at reached
      change (Cut.selected message continued, after) ∈ support (pure (Cut.returned (before.1.2.target.map fun wanted => (wanted, packet)), privateBefore)) at reached
      obtain impossible := eq_of_mem_support_pure _ reached
      cases impossible
    · have notCurrent : ∀ packet, query = .inr (.accept packet) → before.2 ≠ accept := by
        intro packet same selectedAccept
        exact current ⟨packet, same, selectedAccept⟩
      rw [query_lower selected bundle accept placeholder frontend defaults query next before notCurrent,
        RegistrationNativeIdentityTemplateSelectionCut.Original.bind] at reached
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, called, following⟩ := reached
      have shape := RegistrationNativeIdentityTemplateSelectionPrefixScope.program_stem joint selected placeholder ((frontend query).run before.1.1)
        (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) (enter_none bundle query before.1.2 missing)
        privateBefore (enter_journal bundle query before.1.2 privateBefore.2 journal) middle called
      rcases middle with ⟨cut, state⟩
      cases cut with
      | returned current =>
        let nextState : ClientState S := ((current.1.2, current.2), before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
        change (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
          (stop (match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 nextState with
            | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) nextState
            | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason)))).run state) at following
        cases observed : RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 nextState with
        | none =>
          rw [observed] at following
          exact ih current.1.1 nextState shape.1.1 state shape.2 message continued after following
        | some reason =>
          rw [observed] at following
          change (Cut.selected message continued, after) ∈ support (pure (Cut.returned (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason), state)) at following
          obtain impossible := eq_of_mem_support_pure _ following
          cases impossible
      | selected selectedMessage body =>
        simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at following
        cases following
        apply joined_stem selected bundle accept placeholder frontend defaults query next before message _ body
        exact RegistrationNativeIdentityTemplateSelectionPrefixScope.program_guarded_stem joint selected placeholder ((frontend query).run before.1.1)
          (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) (enter_none bundle query before.1.2 missing)
          privateBefore (enter_journal bundle query before.1.2 privateBefore.2 journal) message body after called

/-- The actual whole before-accept visitor carries the same first-selector source receipts and guarded scan/omission stem, including every preceding failed callback and the complete later adaptive continuation. -/
theorem first_cut (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (Option Found))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore)) :
    RegistrationNativeIdentityTemplateSelectionSource.Ready selected after ∧
      RegistrationNativeIdentityTemplateSelectionLoss.Stem selected message after.2.hash.2 continued := by
  exact ⟨RegistrationNativeIdentityTemplateSelectionSource.program joint selected placeholder _
      ((first_scope selected bundle accept placeholder frontend defaults work before missing).mono before_allowed) privateBefore prior _ reached,
    visit_stem joint selected bundle accept placeholder frontend defaults work before missing privateBefore journal message continued after reached⟩


/-- The entire actual packet visitor's first-selector continuation has one public recognized-or-packet bound. Only the original fresh-message/row cut remains to be attached by the issued finite cover. -/
theorem cut_loss {I KemSK : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (Option Found))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler setup.joint selected placeholder)
      (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore))
    (seed : PqxdhJointIdentity.IdentitySeed) (found : after.2.pool.seeds[selected]? = some seed)
    (fresh : message ∉ RegistrationNativeIdentityCensorPolicySource.messages selected after.2.pool)
    (event : Option Found → Prop) :
    Pr{let result ← ((simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued)).run after.2)}[event result.1] ≤
    Pr{let result ← (RegistrationNativeIdentityTemplateOmissionPublic.execute setup.joint (setup.joint.publicKeys seed) selected placeholder
      (Old.query (.inl (.inl (.inl (.inr message)))) >>= continued) after.1
      (RegistrationNativeIdentityTemplateFirstOmitted.install after.2) after.2.pool)}[
        RegistrationNativeIdentityTemplateOmissionPublic.Succeeds event result.1.1] := by
  obtain ⟨ready, guarded⟩ := first_cut setup.joint selected bundle accept placeholder frontend defaults work before missing privateBefore prior journal message continued after reached
  have afterNone : after.1.target = none := ready.aligned.1.trans ready.missing
  have publicFresh : message ∉ after.1.forwarded := by
    intro member
    exact fresh ((ready.aligned.2 afterNone) ▸ member)
  have chosen : RegistrationNativeIdentityCensorPolicySource.choose message after.1 = (true, {after.1 with target := some message}) := by
    simp [RegistrationNativeIdentityCensorPolicySource.choose, afterNone, publicFresh]
  exact RegistrationNativeIdentityTemplateSelectionLoss.stem_loss setup selected placeholder message seed after ready.aligned found ready.known chosen continued guarded event


private theorem erased_before (joint : Primitives) (identity : PublicIdentity) (placeholder : Ed25519Signature)
    (query : Old.Domain) (prior : RegistrationNativeIdentityTemplateSelectionPrefixScope.BeforeSelection query) :
    (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder query).AllQueriesSatisfy
      (fun query => RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity query = none) := by
  rcases query with (((protocol | selection) | scanned) | described) | marker
  · exact (allQueriesSatisfy_query_iff _ _).mpr rfl
  · exact False.elim prior
  · exact False.elim prior
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    simp only [RegistrationNativeIdentityTemplateCensorRecognition.recognize, prior.1]
  · exact False.elim prior

private theorem erased_before_program {X : Type} (joint : Primitives) (identity : PublicIdentity) (placeholder : Ed25519Signature)
    (work : OracleComp Old X) (prior : work.AllQueriesSatisfy RegistrationNativeIdentityTemplateSelectionPrefixScope.BeforeSelection) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work).AllQueriesSatisfy
      (fun query => RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity query = none) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (erased_before joint identity placeholder query first) (fun answer => ih answer (later answer))

private theorem capture_query {X W : Type} (recognize : New.Domain → Option W) (query : New.Domain)
    (next : New.Range query → OracleComp New X) :
    RegistrationNativeIdentityRecognitionCapture.capture recognize (New.query query >>= next) =
      (match recognize query with
      | some witness => pure (.inl witness)
      | none => do let answer ← New.query query
                   RegistrationNativeIdentityRecognitionCapture.capture recognize (next answer)) := rfl

private theorem capture_none {X W : Type} (recognize : New.Domain → Option W) (work : OracleComp New X)
    (prior : work.AllQueriesSatisfy (fun query => recognize query = none)) :
    RegistrationNativeIdentityRecognitionCapture.capture recognize work = Sum.inr <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp prior
    rw [capture_query, first]
    simp only [map_bind]
    exact bind_congr (fun answer => ih answer (later answer))

/-- The first-selector prefix is transparent to the literal recognition stop. All earlier physical inputs are checked retroactively only after the selected message becomes public. -/
theorem prefix_capture (joint : Primitives) (identity : PublicIdentity) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : ClientState S) (missing : before.1.2.target = none) :
    RegistrationNativeIdentityRecognitionCapture.capture (RegistrationNativeIdentityTemplateCensorRecognition.recognize joint identity)
      (RegistrationNativeIdentityTemplateSelectionCut.stop (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
        (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))) =
      Sum.inr <$> RegistrationNativeIdentityTemplateSelectionCut.stop (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
        (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before)) := by
  have erased := erased_before_program joint identity placeholder _ (first_scope selected bundle accept placeholder frontend defaults work before missing)
  have mapped := RegistrationNativeIdentityMainNoRevealCore.mapped _ (RegistrationNativeIdentityTemplateSelectionCut.Original.erased placeholder) _ erased
  rw [RegistrationNativeIdentityTemplateSelectionCut.Original.erase_stop] at mapped
  exact capture_none _ _ mapped

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.prefix_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.first_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.first_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.cut_loss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.cut_loss

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.prefix_capture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.prefix_capture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.returned_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedGame.returned_none
