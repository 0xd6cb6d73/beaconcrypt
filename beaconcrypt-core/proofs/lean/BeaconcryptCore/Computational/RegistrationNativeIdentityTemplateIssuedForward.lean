-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorForward
/-! The actual whole before-accept visitor's first positive selector tail forwards no genuine target signature request and preserves the exact target in every returned packet. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedForward
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhEd25519EufCma (Ed25519Signature)
open PqxdhJointIdentity (Primitives)
open RegistrationNativeIdentityCensorPacketClient (Found)
open RegistrationNativeIdentityCensorPublicClient (ClientState)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
open RegistrationNativeIdentityTemplateSelectionCut.Original (Cut stop)
variable {S A : Type}

private def Tail (selected : Nat) (message : Pqxdh.Bytes) (work : OracleComp Old (Option Found)) : Prop :=
  work.AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) ∧
    ∀ found∈support work,∀ target packet,found=some (target,packet)→target=message
private def Stem (selected : Nat) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old (Option Found)) : Prop :=
  ∃ rest : Option Ed25519Signature → OracleComp Old (Option Found),
    continued true=(do let _ ← Old.query (.inl (.inl (.inr (message,inputs))))
                       let answer ← Old.query (.inr (.omitted selected message))
                       rest answer) ∧ ∀ answer,Tail selected message (rest answer)

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

private theorem visit_query (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : ClientState S) :
    RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (TypedSpec.query query >>= next) before = (do
      let result ← (RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults query).run before
      match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before result.1 result.2 with
      | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next result.1) result.2
      | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason)) := rfl

private def joined (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : ClientState S) (current : (TypedSpec.Range query × S) × Mode) : OracleComp Old (Option Found) :=
  let after : ClientState S := ((current.1.2, current.2), before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
  match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
  | none => RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) after
  | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason)

private theorem joined_tail (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : ClientState S) (message : Pqxdh.Bytes) (current : (TypedSpec.Range query × S) × Mode)
    (held : current.2.target=some message) :
    Tail selected message (joined selected bundle accept placeholder frontend defaults query next before current) := by
  let after : ClientState S := ((current.1.2,current.2),before.2+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)
  change Tail selected message (match RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
    | none=>RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults (next current.1.1) after
    | some reason=>pure (RegistrationNativeIdentityCensorPacketClient.finish current.2.target reason))
  cases RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept query before current.1.1 after with
  | none=>exact ⟨RegistrationNativeIdentityTemplateVisitorForward.visit selected bundle accept placeholder frontend defaults (next current.1.1) message after held,
      RegistrationNativeIdentityTemplateVisitorForward.returned selected bundle accept placeholder frontend defaults (next current.1.1) message after held⟩
  | some reason=>
      refine ⟨allQueriesSatisfy_pure _ _,?_⟩
      intro found reached target packet same
      obtain rfl := eq_of_mem_support_pure _ reached
      rw [held] at same
      cases reason with
      | published=>cases same
      | attempted original reply=>exact (Prod.mk.inj (Option.some.inj same)).1.symm

private theorem joined_stem (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : ClientState S) (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes)
    (continued : Bool → OracleComp Old ((TypedSpec.Range query × S) × Mode))
    (prior : RegistrationNativeIdentityTemplateSelectionPrefixScope.ForwardStem selected message inputs continued) :
    Stem selected message inputs (fun reply=>continued reply >>= joined selected bundle accept placeholder frontend defaults query next before) := by
  obtain ⟨rest,body,safe⟩ := prior
  refine ⟨fun answer=>rest answer >>= joined selected bundle accept placeholder frontend defaults query next before,?_,?_⟩
  · simpa only [bind_assoc] using congrArg (fun code=>code >>= joined selected bundle accept placeholder frontend defaults query next before) body
  · intro answer
    refine ⟨bind_scoped _ _ _ (safe answer).1 ?_,?_⟩
    · intro current reached
      exact (joined_tail selected bundle accept placeholder frontend defaults query next before message current ((safe answer).2 current reached)).1
    · intro found reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨current,called,continued⟩ := reached
      exact (joined_tail selected bundle accept placeholder frontend defaults query next before message current ((safe answer).2 current called)).2 found continued

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


/-- The actual first-selector continuation retains its scan/omission prefix and excludes every later genuine signing request for the selected target. -/
theorem cut (joint : Primitives) (selected bundle accept : Nat) (placeholder : Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : ClientState S) (missing : before.1.2.target = none)
    (privateBefore : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (message : Pqxdh.Bytes) (continued : Bool → OracleComp Old (Option Found))
    (after : RegistrationNativeIdentityAdaptiveCensor.Policy × RegistrationNativeIdentityCensorSource.State)
    (reached : (Cut.selected message continued, after) ∈ support ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
      (stop (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore)) :
    ∃ rest : Option Ed25519Signature → OracleComp Old (Option Found),
      continued true=(do let _ ← Old.query (.inl (.inl (.inr (message,after.2.hash.2))))
                         let answer ← Old.query (.inr (.omitted selected message))
                         rest answer) ∧ ∀ answer,
        (rest answer).AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) ∧
          ∀ found∈support (rest answer),∀ target packet,found=some (target,packet)→target=message := by
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
        exact RegistrationNativeIdentityTemplateSelectionPrefixScope.program_forward_stem joint selected placeholder ((frontend query).run before.1.1)
          (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) (enter_none bundle query before.1.2 missing)
          privateBefore (enter_journal bundle query before.1.2 privateBefore.2 journal) message body after called


end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedForward

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedForward.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedForward.cut
