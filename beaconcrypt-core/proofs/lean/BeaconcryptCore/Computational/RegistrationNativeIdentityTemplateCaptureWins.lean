-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGenuineFresh
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateRecognitionErasure
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateGuardedLateSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateIssuedForward
/-! Every captured witness from the actual fixed-message forwarded tail is valid and absent from its genuine successful signing history. The private canonical omissions do not enter that history. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins
open PqxdhJointIdentity (Primitives PublicIdentity Forgery)
open RegistrationNativeIdentityTemplateCensorRecognition (Spec recognize)
open RegistrationNativeIdentityTemplateProtocol (PublicSpec source coins)
open RegistrationNativeIdentityTemplatePolicy (Public execute)
open RegistrationNativeIdentityCensorPolicySource (messages)
open RegistrationNativeIdentityAdaptiveHashCapture (Candidate)
open RegistrationNativeIdentityCensorPacketClient (Found)
variable {A : Type}

def Forward (selected : Nat) (target : Pqxdh.Bytes) : Spec.Domain → Prop
  | .inl (.inl (.inl query)) => RegistrationNativeIdentityCensorForwardScope.ProtocolAllowed selected target query
  | _ => True

private theorem coins_safe (selected : Nat) (target : Pqxdh.Bytes) (work : ProbComp A) :
    (simulateQ coins work).AllQueriesSatisfy (RegistrationNativeIdentityTemplateGenuineFresh.Allowed selected target) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,coins,allQueriesSatisfy_query_bind_iff]
    exact ⟨trivial,ih⟩

private theorem query_forward (selected : Nat) (target : Pqxdh.Bytes) (request : Spec.Domain)
    (allowed : Forward selected target request) (before : Public) :
    ((RegistrationNativeIdentityTemplatePolicy.handler selected request).run before).AllQueriesSatisfy
      (RegistrationNativeIdentityTemplateGenuineFresh.Allowed selected target) := by
  rcases request with ((protocol | selection) | scanned) | described
  · change AllQueriesSatisfy ((PublicSpec.query (.inl protocol) : OracleComp PublicSpec _) >>= fun answer =>
        pure (answer,(RegistrationNativeIdentityCensorPolicySource.update selected protocol answer before.1,before.2))) _
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr allowed) (fun _ => allQueriesSatisfy_pure _ _)
  · exact allQueriesSatisfy_pure _ _
  · exact allQueriesSatisfy_pure _ _
  · exact RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ (coins_safe selected target _)

/-- Literal policy/hash compilation forwards no selected-target signing request from a scoped source tail. -/
theorem forward (selected : Nat) (target : Pqxdh.Bytes) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy (Forward selected target)) (before : Public) :
    ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run before).AllQueriesSatisfy
      (RegistrationNativeIdentityTemplateGenuineFresh.Allowed selected target) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    exact allQueriesSatisfy_bind (query_forward selected target request first before) (fun result => ih result.1 (later result.1) result.2)

private theorem capture_scope {W : Type} (recognizer : Spec.Domain → Option W) (work : OracleComp Spec A)
    (selected : Nat) (target : Pqxdh.Bytes) (allowed : work.AllQueriesSatisfy (Forward selected target)) :
    (RegistrationNativeIdentityRecognitionCapture.capture recognizer work).AllQueriesSatisfy (Forward selected target) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    change AllQueriesSatisfy (match recognizer request with
      | some witness => pure (.inl witness)
      | none => do let answer ← (Spec.query request : OracleComp Spec _)
                   RegistrationNativeIdentityRecognitionCapture.capture recognizer (next answer)) _
    cases recognizer request with
    | some witness => exact allQueriesSatisfy_pure _ _
    | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨first,fun answer => ih answer (later answer)⟩

/-- Recognition stops before the actual forbidden request and preserves freshness in the complete genuine source audit. -/
theorem fresh (joint : Primitives) (identity : PublicIdentity) (selected : Nat) (target : Pqxdh.Bytes)
    (work : OracleComp Spec A) (allowed : work.AllQueriesSatisfy (Forward selected target))
    (before : Public × PqxdhDynamicIdentityPool.SourceState) (prior : target ∉ messages selected before.2)
    (result : ((Candidate joint identity ⊕ A) × Public) × PqxdhDynamicIdentityPool.SourceState)
    (reached : result ∈ support (execute joint selected
      (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity) work) before)) :
    target ∉ messages selected result.2 := by
  exact RegistrationNativeIdentityTemplateGenuineFresh.program joint selected target _
    (forward selected target _ (capture_scope _ work selected target allowed) before.1) before.2 prior result reached

private theorem linked (joint : Primitives) (selected : Nat) (work : OracleComp Spec A)
    (before : Public × PqxdhDynamicIdentityPool.SourceState) :
    (simulateQ (QueryImpl.Stateful.link (RegistrationNativeIdentityTemplatePolicy.handler selected) (source joint)) work).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$> execute joint selected work before := by
  rw [QueryImpl.Stateful.simulateQ_link_run]
  rfl

def Annotated (target : Pqxdh.Bytes) : Spec.Domain → Prop
  | .inl (.inr scanned) => scanned.1=target
  | .inr described => described.message=some target
  | _ => True

private theorem recognized_message (joint : Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes)
    (request : Spec.Domain) (allowed : Annotated target request) (candidate : Candidate joint identity)
    (found : recognize joint identity request=some candidate) : candidate.1=target := by
  rcases request with ((protocol | selection) | scanned) | described
  · simp only [recognize,reduceCtorEq] at found
  · simp only [recognize,reduceCtorEq] at found
  · change scanned.1=target at allowed
    simp only [recognize,RegistrationNativeIdentityTemplateCensorRecognition.certifyScan] at found
    split at found
    · cases found
    · cases Option.some.inj found
      exact allowed
  · rcases described with ⟨message,input⟩
    change message=some target at allowed
    subst message
    cases input with
    | inl input => exact RegistrationNativeIdentityTemplateRecognitionErasure.known_message joint identity target input candidate found
    | inr frame => simp only [recognize,reduceCtorEq] at found

private theorem capture_step {X W : Type} (recognizer : Spec.Domain → Option W)
    (request : Spec.Domain) (next : Spec.Range request → OracleComp Spec X) :
    RegistrationNativeIdentityRecognitionCapture.capture recognizer ((Spec.query request : OracleComp Spec _) >>= next) =
      (match recognizer request with
      | some witness => pure (.inl witness)
      | none => do let reply ← (Spec.query request : OracleComp Spec _)
                   RegistrationNativeIdentityRecognitionCapture.capture recognizer (next reply)) := rfl

private theorem captured_message {X : Type} (joint : Primitives) (identity : PublicIdentity) (target : Pqxdh.Bytes)
    (handler : QueryImpl Spec (StateT X ProbComp)) (work : OracleComp Spec A)
    (allowed : work.AllQueriesSatisfy (Annotated target)) (before : X)
    (result : (Candidate joint identity ⊕ A) × X)
    (supported : result ∈ support ((simulateQ handler
      (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity) work)).run before)) :
    ∀ candidate,result.1=.inl candidate→candidate.1=target := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    change result ∈ support (pure (.inr value,before)) at supported
    obtain rfl := eq_of_mem_support_pure _ supported
    intro candidate same
    cases same
  | query_bind request next ih =>
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    rw [capture_step] at supported
    cases found : recognize joint identity request with
    | some witness =>
      simp only [found,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      intro candidate same
      cases same
      exact recognized_message joint identity target request first witness found
    | none =>
      simp only [found,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,_called,continued⟩ := supported
      exact ih middle.1 (later middle.1) middle.2 result continued

private theorem returned {X W : Type} (handler : QueryImpl Spec (StateT X ProbComp))
    (recognizer : Spec.Domain → Option W) (work : OracleComp Spec A) (before : X)
    (result : (W ⊕ A) × X) (reached : result ∈ support ((simulateQ handler
      (RegistrationNativeIdentityRecognitionCapture.capture recognizer work)).run before)) :
    ∀ answer, result.1=.inr answer → answer ∈ support work := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    change result ∈ support (pure (.inr value,before)) at reached
    obtain rfl := eq_of_mem_support_pure _ reached
    intro answer same
    cases Sum.inr.inj same
    exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind request next ih =>
    change result ∈ support ((simulateQ handler (match recognizer request with
      | some witness => pure (.inl witness)
      | none => do let reply ← (Spec.query request : OracleComp Spec _)
                   RegistrationNativeIdentityRecognitionCapture.capture recognizer (next reply))).run before) at reached
    cases found : recognizer request with
    | some witness =>
      simp only [found,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at reached
      cases reached
      intro answer same
      cases same
    | none =>
      simp only [found,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at reached
      obtain ⟨middle,called,continued⟩ := reached
      intro answer same
      rw [mem_support_bind_iff]
      exact ⟨middle.1,by simp only [support_query,Set.mem_univ],ih middle.1 middle.2 result continued answer same⟩

/-- Every extracted witness from an annotated forwarded tail is a valid fresh forgery of that same selected message. -/
theorem witness (joint : Primitives) (identity : PublicIdentity) (selected : Nat) (target : Pqxdh.Bytes)
    (work : OracleComp Spec (Option Found)) (allowed : work.AllQueriesSatisfy (Forward selected target))
    (annotated : work.AllQueriesSatisfy (Annotated target))
    (sameTarget : ∀ found∈support work,∀ message packet,found=some (message,packet)→message=target)
    (before : Public × PqxdhDynamicIdentityPool.SourceState) (prior : target ∉ messages selected before.2)
    (result : ((Candidate joint identity ⊕ Option Found) × Public) × PqxdhDynamicIdentityPool.SourceState)
    (reached : result ∈ support (execute joint selected
      (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity) work) before))
    (candidate : RegistrationNativeIdentityTemplateLateIdentity.Witness)
    (extracted : RegistrationNativeIdentityTemplateLateIdentity.raw joint identity result.1.1=some candidate) :
    candidate.1=identity ∧ candidate.2.message=target ∧
      joint.verify identity.ed25519 candidate.2.message candidate.2.signature=true ∧
        candidate.2.message ∉ messages selected result.2 := by
  have noSign := fresh joint identity selected target work allowed before prior result reached
  have sourceReached : (result.1.1,(result.1.2,result.2)) ∈ support
      ((simulateQ (QueryImpl.Stateful.link (RegistrationNativeIdentityTemplatePolicy.handler selected) (source joint))
        (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity) work)).run before) := by
    rw [linked,support_map]
    exact ⟨result,reached,rfl⟩
  cases value : result.1.1 with
  | inl chosen =>
    have message := captured_message joint identity target _ work annotated before _ sourceReached chosen value
    simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,value,Option.some.injEq] at extracted
    cases extracted
    exact ⟨rfl,message,chosen.2.property,message ▸ noSign⟩
  | inr found =>
    have present := returned _ (recognize joint identity) work before _ sourceReached found value
    cases found with
    | none => simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,value,RegistrationNativeIdentityCensorPacketClient.candidate,Option.bind_none,Option.map_none,reduceCtorEq] at extracted
    | some found =>
      rcases found with ⟨message,packet⟩
      have messageEq := sameTarget _ present message packet rfl
      simp only [RegistrationNativeIdentityTemplateLateIdentity.raw,value,RegistrationNativeIdentityCensorPacketClient.candidate,Option.bind_some] at extracted
      rw [Option.map_eq_some_iff] at extracted
      obtain ⟨chosen,selected,same⟩ := extracted
      have chosenMessage := RegistrationNativeIdentityCensorStoppedReduction.choose_target joint identity message _ chosen selected
      cases same
      exact ⟨rfl,chosenMessage.trans messageEq,chosen.2.property,(chosenMessage.trans messageEq) ▸ noSign⟩

private theorem erased_forward_query (selected : Nat) (target : Pqxdh.Bytes)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (request : RegistrationNativeIdentityCensorOperational.Spec.Domain)
    (allowed : RegistrationNativeIdentityCensorForwardScope.Allowed selected target request) :
    (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder request).AllQueriesSatisfy (Forward selected target) := by
  rcases request with (((protocol | selection) | scanned) | described) | marker
  · exact (allQueriesSatisfy_query_iff _ _).mpr allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · cases marker with
    | omitted handle message => exact allQueriesSatisfy_pure _ _
    | template handle message leading trailing => exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem erased_forward (selected : Nat) (target : Pqxdh.Bytes)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A)
    (allowed : work.AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected target)) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work).AllQueriesSatisfy (Forward selected target) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind,simulateQ_spec_query]
    exact allQueriesSatisfy_bind (erased_forward_query selected target placeholder request first) (fun answer => ih answer (later answer))

private theorem erased_member (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A) (value : A)
    (present : value ∈ support (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure answer =>
    simp only [simulateQ_pure,mem_support_pure_iff] at present
    exact (mem_support_pure_iff _ _).mpr present
  | query_bind request next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,mem_support_bind_iff] at present
    obtain ⟨answer,_called,later⟩ := present
    rw [mem_support_bind_iff]
    exact ⟨answer,by simp only [support_query,Set.mem_univ],ih answer later⟩

private theorem annotation_mono (target : Pqxdh.Bytes) (request : Spec.Domain)
    (allowed : RegistrationNativeIdentityTemplateRecognitionErasure.ErasedAllowed target request) : Annotated target request := by
  rcases request with ((protocol | selection) | scanned) | described
  · trivial
  · trivial
  · exact False.elim allowed
  · exact allowed

/-- The literal reached first-selector suffix derives all freshness and target scopes required of candidate extraction; no desired forgery event is a premise. -/
theorem actual_scope {S V : Type} (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target=none)
    (privateBefore : RegistrationNativeIdentityTemplateVisitorProbability.Private)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (message : Pqxdh.Bytes)
    (continued : Bool → OracleComp RegistrationNativeIdentityCensorOperational.Spec (Option Found))
    (after : RegistrationNativeIdentityTemplateVisitorProbability.Private)
    (reached : (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued,after) ∈ support
      ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
        (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
          (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore)) :
    let code := simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (continued true)
    code.AllQueriesSatisfy (Forward selected message) ∧
      code.AllQueriesSatisfy (Annotated message) ∧
        ∀ found∈support code,∀ target packet,found=some (target,packet)→target=message := by
  dsimp only
  have sourceScope := (RegistrationNativeIdentityTemplateIssuedGame.first_cut joint selected bundle accept placeholder frontend defaults work before missing
    privateBefore prior journal message continued after reached).2
  obtain ⟨rest,body,safe⟩ := sourceScope
  have actualForward := RegistrationNativeIdentityTemplateIssuedForward.cut joint selected bundle accept placeholder frontend defaults work before missing
    privateBefore journal message continued after reached
  obtain ⟨forwardRest,forwardBody,forwardSafe⟩ := actualForward
  have forwardAll : (continued true).AllQueriesSatisfy (RegistrationNativeIdentityCensorForwardScope.Allowed selected message) := by
    rw [forwardBody]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ =>
      allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun answer => (forwardSafe answer).1))
  refine ⟨erased_forward selected message placeholder _ forwardAll,?_,?_⟩
  · rw [body]
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativeIdentityTemplateCensorRecognition.erase,pure_bind]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ =>
      (RegistrationNativeIdentityTemplateRecognitionErasure.erased_scope selected message placeholder _ (safe (some placeholder)).2).mono
        (annotation_mono message))
  · intro found present target packet same
    have original := erased_member placeholder (continued true) found present
    rw [forwardBody,mem_support_bind_iff] at original
    obtain ⟨_scanned,_scanCalled,original⟩ := original
    rw [mem_support_bind_iff] at original
    obtain ⟨answer,_omittedCalled,restReached⟩ := original
    exact (forwardSafe answer).2 found restReached target packet same

/-- A positive actual public selector gives genuine weak-EUF freshness for every returned candidate of its retained source continuation. Freshness is derived at that same cut from the public successful-reply policy. -/
theorem actual_witness {S V : Type} (joint : Primitives) (selected bundle accept : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V)
    (before : RegistrationNativeIdentityCensorPublicClient.ClientState S) (missing : before.1.2.target=none)
    (privateBefore : RegistrationNativeIdentityTemplateVisitorProbability.Private)
    (prior : RegistrationNativeIdentityTemplateSelectionSource.Ready selected privateBefore)
    (journal : RegistrationNativeIdentityCensorPrefixJournal.Aligned before.1.2 privateBefore.2)
    (message : Pqxdh.Bytes)
    (continued : Bool → OracleComp RegistrationNativeIdentityCensorOperational.Spec (Option Found))
    (after : RegistrationNativeIdentityTemplateVisitorProbability.Private)
    (reached : (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued,after) ∈ support
      ((simulateQ (RegistrationNativeIdentityCensorPolicySource.handler joint selected placeholder)
        (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
          (RegistrationNativeIdentityCensorPacketClient.visit selected bundle accept placeholder frontend defaults work before))).run privateBefore))
    (identity : PublicIdentity) (picked : RegistrationNativeIdentityAdaptiveCensor.Policy)
    (choice : RegistrationNativeIdentityCensorPolicySource.choose message after.1=(true,picked))
    (hash : RegistrationNativeIdentityReindexedCtx.State RegistrationNativeIdentityTemplateAddress.Key)
    (result : ((Candidate joint identity ⊕ Option Found) × Public) × PqxdhDynamicIdentityPool.SourceState)
    (observed : result ∈ support (execute joint selected
      (RegistrationNativeIdentityRecognitionCapture.capture (recognize joint identity)
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) (continued true)))
      ((picked,hash),after.2.pool)))
    (candidate : RegistrationNativeIdentityTemplateLateIdentity.Witness)
    (extracted : RegistrationNativeIdentityTemplateLateIdentity.raw joint identity result.1.1=some candidate) :
    candidate.1=identity ∧ candidate.2.message=message ∧
      PqxdhJointIdentity.wins joint identity candidate.2
        (RegistrationNativeIdentityHistory.history selected result.2.transcript)=true := by
  have ready := (RegistrationNativeIdentityTemplateIssuedGame.first_cut joint selected bundle accept placeholder frontend defaults work before missing
    privateBefore prior journal message continued after reached).1
  have eligible : after.1.target=none ∧ message ∉ after.1.forwarded := by
    by_cases eligible : after.1.target=none ∧ message ∉ after.1.forwarded
    · exact eligible
    · simp only [RegistrationNativeIdentityCensorPolicySource.choose,eligible,ite_false,Prod.mk.injEq,Bool.false_eq_true,false_and] at choice
  have originalFresh : message ∉ messages selected after.2.pool := by
    simpa only [ready.aligned.2 eligible.1] using eligible.2
  obtain ⟨forwarded,annotated,sameTarget⟩ := actual_scope joint selected bundle accept placeholder frontend defaults work before missing
    privateBefore prior journal message continued after reached
  have witnessFact := witness joint identity selected message _ forwarded annotated sameTarget ((picked,hash),after.2.pool) originalFresh
    result observed candidate extracted
  refine ⟨witnessFact.1,witnessFact.2.1,?_⟩
  have noHistory : candidate.2.message ∉ PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected result.2.transcript) := witnessFact.2.2.2
  simp [PqxdhJointIdentity.wins,witnessFact.2.2.1,noHistory]

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.forward
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.witness

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.actual_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.actual_scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.actual_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCaptureWins.actual_witness
