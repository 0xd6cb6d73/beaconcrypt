-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateErasure
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTargetSync
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource

/-! The source selector can use an executable record of actual successful indexed signing replies. Exact signing-history equality is needed only before selection; canonical omitted attempts remain private afterward and never become challenger calls. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource
open RegistrationNativeIdentityAdaptiveCensor (Policy)
open RegistrationNativeIdentityCensorCompiler (Mode)
open PqxdhDynamicIdentityPool (SourceState DynamicSpec)
open PqxdhJointPhase1Reports (ProtocolSpec)
open RegistrationNativeIdentityCensorSource (State)
variable {Value : Type}

def messages (selected : Nat) (before : SourceState) : List Pqxdh.Bytes :=
  PqxdhJointIdentity.signedMessages (RegistrationNativeIdentityHistory.history selected before.transcript)

/-- Only a literal successful selected-handle signing reply enters the executable forwarding history. Failed attempts and every other request are retained by the source but add no signing message. -/
def newMessage (selected : Nat) : (query : ProtocolSpec.Domain) → ProtocolSpec.Range query → Option Pqxdh.Bytes
  | .inl (.inr (.service handle (.sign message))), answer => if handle = selected then answer.map (fun _ => message) else none
  | _, _ => none

def update (selected : Nat) (query : ProtocolSpec.Domain) (answer : ProtocolSpec.Range query) (before : Policy) : Policy :=
  {before with forwarded := before.forwarded ++ (newMessage selected query answer).toList}

def choose (message : Pqxdh.Bytes) (before : Policy) : Bool × Policy :=
  if before.target = none ∧ message ∉ before.forwarded then (true, {before with target := some message}) else (false, before)

def Aligned (selected : Nat) (before : Policy × State) : Prop :=
  before.1.target = before.2.target ∧ (before.1.target = none → before.1.forwarded = messages selected before.2.pool)

private theorem record_messages (selected : Nat) (query : DynamicSpec.Domain) (answer : DynamicSpec.Range query) (before : SourceState) :
    messages selected (PqxdhDynamicIdentityPool.record query answer before) =
      messages selected before ++ (newMessage selected (.inl query) answer).toList := by
  cases query with
  | inl coin => simp [messages, PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityHistory.history,
      RegistrationNativeIdentityHistory.entry, PqxdhJointIdentity.signedMessages, newMessage, List.filterMap_append]
  | inr query => cases query with
    | create => simp [messages, PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityHistory.history,
        RegistrationNativeIdentityHistory.entry, PqxdhJointIdentity.signedMessages, newMessage, List.filterMap_append]
    | reveal handle => simp [messages, PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityHistory.history,
        RegistrationNativeIdentityHistory.entry, PqxdhJointIdentity.signedMessages, newMessage, List.filterMap_append]
    | service handle request =>
      by_cases same : handle = selected
      · subst handle
        cases request <;> cases answer <;>
          simp [messages, PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityHistory.history,
            RegistrationNativeIdentityHistory.entry, PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent,
            newMessage, List.filterMap_append]
      · cases request <;> cases answer <;>
          simp [messages, PqxdhDynamicIdentityPool.record, RegistrationNativeIdentityHistory.history,
            RegistrationNativeIdentityHistory.entry, PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent,
            newMessage, List.filterMap_append, same]

/-- Every actual ordinary protocol reply updates successful message history exactly as its executable optional-reply recorder. Creation and rejected handles add no message. -/
theorem protocol_messages (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (query : ProtocolSpec.Domain)
    (before : SourceState) (result : ProtocolSpec.Range query × SourceState)
    (supported : result ∈ support ((RegistrationNativeIdentityMainSource.implementation joint query).run before)) :
    messages selected result.2 = messages selected before ++ (newMessage selected query result.1).toList := by
  cases query with
  | inr report =>
    simp only [RegistrationNativeIdentityMainSource.implementation, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    simp only [newMessage, Option.toList_none, List.append_nil]
  | inl query => cases query with
    | inl coin =>
      simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
        PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨answer, _sampled, returned⟩ := supported
      obtain rfl := eq_of_mem_support_pure _ returned
      exact record_messages selected (.inl coin) answer before
    | inr query => cases query with
      | create =>
        simp only [RegistrationNativeIdentityMainSource.implementation] at supported
        rw [PqxdhDynamicIdentityPool.lazyImpl_create, support_map] at supported
        obtain ⟨seed, _sampled, rfl⟩ := supported
        simp [PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record, messages,
          RegistrationNativeIdentityHistory.history, RegistrationNativeIdentityHistory.entry,
          PqxdhJointIdentity.signedMessages, newMessage, List.filterMap_append]
      | service handle request =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        exact record_messages selected (.inr (.service handle request)) _ before
      | reveal handle =>
        simp only [RegistrationNativeIdentityMainSource.implementation, PqxdhDynamicIdentityPool.lazyImpl,
          PqxdhDynamicIdentityPool.poolImpl, StateT.run, mem_support_pure_iff] at supported
        cases supported
        exact record_messages selected (.inr (.reveal handle)) _ before

/-- The public successful-reply recorder matches the source's private successful history for as long as no target has been chosen. -/
theorem protocol (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (query : ProtocolSpec.Domain)
    (before : Policy × State) (prior : Aligned selected before)
    (result : ProtocolSpec.Range query × State)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.protocol joint query).run before.2)) :
    Aligned selected (update selected query result.1 before.1, result.2) := by
  simp only [RegistrationNativeIdentityCensorSource.protocol, StateT.run, support_map] at supported
  obtain ⟨actual, called, rfl⟩ := supported
  refine ⟨prior.1, ?_⟩
  intro none
  have same := protocol_messages joint selected query before.2.pool actual called
  change before.1.forwarded ++ (newMessage selected query actual.1).toList = messages selected actual.2
  rw [same, prior.2 none]

private theorem eligibility (selected : Nat) (message : Pqxdh.Bytes) (before : Policy × State) (prior : Aligned selected before) :
    (before.2.target = none ∧ message ∉ messages selected before.2.pool) ↔
      (before.1.target = none ∧ message ∉ before.1.forwarded) := by
  constructor
  · rintro ⟨missing, fresh⟩
    have publicNone := prior.1.trans missing
    exact ⟨publicNone, by simpa only [prior.2 publicNone] using fresh⟩
  · rintro ⟨missing, fresh⟩
    exact ⟨prior.1.symm.trans missing, by simpa only [← prior.2 missing] using fresh⟩

def afterSelection (message : Pqxdh.Bytes) (chosen : Bool) (before : State) : State :=
  if chosen then {before with target := some message, canonical := none, framing := none} else before

/-- The literal private source selector returns exactly the public policy's computable choice; no selected row, canonical reply or success premise is supplied. -/
theorem select_source (selected : Nat) (message : Pqxdh.Bytes) (before : Policy × State) (prior : Aligned selected before) :
    (RegistrationNativeIdentityCensorSource.select selected message).run before.2 =
      pure ((choose message before.1).1, afterSelection message (choose message before.1).1 before.2) := by
  have equivalent := eligibility selected message before prior
  by_cases chosen : before.1.target = none ∧ message ∉ before.1.forwarded
  · have actual := equivalent.mpr chosen
    simp only [messages] at actual
    simp [RegistrationNativeIdentityCensorSource.select, StateT.run, choose, afterSelection, actual, chosen]
  · have denied : ¬(before.2.target = none ∧ message ∉ messages selected before.2.pool) := fun accepted => chosen (equivalent.mp accepted)
    simp only [messages] at denied
    simp [RegistrationNativeIdentityCensorSource.select, StateT.run, choose, afterSelection, denied, chosen]

/-- Actual selection preserves the precise conditional history relation. Once selected, no equality with privately appended canonical omitted receipts is required. -/
theorem select_aligned (selected : Nat) (message : Pqxdh.Bytes) (before : Policy × State) (prior : Aligned selected before)
    (result : Bool × State) (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.select selected message).run before.2)) :
    result.1 = (choose message before.1).1 ∧ Aligned selected ((choose message before.1).2, result.2) := by
  rw [select_source selected message before prior, mem_support_pure_iff] at supported
  cases supported
  refine ⟨rfl, ?_⟩
  unfold choose
  split
  · exact ⟨rfl, by intro impossible; cases impossible⟩
  · exact prior

def observe (selected : Nat) : (query : RegistrationNativeIdentityCensorOperational.Spec.Domain) →
    RegistrationNativeIdentityCensorOperational.Spec.Range query → Policy → Policy
  | .inl (.inl (.inl (.inl query))), answer, before => update selected query answer before
  | query, answer, before => {before with target := RegistrationNativeIdentityCensorTargetSync.targetAfter query answer before.target}

private theorem observe_select (selected : Nat) (message : Pqxdh.Bytes) (reply : Bool) (before : Policy) :
    observe selected (.inl (.inl (.inl (.inr message)))) reply before =
      {before with target := cond reply (some message) before.target} := by
  cases reply <;> rfl

/-- Only malformed standalone omitted markers would require a preselection audit relation after a private signature was added. The literal lowering emits its omissions only after selecting a target. -/
def MarkerReady (before : State) : RegistrationNativeIdentityCensorOperational.Spec.Domain → Prop
  | .inr (.omitted _ _) => before.target ≠ none
  | _ => True

/-- Each actual source observation preserves the public conditional-history record. The marker condition is local to the omission call, not a global source-security premise. -/
theorem step (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (query : RegistrationNativeIdentityCensorOperational.Spec.Domain) (before : Policy × State) (prior : Aligned selected before)
    (ready : MarkerReady before.2 query)
    (result : RegistrationNativeIdentityCensorOperational.Spec.Range query × State)
    (supported : result ∈ support ((RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run before.2)) :
    Aligned selected (observe selected query result.1 before.1, result.2) := by
  rcases query with (((request | message) | scanned) | described) | marker
  · exact protocol joint selected request before prior result supported
  · have actual := select_aligned selected message before prior result supported
    have after : observe selected (.inl (.inl (.inl (.inr message)))) result.1 before.1 = (choose message before.1).2 := by
      rw [actual.1, observe_select]
      unfold choose
      split <;> rfl
    rw [after]
    exact actual.2
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  · simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
      RegistrationNativeIdentityCensorSource.physical, StateT.run, support_map] at supported
    obtain ⟨actual, _called, rfl⟩ := supported
    exact prior
  · cases marker with
    | template handle message leading trailing =>
      simp only [RegistrationNativeIdentityCensorSource.censored, RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.template, RegistrationNativeIdentityCensorSource.physical,
        StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨actual, _called, rfl⟩ := supported
      exact prior
    | omitted handle message =>
      have targetEq := RegistrationNativeIdentityCensorTargetSync.censored_step joint selected placeholder
        (.inr (.omitted handle message)) before.2 result supported
      change result.2.target = before.2.target at targetEq
      refine ⟨prior.1.trans targetEq.symm, ?_⟩
      intro impossible
      exact False.elim (ready (prior.1.symm.trans impossible))

/-- The actual source starts with no indexed signing history and the public selector's empty forwarding policy, preserving the literal warm physical state. -/
theorem initialized (selected : Nat) (physical : RegistrationNativePlatformCtxBackend.State) :
    Aligned selected (({} : Policy), ({pool := PqxdhDynamicIdentityPool.initialState, hash := physical} : State)) := by
  exact ⟨rfl, by intro _missing; rfl⟩

abbrev OpSpec := RegistrationNativeIdentityCensorOperational.Spec

/-- This source observer adds only the public forwarding policy; seed rows and canonical signing remain in the unchanged private backend. -/
noncomputable def handler (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) : QueryImpl OpSpec (StateT (Policy × State) ProbComp) := fun query before =>
  (fun result => (result.1, (observe selected query result.1 before.1, result.2))) <$>
    (RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run before.2

private theorem handler_erasure (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (query : OpSpec.Domain) (before : Policy × State) :
    Prod.map id Prod.snd <$> (handler joint selected placeholder query).run before =
      (RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run before.2 := by
  simp only [handler, StateT.run, Functor.map_map, Prod.map_def, id_eq, Prod.eta]
  rw [show (fun value : OpSpec.Range query × State => value) = id from rfl, id_map]

/-- Erasing only the added public forwarding policy retains the complete actual private source distribution, including warm physical cache and all canonical observations. -/
theorem program_erasure (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp OpSpec Value) (before : Policy × State) :
    Prod.map id Prod.snd <$> (simulateQ (handler joint selected placeholder) work).run before =
      (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (handler_erasure joint selected placeholder) work before

private theorem handler_target (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (query : OpSpec.Domain) (before : Policy × State)
    (result : OpSpec.Range query × (Policy × State))
    (supported : result ∈ support ((handler joint selected placeholder query).run before)) :
    result.2.2.target = RegistrationNativeIdentityCensorTargetSync.targetAfter query result.1 before.2.target := by
  change result ∈ support ((fun actual : OpSpec.Range query × State => (actual.1, (observe selected query actual.1 before.1, actual.2))) <$>
    (RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨actual, called, rfl⟩ := supported
  exact RegistrationNativeIdentityCensorTargetSync.censored_step joint selected placeholder query before.2 actual called

private theorem handler_aligned (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (query : OpSpec.Domain) (before : Policy × State)
    (prior : Aligned selected before) (ready : MarkerReady before.2 query)
    (result : OpSpec.Range query × (Policy × State))
    (supported : result ∈ support ((handler joint selected placeholder query).run before)) : Aligned selected result.2 := by
  change result ∈ support ((fun actual : OpSpec.Range query × State => (actual.1, (observe selected query actual.1 before.1, actual.2))) <$>
    (RegistrationNativeIdentityCensorSource.censored joint selected placeholder query).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨actual, called, rfl⟩ := supported
  exact step joint selected placeholder query before prior ready actual called

private def NoOmitted : OpSpec.Domain → Prop
  | .inr (.omitted _ _) => False
  | _ => True

private theorem ready_of_noOmitted (before : State) (query : OpSpec.Domain) (allowed : NoOmitted query) : MarkerReady before query := by
  cases query with
  | inl query => cases query <;> trivial
  | inr marker => cases marker with
    | template handle message leading trailing => trivial
    | omitted handle message => exact False.elim allowed

private theorem noOmitted_aligned (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp OpSpec Value)
    (allowed : work.AllQueriesSatisfy NoOmitted) (before : Policy × State) (prior : Aligned selected before)
    (result : Value × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder) work).run before)) : Aligned selected result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind request next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, rest⟩ := supported
    exact ih middle.1 (later middle.1) middle.2
      (handler_aligned joint selected placeholder request before prior (ready_of_noOmitted before.2 request first) middle called) result rest

private theorem bind_apply {Local A B : Type} {m : Type → Type} [Monad m]
    (work : StateT Local m A) (next : A → StateT Local m B) (before : Local) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {Local A : Type} {m : Type → Type} [Monad m] (value : A) (before : Local) :
    (pure value : StateT Local m A) before = pure (value, before) := rfl

private theorem embed_noOmitted {A : Type} (work : OracleComp RegistrationNativeIdentityCensorCompiler.Spec A) :
    (simulateQ RegistrationNativeIdentityCensorOperational.embed work).AllQueriesSatisfy NoOmitted := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem prepare_sync (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (message : Pqxdh.Bytes)
    (mode : Mode) (before : Policy × State) (prior : mode.target = before.2.target)
    (result : (Unit × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode)).run before)) :
    result.1.2.target = result.2.2.target := by
  simp only [RegistrationNativeIdentityCensorOperational.promote, RegistrationNativeIdentityCensorCompiler.prepare,
    StateT.run] at supported
  split at supported
  · split at supported
    · simp only [RegistrationNativeIdentityCensorCompiler.select, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed, bind_apply, mem_support_bind_iff] at supported
      obtain ⟨chosen, called, rest⟩ := supported
      have step := handler_target joint selected placeholder (.inl (.inl (.inl (.inr message)))) before chosen called
      cases chosenReply : chosen.1 with
      | false =>
        simp only [chosenReply, Bool.false_eq_true, ite_false, simulateQ_pure, pure_apply, mem_support_pure_iff] at rest
        cases rest
        exact prior.trans (by simpa only [RegistrationNativeIdentityCensorTargetSync.targetAfter, chosenReply, Bool.cond_false] using step.symm)
      | true =>
        simp only [chosenReply, ite_true, RegistrationNativeIdentityCensorCompiler.inspect,
          simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
          simulateQ_pure, bind_apply, pure_apply, mem_support_bind_iff] at rest
        obtain ⟨inspected, calledInspect, returned⟩ := rest
        obtain rfl := eq_of_mem_support_pure _ returned
        have inspectStep := handler_target joint selected placeholder (.inl (.inl (.inr (message, mode.knownInputs)))) chosen.2 inspected calledInspect
        have selectedTarget : some message = chosen.2.2.target := by
          simpa only [RegistrationNativeIdentityCensorTargetSync.targetAfter, chosenReply, Bool.cond_true] using step.symm
        exact selectedTarget.trans inspectStep.symm
    · simp only [pure_bind, Bool.false_eq_true, ite_false, simulateQ_pure, pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact prior
  · simp only [simulateQ_pure, pure_apply, mem_support_pure_iff] at supported
    cases supported
    exact prior

private theorem prepare_aligned (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (message : Pqxdh.Bytes) (mode : Mode)
    (before : Policy × State) (prior : Aligned selected before) (result : (Unit × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode)).run before)) :
    Aligned selected result.2 := by
  exact noOmitted_aligned joint selected placeholder _ (embed_noOmitted _) before prior result supported

private theorem constant_aligned (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (request : OpSpec.Domain) (mode : Mode)
    (before : Policy × State) (prior : Aligned selected before) (ready : MarkerReady before.2 request)
    (result : (OpSpec.Range request × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      (do let reply ← OpSpec.query request; pure (reply, mode))).run before)) : Aligned selected result.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨actual, called, rest⟩ := supported
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at rest
  cases rest
  exact handler_aligned joint selected placeholder request before prior ready actual called

private theorem signing_aligned (joint : PqxdhJointIdentity.Primitives) (selected handle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (message : Pqxdh.Bytes) (mode : Mode)
    (before : Policy × State) (prior : Aligned selected before) (synced : mode.target = before.2.target)
    (result : (Option PqxdhEd25519EufCma.Ed25519Signature × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode)).run before)) : Aligned selected result.2 := by
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind,
    simulateQ_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, called, rest⟩ := supported
  have aligned := prepare_aligned joint selected handle placeholder message mode before prior prepared called
  have same := prepare_sync joint selected handle placeholder message mode before synced prepared called
  simp only [StateT.run_get, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, exists_eq_left] at rest
  split at rest
  · rename_i suppressed
    have ready : MarkerReady prepared.2.2 (.inr (.omitted handle message)) := by
      change prepared.2.2.target ≠ none
      rw [← same, suppressed.2]
      exact Option.some_ne_none message
    exact constant_aligned joint selected placeholder (.inr (.omitted handle message)) prepared.1.2 prepared.2 aligned ready result rest
  · exact constant_aligned joint selected placeholder
      (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message))))))))
      prepared.1.2 prepared.2 aligned True.intro result rest

private def Nonsign : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain → Prop
  | .inl (.inl (.inr (.service _ (.sign _)))) => False
  | _ => True

private theorem nonsign_safe (selected : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain) (allowed : Nonsign request) (mode : Mode) :
    ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode).AllQueriesSatisfy NoOmitted := by
  rcases request with ((coin | query) | report) | bytes
  · exact embed_noOmitted _
  · cases query with
    | create | reveal handle => exact embed_noOmitted _
    | service handle request => cases request with
      | staticDh peer => exact embed_noOmitted _
      | sign message => exact False.elim allowed
  · exact embed_noOmitted _
  · change (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => simulateQ RegistrationNativeIdentityCensorOperational.embed
          ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run mode)
      | none => do let reply ← OpSpec.query (.inr (.template selected mode.target
          (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2))
                   pure (reply, mode)).AllQueriesSatisfy NoOmitted
    cases (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
    | some input => exact embed_noOmitted _
    | none => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, fun _ => trivial⟩

/-- Every actual lower Ctx request derives the omission-stage condition internally and preserves the public selector/history relation, including first selection from none. -/
theorem lower_query (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain)
    (mode : Mode) (before : Policy × State) (prior : Aligned selected before) (synced : mode.target = before.2.target)
    (result : (RegistrationNativePlatformIdentityCtxCompiler.Spec.Range request × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)).run before)) :
    Aligned selected result.2 := by
  by_cases nonsign : Nonsign request
  · exact noOmitted_aligned joint selected placeholder _ (nonsign_safe selected placeholder request nonsign mode) before prior result supported
  · rcases request with ((coin | query) | report) | bytes
    · exact False.elim (nonsign True.intro)
    · cases query with
      | create | reveal handle => exact False.elim (nonsign True.intro)
      | service handle request => cases request with
        | staticDh peer => exact False.elim (nonsign True.intro)
        | sign message => exact signing_aligned joint selected handle placeholder message mode before prior synced result supported
    · exact False.elim (nonsign True.intro)
    · exact False.elim (nonsign True.intro)

private theorem lower_synced (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (request : RegistrationNativePlatformIdentityCtxCompiler.Spec.Domain)
    (mode : Mode) (before : Policy × State) (prior : mode.target = before.2.target)
    (result : (RegistrationNativePlatformIdentityCtxCompiler.Spec.Range request × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)).run before)) :
    result.1.2.target = result.2.2.target := by
  have actual : (result.1, result.2.2) ∈ support ((simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode)).run before.2) := by
    rw [← program_erasure joint selected placeholder _ before, support_map]
    exact ⟨result, supported, rfl⟩
  apply RegistrationNativeIdentityCensorTargetSync.lower_query joint selected placeholder true request mode before.2 prior (result.1, result.2.2)
  simpa only [RegistrationNativeIdentityCensorTargetSync.lower, ite_true] using actual

/-- The complete actual lower source tree derives both target synchronization and the public preselection-history relation through first selection and every later canonical omitted attempt. -/
theorem lower_program (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec Value)
    (mode : Mode) (before : Policy × State) (prior : Aligned selected before) (synced : mode.target = before.2.target)
    (result : (Value × Mode) × (Policy × State))
    (supported : result ∈ support ((simulateQ (handler joint selected placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before)) :
    Aligned selected result.2 ∧ result.1.2.target = result.2.2.target := by
  induction work using OracleComp.inductionOn generalizing mode before result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact ⟨prior, synced⟩
  | query_bind request next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, rest⟩ := supported
    exact ih middle.1.1 middle.1.2 middle.2
      (lower_query joint selected placeholder request mode before prior synced middle called)
      (lower_synced joint selected placeholder request mode before synced middle called) result rest

private theorem map_apply {Local A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT Local m A) (before : Local) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

section Callback
open RegistrationNativeRawAdapter (TypedSpec)
variable {S : Type}
abbrev Whole (S : Type) := (S × Mode) × (Policy × State)

noncomputable def callbacks (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec))) :
    QueryImpl TypedSpec (StateT (Whole S) ProbComp) :=
  RegistrationNativeIdentityCensorPublicSource.callback (handler joint selected placeholder)
    (RegistrationNativeIdentityCensorPublicClient.callback selected bundle placeholder frontend)

private theorem enter_target (bundle : Nat) (query : TypedSpec.Domain) (mode : Mode) :
    (RegistrationNativeIdentityCensorCompiler.enter bundle query mode).target = mode.target := by
  cases query with
  | inl query => rfl
  | inr query => cases query <;> rfl

/-- The actual entered callback and every source failure preserve the public selector relation and both target copies. The frontend is any literal free Ctx callback, with no body law supplied. -/
theorem callback_aligned (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (query : TypedSpec.Domain) (before : Whole S) (prior : Aligned selected before.2)
    (synced : before.1.2.target = before.2.2.target) (result : TypedSpec.Range query × Whole S)
    (supported : result ∈ support ((callbacks joint selected bundle placeholder frontend query).run before)) :
    Aligned selected result.2.2 ∧ result.2.1.2.target = result.2.2.2.target := by
  simp only [callbacks, RegistrationNativeIdentityCensorPublicSource.callback,
    RegistrationNativeIdentityCensorPublicSource.runState, RegistrationNativeIdentityCensorPublicClient.callback,
    StateT.run, bind_pure_comp, simulateQ_map, map_apply, Functor.map_map, support_map] at supported
  obtain ⟨actual, called, rfl⟩ := supported
  exact lower_program joint selected placeholder ((frontend query).run before.1.1)
    (RegistrationNativeIdentityCensorCompiler.enter bundle query before.1.2) before.2 prior
    ((enter_target bundle query before.1.2).trans synced) actual called

/-- The complete original adaptive typed callback tree retains this public-history/target alignment through every reached prefix, with its full frontend/P/private physical state unchanged. -/
theorem callback_program (joint : PqxdhJointIdentity.Primitives) (selected bundle : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (work : OracleComp TypedSpec Value) (before : Whole S) (prior : Aligned selected before.2)
    (synced : before.1.2.target = before.2.2.target) (result : Value × Whole S)
    (supported : result ∈ support ((simulateQ (callbacks joint selected bundle placeholder frontend) work).run before)) :
    Aligned selected result.2.2 ∧ result.2.1.2.target = result.2.2.2.target := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query
    (callbacks joint selected bundle placeholder frontend)
    (fun current => Aligned selected current.2 ∧ current.1.2.target = current.2.2.target) _ work before ⟨prior, synced⟩ result supported
  intro query current held returned called
  exact callback_aligned joint selected bundle placeholder frontend query current held.1 held.2 returned called
end Callback

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.protocol_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.protocol_messages

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.protocol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.protocol

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.select_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.select_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.select_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.select_aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.initialized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.program_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.program_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.lower_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.lower_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.lower_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.callback_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.callback_aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.callback_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPolicySource.callback_program
