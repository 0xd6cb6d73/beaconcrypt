-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateChosenSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxNoReveal
/-! The literal normalized source packet visitor remains structurally free of generated-identity reveals after marker/template erasure. Actual callback safety is derived from the current source dispatcher. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityTemplateChosenSource (TemplateAllowed)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
variable {A : Type}

private theorem prepare_scope (selected handle : Nat) (message : Pqxdh.Bytes)
    (before : Mode) (placeholder : Ed25519Signature) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run before)).AllQueriesSatisfy TemplateAllowed := by
  unfold RegistrationNativeIdentityCensorOperational.promote RegistrationNativeIdentityCensorCompiler.prepare
  dsimp only [StateT.run]
  split
  · rename_i eligible
    split
    · simp only [simulateQ_bind, RegistrationNativeIdentityCensorCompiler.select, simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase]
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
      · intro chosen
        cases chosen with
        | false =>
          simp only [Bool.false_eq_true, ite_false, simulateQ_pure]
          exact allQueriesSatisfy_pure _ _
        | true =>
          simp only [ite_true, simulateQ_bind, RegistrationNativeIdentityCensorCompiler.inspect,
            simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
            RegistrationNativeIdentityTemplateCensorRecognition.erase]
          apply allQueriesSatisfy_bind
          · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
          · intro inspected
            exact allQueriesSatisfy_pure _ _
    · simp only [pure_bind]
      exact allQueriesSatisfy_pure _ _
  · simp only [simulateQ_pure]
    exact allQueriesSatisfy_pure _ _
private theorem lift_scope (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A)
    (safe : (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work).AllQueriesSatisfy TemplateAllowed)
    (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((StateT.lift work : StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) A).run before)).AllQueriesSatisfy TemplateAllowed := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (do let answer ← work; pure (answer,before))).AllQueriesSatisfy _
  rw [simulateQ_bind]
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

private theorem signing_scope (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) (placeholder : Ed25519Signature) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run before)).AllQueriesSatisfy TemplateAllowed := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, simulateQ_bind]
  apply allQueriesSatisfy_bind (prepare_scope selected handle message before placeholder)
  intro prepared
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · apply lift_scope
    rw [simulateQ_spec_query]
    exact allQueriesSatisfy_pure _ _
  · apply lift_scope
    simp only [RegistrationNativeIdentityCensorOperational.embed, simulateQ_spec_query,
      RegistrationNativeIdentityTemplateCensorRecognition.erase]
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem hash_scope (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before)).AllQueriesSatisfy TemplateAllowed := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
    | some _ => simulateQ RegistrationNativeIdentityCensorOperational.embed
        ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run before)
    | none => do
        let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inr (.template selected before.target
          (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) :
          OracleComp RegistrationNativeIdentityCensorOperational.Spec (CtxRomAuth.CtxDigest × Nat))
        pure (reply,before))).AllQueriesSatisfy _
  cases routed : (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
  | none =>
    simp only [simulateQ_bind, simulateQ_spec_query,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro reply
      exact allQueriesSatisfy_pure _ _
  | some input =>
    unfold RegistrationNativeIdentityCensorCompiler.implementation
    dsimp only [StateT.run]
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro reply
      exact allQueriesSatisfy_pure _ _

private theorem protocol_scope (placeholder : Ed25519Signature)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (allowed : RegistrationNativeIdentityMainNoRevealCore.Allowed request) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol request))).run before)).AllQueriesSatisfy TemplateAllowed := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      (do let answer ← RegistrationNativeIdentityCensorCompiler.protocol request; pure (answer,before)))).AllQueriesSatisfy _
  rw [simulateQ_bind, simulateQ_bind]
  apply allQueriesSatisfy_bind
  · simp only [RegistrationNativeIdentityCensorCompiler.protocol, simulateQ_spec_query,
      RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase]
    exact (allQueriesSatisfy_query_iff _ _).mpr allowed
  · intro answer
    exact allQueriesSatisfy_pure _ _


private theorem query_scope (selected : Nat) (placeholder : Ed25519Signature)
    (request : Source.Domain) (before : Mode) (allowed : RegistrationNativePlatformIdentityCtxNoReveal.Allowed request) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run before)).AllQueriesSatisfy TemplateAllowed := by
  rcases request with ((coin|request)|report)|bytes
  · exact protocol_scope placeholder (.inl (.inl coin)) trivial before
  · cases request with
    | create => exact protocol_scope placeholder (.inl (.inr .create)) trivial before
    | reveal handle => exact False.elim (allowed trivial)
    | service handle request => cases request with
      | staticDh peer => exact protocol_scope placeholder (.inl (.inr (.service handle (.staticDh peer)))) trivial before
      | sign message => exact signing_scope selected handle message before placeholder
  · exact protocol_scope placeholder (.inr report) trivial before
  · exact hash_scope selected placeholder bytes before

/-- Every actual operational source continuation preserves the original structural identity no-reveal restriction under marker erasure. -/
theorem operational (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Source A)
    (allowed : work.AllQueriesSatisfy RegistrationNativePlatformIdentityCtxNoReveal.Allowed) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before)).AllQueriesSatisfy TemplateAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
      exact allQueriesSatisfy_bind (query_scope selected placeholder query before allowed.1)
        (fun result => ih result.1 (allowed.2 result.1) result.2)

open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "MainState" => RegistrationNativeIdentityMain.State n KemSK mlSource × Platform
local notation "view" => RegistrationNativeIdentityCensorOutgoingView.view placeholder

local notation "current" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder

local notation "entered(" query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.entered position query before
local notation "called(" masked "," query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query before
local notation "run(" masked "," accept "," work "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept work before


local notation "erase" => RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder
local notation "ClientState" => RegistrationNativeIdentityCensorPublicClient.ClientState MainState

private theorem normalized_safe (query : TypedSpec.Domain) (before : MainState) :
    ((current query).run before).AllQueriesSatisfy RegistrationNativePlatformIdentityCtxNoReveal.Allowed := by
  change (Prod.map id (RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder) <$> (actual query).run before).AllQueriesSatisfy _
  exact RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _
    (RegistrationNativePlatformIdentityCtxNoReveal.handler_safe setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve) query before)

private theorem callback_safe (query : TypedSpec.Domain) (before : MainState × Mode) :
    (simulateQ erase ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder current query).run before)).AllQueriesSatisfy TemplateAllowed := by
  have safe := operational selected placeholder ((current query).run before.1)
    (normalized_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder query before.1)
    (RegistrationNativeIdentityCensorCompiler.enter position query before.2)
  simpa only [RegistrationNativeIdentityCensorPublicClient.callback,StateT.run,bind_pure_comp,simulateQ_map]
    using RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ safe

private theorem public_step_safe (query : TypedSpec.Domain) (before : ClientState) :
    (simulateQ erase ((RegistrationNativeIdentityCensorPublicClient.step selected position placeholder current query).run before)).AllQueriesSatisfy TemplateAllowed := by
  have safe := callback_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder query before.1
  simpa only [RegistrationNativeIdentityCensorPublicClient.step,StateT.run,simulateQ_map]
    using RegistrationNativeIdentityMainNoRevealCore.mapped _ _ _ safe

private theorem step_safe (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (before : ClientState) :
    (simulateQ erase ((RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder current defaults query).run before)).AllQueriesSatisfy TemplateAllowed := by
  cases query with
  | inl coin =>
      exact public_step_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reserve selected position placeholder (.inl coin) before
  | inr command =>
    cases command
    case accept packet =>
      change (simulateQ erase (if before.2=accept then pure (defaults (.inr (.accept packet)),before)
        else (RegistrationNativeIdentityCensorPublicClient.step selected position placeholder current (.inr (.accept packet))).run before)).AllQueriesSatisfy _
      split
      · exact allQueriesSatisfy_pure _ _
      · exact public_step_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
          erased helper reserve selected position placeholder (.inr (.accept packet)) before
    all_goals
      exact public_step_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reserve selected position placeholder _ before

/-- The actual normalized before-accept packet visitor has no indexed identity reveal under any original typed continuation, source state, defaults or public counters. -/
theorem visit (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : ClientState) :
    (simulateQ erase (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current defaults work before)).AllQueriesSatisfy TemplateAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      change (simulateQ erase (do
        let result ← (RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder current defaults query).run before
        match RegistrationNativeIdentityCensorPublicClient.observe accept query before result.1 result.2 with
        | none => RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current defaults (next result.1) result.2
        | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason))).AllQueriesSatisfy TemplateAllowed
      rw [simulateQ_bind]
      apply allQueriesSatisfy_bind (step_safe setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position placeholder accept defaults query before)
      intro result
      cases RegistrationNativeIdentityCensorPublicClient.observe accept query before result.1 result.2 with
      | none => exact ih result.1 result.2
      | some reason => exact allQueriesSatisfy_pure _ _

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal.operational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal.operational

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal.visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorNoReveal.visit
