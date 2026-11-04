-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedEdBounds
/-! Actual fixed-public bundle/accept packet traversal retains the original indexed identity-create bill. Template markers, observers and independent hash coins add no creation; the actual callback leaf count is derived internally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
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


open RegistrationNativeIdentityTemplateCreateCounts (SourceCreate TargetCreate)
abbrev New := RegistrationNativeIdentityTemplateCensorRecognition.Spec
local notation "erase" => RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder
local notation "ClientState" => RegistrationNativeIdentityCensorPublicClient.ClientState MainState

omit primitive in
private theorem predicates : RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target .create = SourceCreate := by
  funext query
  rcases query with ((coin | request) | report) | bytes
  · simp [RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target,SourceCreate]
  · cases request <;> simp [RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target,SourceCreate]
    case service handle request => cases request <;> simp
  · simp [RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target,SourceCreate]
  · simp [RegistrationNativePlatformIdentityCtxEdCompilerBounds.Target,SourceCreate]

private theorem normalized_bound (query : TypedSpec.Domain) (before : MainState) :
    ((current query).run before).IsQueryBoundP SourceCreate (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  have bounded := RegistrationNativePlatformIdentityCtxTypedEdBounds.handler_create_bound setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve) query before
  change (Prod.map id (RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder) <$> (actual query).run before).IsQueryBoundP SourceCreate _
  rw [isQueryBoundP_map_iff]
  simpa only [predicates] using bounded

private theorem callback_bound (query : TypedSpec.Domain) (before : MainState × RegistrationNativeIdentityCensorCompiler.Mode) :
    (simulateQ erase ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder current query).run before)).IsQueryBoundP
      TargetCreate (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  have bounded := RegistrationNativeIdentityTemplateCreateCounts.operational selected placeholder ((current query).run before.1)
    (RegistrationNativeIdentityCensorCompiler.enter position query before.2) _
    (normalized_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve placeholder query before.1)
  simpa only [RegistrationNativeIdentityCensorPublicClient.callback,StateT.run,bind_pure_comp,simulateQ_map,isQueryBoundP_map_iff] using bounded

private theorem public_step_bound (query : TypedSpec.Domain) (before : ClientState) :
    (simulateQ erase ((RegistrationNativeIdentityCensorPublicClient.step selected position placeholder current query).run before)).IsQueryBoundP
      TargetCreate (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  simpa only [RegistrationNativeIdentityCensorPublicClient.step,StateT.run,simulateQ_map,isQueryBoundP_map_iff] using
    callback_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder query before.1

private theorem step_bound (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (before : ClientState) :
    (simulateQ erase ((RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder current defaults query).run before)).IsQueryBoundP
      TargetCreate (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin =>
    exact public_step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
      erased helper reserve selected position placeholder (.inl coin) before
  | inr command =>
    cases command
    case accept packet =>
      change (simulateQ erase (if before.2 = accept then pure (defaults (.inr (.accept packet)),before)
        else (RegistrationNativeIdentityCensorPublicClient.step selected position placeholder current (.inr (.accept packet))).run before)).IsQueryBoundP _ _
      split
      · rw [simulateQ_pure]
        exact isQueryBoundP_pure _ _ _
      · exact public_step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
          erased helper reserve selected position placeholder (.inr (.accept packet)) before
    all_goals
      exact public_step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame
        erased helper reserve selected position placeholder _ before

private theorem freeze_bound (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (before : ClientState × Option RegistrationNativeIdentityCensorPublicClient.Stop) :
    (simulateQ erase ((RegistrationNativeIdentityCensorBeforeAccept.freeze selected position accept placeholder current defaults query).run before)).IsQueryBoundP
      TargetCreate (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  rcases before with ⟨before,prior⟩
  cases prior with
  | some reason =>
    change (simulateQ erase (pure (defaults query,(before,some reason)))).IsQueryBoundP _ _
    rw [simulateQ_pure]
    exact isQueryBoundP_pure _ _ _
  | none =>
    simp only [RegistrationNativeIdentityCensorBeforeAccept.freeze,RegistrationNativeMldsaStop.freeze,RegistrationNativeMldsaStop.monitor,StateT.run,
      bind_pure_comp,simulateQ_map,isQueryBoundP_map_iff]
    exact step_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder accept defaults query before

private noncomputable def lowered (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) :
    QueryImpl TypedSpec (StateT (ClientState × Option RegistrationNativeIdentityCensorPublicClient.Stop) (OracleComp New)) :=
  fun query before => simulateQ erase ((RegistrationNativeIdentityCensorBeforeAccept.freeze selected position accept placeholder current defaults query).run before)

private theorem lowered_run (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : ClientState × Option RegistrationNativeIdentityCensorPublicClient.Stop) :
    simulateQ erase ((simulateQ (RegistrationNativeIdentityCensorBeforeAccept.freeze selected position accept placeholder current defaults) work).run before) =
      (simulateQ (lowered setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position placeholder accept defaults) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    exact bind_congr (fun result => ih result.1 result.2)

private theorem frozen (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : ClientState × Option RegistrationNativeIdentityCensorPublicClient.Stop) :
    (simulateQ erase ((simulateQ (RegistrationNativeIdentityCensorBeforeAccept.freeze selected position accept placeholder current defaults) work).run before)).IsQueryBoundP TargetCreate cap := by
  rw [lowered_run]
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded
    (freeze_bound setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder accept defaults) before

/-- The actual before-a packet visitor and template erasure retain the original create allowance. Every current callback leaf bill is discharged by the literal CTX typed handler, including rows born before a later failure. -/
theorem visit (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap) (before : ClientState) :
    (simulateQ erase (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current defaults work before)).IsQueryBoundP TargetCreate cap := by
  have observed := congrArg (fun script => simulateQ erase script)
    (RegistrationNativeIdentityCensorPacketClient.source selected position accept placeholder current defaults work before)
  simp only [simulateQ_map] at observed
  rw [←observed,isQueryBoundP_map_iff]
  exact frozen setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder accept defaults work cap bounded (before,none)

omit primitive in
private theorem capture_bound {W V : Type} (recognize : New.Domain → Option W)
    (work : OracleComp New V) (cap : Nat) (bounded : work.IsQueryBoundP TargetCreate cap) :
    (RegistrationNativeIdentityRecognitionCapture.capture recognize work).IsQueryBoundP TargetCreate cap := by
  induction work using OracleComp.inductionOn generalizing cap with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
    obtain ⟨first,later⟩ := (isQueryBoundP_query_bind_iff _ _ _ _).mp bounded
    have step : RegistrationNativeIdentityRecognitionCapture.capture recognize (New.query query >>= next) =
        (match recognize query with
        | some witness => pure (.inl witness)
        | none => do let reply ← New.query query; RegistrationNativeIdentityRecognitionCapture.capture recognize (next reply)) := rfl
    rw [step]
    cases recognize query with
    | some witness => exact isQueryBoundP_pure _ _ _
    | none => exact (isQueryBoundP_query_bind_iff _ _ _ _).mpr ⟨first,fun reply => ih reply _ (later reply)⟩

/-- Recognition/extraction observes existing bytes and may stop early; it issues no identity creation. The actual packet client therefore keeps the same original create cap. -/
theorem packet (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : MainState) (knownInputs : List Pqxdh.Bytes) (identity : PqxdhJointIdentity.PublicIdentity) :
    (RegistrationNativeIdentityTemplateCensorRecognition.packetClient setup.joint selected position accept placeholder current defaults
      (fun _identity => work) before knownInputs identity).IsQueryBoundP TargetCreate cap := by
  rw [RegistrationNativeIdentityTemplateCensorRecognition.packetClient,isQueryBoundP_map_iff]
  apply capture_bound
  exact visit setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder accept defaults work cap bounded ((before,({knownInputs := knownInputs} : RegistrationNativeIdentityCensorCompiler.Mode)),0)

/-- The literal public successful-reply policy and independent hash sampler retain the actual client’s create cap, supplying the reserved-family interpreter with no extra capacity hypothesis. -/
theorem independent (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap)
    (before : MainState) (knownInputs : List Pqxdh.Bytes) (identity : PqxdhJointIdentity.PublicIdentity)
    (publicBefore : RegistrationNativeIdentityTemplatePolicy.Public) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.independent ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
      (RegistrationNativeIdentityTemplateCensorRecognition.packetClient setup.joint selected position accept placeholder current defaults
        (fun _identity => work) before knownInputs identity)).run publicBefore)).IsQueryBoundP RegistrationNativeIdentityIndependentSource.IsCreate cap := by
  apply RegistrationNativeIdentityTemplateCreateCounts.policy
  exact packet setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder accept defaults work cap bounded before knownInputs identity

/-- The original raw command allowance supplies the reserved-family creation cap for the actual before-accept client in every original mode. -/
theorem raw (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work)
    (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (before : MainState) (knownInputs : List Pqxdh.Bytes) (identity : PqxdhJointIdentity.PublicIdentity)
    (publicBefore : RegistrationNativeIdentityTemplatePolicy.Public) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.independent ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
      (RegistrationNativeIdentityTemplateCensorRecognition.packetClient setup.joint selected position accept placeholder current defaults
        (fun _identity => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
          serverKeyId bounds mode work) before knownInputs identity)).run publicBefore)).IsQueryBoundP
      RegistrationNativeIdentityIndependentSource.IsCreate (budget.cap 1) := by
  have bill := RegistrationNativeFullCompiler.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded 1
  simp [Fin.sum_univ_succ,PqxdhDeploymentCompileSecrecy.wrapCost] at bill
  exact independent setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position placeholder accept defaults _ (budget.cap 1) bill before knownInputs identity publicBefore

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.visit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.visit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.packet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateVisitorCreateBounds.raw
