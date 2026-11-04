-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionBind
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorUnarmedCallbackSyntax
/-! The actual proof-side before-accept collector reaches the same first-selector ordinary-EUF success event. No supported source prefix is chosen independently of its recorded bundle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCollectorSuccess
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorPublicClient (ClientState)
open RegistrationNativeIdentityCensorPacketClient (Found)
variable {S A : Type}

private def publication : (query : TypedSpec.Domain) → TypedSpec.Range query → (S × Mode) → Bool
  | .inr (.bundle _),reply,after=>after.2.active &&(RegistrationNativeRawAdapter.resultOption reply).isSome
  | _,_,_=>false

private theorem visit_query (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : ClientState S) :
    RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder frontend defaults (TypedSpec.query query >>=next) before=(do
      let result←(RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder frontend defaults query).run before
      match RegistrationNativeIdentityCensorPublicClient.observe accept query before result.1 result.2 with
      | none=>RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder frontend defaults (next result.1) result.2
      | some reason=>pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason)) := rfl

private theorem callback_step (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (before : S × Mode) (cursor : Nat)
    (skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor=none) :
    (RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder frontend defaults query).run (before,cursor)=
      (RegistrationNativeIdentityCensorPublicClient.step selected position placeholder frontend query).run (before,cursor) := by
  cases query with
  | inl coin=>rfl
  | inr command=>
    cases command <;> try rfl
    rename_i packet
    have different : cursor≠accept := by
      intro equal
      simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt,equal,ite_true,reduceCtorEq] at skipped
    simp only [RegistrationNativeIdentityCensorBeforeAccept.step,StateT.run,different,ite_false]

private theorem observe_step (accept cursor nextCursor : Nat) (query : TypedSpec.Domain) (before after : S × Mode)
    (reply : TypedSpec.Range query) (skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor=none) :
    RegistrationNativeIdentityCensorPublicClient.observe accept query (before,cursor) reply (after,nextCursor)=
      if publication query reply after then some RegistrationNativeIdentityCensorPublicClient.Stop.published else none := by
  cases query with
  | inl coin=>rfl
  | inr command=>
    cases command <;> try rfl
    case bundle index=>
      cases active : after.2.active <;> cases returned : (RegistrationNativeRawAdapter.resultOption reply).isSome <;>
        simp only [RegistrationNativeIdentityCensorPublicClient.observe,publication,active,returned,Bool.and_false,Bool.and_true,
          Bool.false_eq_true,Bool.and_self,false_and,true_and,ite_true,ite_false]
    case accept packet=>
      have different : cursor≠accept := by
        intro equal
        simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt,equal,ite_true,reduceCtorEq] at skipped
      simp only [RegistrationNativeIdentityCensorPublicClient.observe,different,ite_false,publication,Bool.false_eq_true]

private theorem packet_step (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : S × Mode) (cursor : Nat)
    (skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor=none) :
    RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder frontend defaults (TypedSpec.query query >>=next) (before,cursor)=(do
      let result←(RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend query).run before
      if publication query result.1 result.2 then pure none else
        RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder frontend defaults (next result.1)
          (result.2,cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)) := by
  rw [visit_query,callback_step selected position accept placeholder frontend defaults query before cursor skipped]
  change (do
    let result←(fun result : TypedSpec.Range query ×(S ×Mode)=>(result.1,(result.2,cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))) <$>
      (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder frontend query).run before
    match RegistrationNativeIdentityCensorPublicClient.observe accept query (before,cursor) result.1 result.2 with
    | none=>RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder frontend defaults (next result.1) result.2
    | some reason=>pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason))=_
  rw [bind_map_left]
  apply bind_congr
  intro result
  rw [observe_step accept cursor _ query before result.2 result.1 skipped]
  cases published : publication query result.1 result.2 with
  | false=>simp only [Bool.false_eq_true,ite_false]
  | true=>simp only [ite_true,RegistrationNativeIdentityCensorPacketClient.finish]

open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


local notation "NativeState" => RegistrationNativeIdentityMain.State n KemSK source × Platform
local notation "Mode" => RegistrationNativeIdentityCensorCompiler.Mode
local notation "Private" => RegistrationNativeIdentityCensorSource.State
local notation "current(" placeholder ")" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder
local notation "callback(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder current(placeholder)



local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "PlainState" => RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source
local notation "target" => RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "published" => RegistrationNativeIdentityCensorAdaptivePostselection.published (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "impl(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder true current(placeholder)
local notation "sample(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorBundleSelectorSample.sample setup checks route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder
local notation "retained(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorBundleBoundaryPair.retained setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder true


private theorem sampled_event (selected position index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState)) (ordinal : before.1.2.bundles=position) (missing : before.1.2.target=none)
    (result : RegistrationNativeIdentityCensorBundleSelectorSample.Receipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) × (RustM (Option Pqxdh.Bytes) × FullState))
    (supported : result∈support (sample(selected,position,placeholder) index before)) (found : Found)
    (good : RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected
      (some ((RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle index next,(before,leading)),result.1,result.2,found))) :
    ∃ wanted continued,result.1.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
      wanted∉RegistrationNativeIdentityCensorPolicySource.messages selected result.1.2.pool ∧
      ∃seed,result.1.2.pool.seeds[selected]?=some seed ∧
        (RegistrationNativeIdentityCensorPacketClient.candidate setup.joint (setup.joint.publicKeys seed) (some found)).isSome=true := by
  obtain ⟨seed,row,wanted,packet,equal,role,fresh,member,valid⟩ := good
  have packetEq := Option.some.inj equal
  rw [←packetEq] at valid
  obtain ⟨continued,kind,freshAt,rowAt⟩ := RegistrationNativeIdentityCensorBundleSelectorSample.selected setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder index before ordinal missing wanted role fresh seed row result supported member
  exact ⟨wanted,continued,kind,freshAt,seed,rowAt,valid⟩

abbrev Op := RegistrationNativeIdentityCensorOperational.Spec
abbrev LocalReceipt := RegistrationNativeIdentityCensorBundleSelectorSample.Receipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)
abbrev Stored (A : Type) := RegistrationNativeIdentityCensorBundleVisitorReceipt.Receipt A FullState PlainState
  (LocalReceipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))
local notation "backend(" selected "," placeholder ")" => RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder

noncomputable def callbackCode (selected position index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (before : FullState) :=
  (callback(selected,position,placeholder) (.inr (.bundle index))).run before.1

private noncomputable def afterCode (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (cursor : Nat)
    (returned : TypedSpec.Range query × (NativeState × Mode)) : OracleComp Op (Option Found) :=
  if publication query returned.1 returned.2 then pure none else
    RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults (next returned.1)
      (returned.2,cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)

private noncomputable def positiveResume (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState)) (cut : LocalReceipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)) :
    ProbComp (Option (Stored (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) A)) := do
  let after←(simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2
  let kept := (after.1.1,(after.1.2,after.2))
  if published (.inr (.bundle index)) kept.1 kept.2 then pure none else
    (fun found=>found.map (fun found=>((RegistrationNativeIdentityCensorBundlePrefix.Cut.bundle index next,(before,leading)),cut,kept,found))) <$>
      RegistrationNativeIdentityCensorVisitorJournal.visit impl(selected,position,placeholder) target published accept (next kept.1) kept.2
        (RegistrationNativeIdentityCensorVisitorFold.count leading)

private theorem positive_factor (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState)) :
    RegistrationNativeIdentityCensorBundleVisitorReceipt.positive impl(selected,position,placeholder) target published sample(selected,position,placeholder) accept index next before leading=(do
      let cut←(simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        (callbackCode setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          selected position index placeholder before))).run before.2
      positiveResume setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position accept index placeholder next before leading cut) := by
  unfold RegistrationNativeIdentityCensorBundleVisitorReceipt.positive RegistrationNativeIdentityCensorBundleSelectorSample.sample positiveResume callbackCode
  simp only [bind_assoc,pure_bind]
  rfl

private theorem sample_supported (selected position index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (before : FullState) (cut : LocalReceipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))
    (stopped : cut∈support ((simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
      (callbackCode setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder before))).run before.2))
    (after : (RustM (Option Pqxdh.Bytes) × (NativeState × Mode)) × RegistrationNativeIdentityCensorSource.State)
    (resumed : after∈support ((simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2)) :
    (cut,(after.1.1,(after.1.2,after.2)))∈support (sample(selected,position,placeholder) index before) := by
  simp only [RegistrationNativeIdentityCensorBundleSelectorSample.sample,mem_support_bind_iff,mem_support_pure_iff]
  exact ⟨cut,stopped,after,resumed,rfl⟩

private theorem returned_zero (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState))
    (ordinal : before.1.2.bundles=position) (missing : before.1.2.target=none)
    (cut : LocalReceipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))
    (stopped : cut∈support ((simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
      (callbackCode setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder before))).run before.2))
    (value : RegistrationNativeIdentityCensorBundleSelectorSample.Value (n := n) (KemSK := KemSK) (Platform := Platform) (source := source))
    (returned : cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.returned value) :
    Pr{let result←(positiveResume setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept index placeholder next before leading cut)}[
        RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected result]=0 := by
  apply prEvent_eq_zero_of_forall_mem_support
  intro result reached good
  simp only [positiveResume,mem_support_bind_iff] at reached
  obtain ⟨after,resumed,reached⟩ := reached
  split at reached
  · simp only [mem_support_pure_iff] at reached
    subst result
    cases good
  · rw [support_map] at reached
    obtain ⟨found,_following,rfl⟩ := reached
    cases found with
    | none=>cases good
    | some found=>
      have sampled := sample_supported setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder before cut stopped after resumed
      obtain ⟨wanted,continued,kind,_fresh,_row⟩ := sampled_event setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder next before leading ordinal missing (cut,(after.1.1,(after.1.2,after.2))) sampled found good
      rw [returned] at kind
      cases kind

private theorem selected_bound (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState))
    (ordinal : before.1.2.bundles=position) (missing : before.1.2.target=none)
    (message : Pqxdh.Bytes)
    (continued : Bool → OracleComp Op (RegistrationNativeIdentityCensorBundleSelectorSample.Value (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)))
    (privateCut : RegistrationNativeIdentityCensorSource.State)
    (stopped : (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued,privateCut)∈support
      ((simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        (callbackCode setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          selected position index placeholder before))).run before.2)) :
    Pr{let result←(positiveResume setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept index placeholder next before leading (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued,privateCut))}[
        RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected result] ≤
    Pr{let final←((simulateQ backend(selected,placeholder) (RegistrationNativeIdentityTemplateSelectionCut.Original.resume
      (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message (fun reply=>continued reply >>=afterCode setup checks route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position accept placeholder defaults (.inr (.bundle index)) next (RegistrationNativeIdentityCensorVisitorFold.count leading))))).run privateCut)}[
          RegistrationNativeIdentityCensorPlainSelection.Success setup.joint selected
            ((RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message (fun reply=>continued reply >>=afterCode setup checks route representation created credential view failure allocation
              reserveRegistration reservePeer reserveFrame erased helper reserve selected position accept placeholder defaults (.inr (.bundle index)) next (RegistrationNativeIdentityCensorVisitorFold.count leading)),privateCut),final)] := by
  classical
  rw [RegistrationNativeIdentityCensorPlainSelectionSequence.resume_selected]
  unfold positiveResume
  apply prEvent_bind_mono_of_forall_le_of_support
  intro after resumed
  cases stoppedPublication : published (.inr (.bundle index)) after.1.1 (after.1.2,after.2) with
  | true=>
    simp only [stoppedPublication,ite_true,RegistrationNativeIdentityCensorIssuedCollector.Event,RegistrationNativeIdentityCensorIssuedCollector.PlainEvent,
      RegistrationNativeIdentityCensorBundleVisitorReceipt.forget,Option.map_none,Option.elim_none,prEvent_pure,ite_false]
    exact zero_le
  | false=>
    simp only [stoppedPublication,Bool.false_eq_true,ite_false]
    have notPublished : publication (.inr (.bundle index)) after.1.1 after.1.2=false := stoppedPublication
    simp only [afterCode,notPublished,Bool.false_eq_true,ite_false,RegistrationNativeIdentityCensorPublicClient.IsAccept,Nat.add_zero]
    rw [←RegistrationNativeIdentityCensorMaskedVisitorSource.packet_source setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder true accept defaults (next after.1.1) (after.1.2,after.2) (RegistrationNativeIdentityCensorVisitorFold.count leading)]
    simp only [StateT.run'_eq,Functor.map_map,RegistrationNativeIdentityCensorAdaptiveSource.sourceBackend,ite_true]
    apply prEvent_mono_of_support
    intro final _following good
    cases foundEq : final.1 with
    | none=>
      simp only [foundEq,Option.map_none] at good
      cases good
    | some found=>
      simp only [foundEq,Option.map_some] at good
      have sampled := sample_supported setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder before (RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued,privateCut) stopped after resumed
      obtain ⟨wanted,nextWanted,kind,fresh,seed,row,valid⟩ := sampled_event setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder next before leading ordinal missing
          ((RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected message continued,privateCut),(after.1.1,(after.1.2,after.2))) sampled found good
      have messageEq := congrArg (fun cut=>match cut with
        | .returned _=>none
        | .selected current _=>some current) kind
      change some message=some wanted at messageEq
      have sameMessage := Option.some.inj messageEq
      simp only [RegistrationNativeIdentityCensorPlainSelection.Success,row]
      exact ⟨by simpa only [sameMessage] using fresh,by simpa only [foundEq] using valid⟩

/-- At the same correct b callback, a positive collector receipt is contained in the literal plain first-selector success game. The fresh/new history crossing supplies its same sampled selector. -/
private theorem bundle_bound (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState))
    (ordinal : before.1.2.bundles=position) (missing : before.1.2.target=none) :
    Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.positive impl(selected,position,placeholder) target published sample(selected,position,placeholder)
      accept index next before leading)}[RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected result] ≤
    Pr{let result←(RegistrationNativeIdentityCensorPlainSelection.coupled setup.joint selected placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults
        (TypedSpec.query (.inr (.bundle index)) >>=next) (before.1,RegistrationNativeIdentityCensorVisitorFold.count leading)) before.2)}[
          RegistrationNativeIdentityCensorPlainSelection.Success setup.joint selected result] := by
  rw [packet_step selected position accept placeholder current(placeholder) defaults (.inr (.bundle index)) next before.1
    (RegistrationNativeIdentityCensorVisitorFold.count leading) rfl]
  change Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.positive impl(selected,position,placeholder) target published sample(selected,position,placeholder)
    accept index next before leading)}[RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected result] ≤
    Pr{let result←(RegistrationNativeIdentityCensorPlainSelection.coupled setup.joint selected placeholder
      (callbackCode setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position index placeholder before >>=afterCode setup checks route representation created credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper reserve selected position accept placeholder defaults (.inr (.bundle index)) next (RegistrationNativeIdentityCensorVisitorFold.count leading)) before.2)}[
            RegistrationNativeIdentityCensorPlainSelection.Success setup.joint selected result]
  rw [RegistrationNativeIdentityCensorPlainSelectionSequence.source,positive_factor]
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨cut,privateCut⟩ stopped
  cases cut with
  | returned value=>
    rw [returned_zero setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept index placeholder next before leading ordinal missing (.returned value,privateCut) stopped value rfl]
    exact zero_le
  | selected message continued=>
    simpa only [bind_pure_comp,prEvent_map] using selected_bound setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept index placeholder defaults next before leading ordinal missing message continued privateCut stopped

private theorem callback_marginal (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (query : TypedSpec.Domain) (before : FullState) :
    (fun after=>(after.1.1,(after.1.2,after.2))) <$>
      (simulateQ backend(selected,placeholder) ((callback(selected,position,placeholder) query).run before.1)).run before.2=
    (impl(selected,position,placeholder) query).run before := rfl

omit primitives in
private theorem publication_inactive (query : TypedSpec.Domain) (reply : TypedSpec.Range query) (after : NativeState × Mode)
    (inactive : after.2.active=false) : publication query reply after=false := by
  cases query with
  | inl coin=>rfl
  | inr command=>cases command <;> first | rfl | simp only [publication,inactive,Bool.false_and]

omit primitives in
private theorem count_next (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState))
    (query : TypedSpec.Domain) (before after : PlainState) (reply : TypedSpec.Range query) :
    RegistrationNativeIdentityCensorVisitorFold.count (leading++[⟨query,before,reply,after⟩])=
      RegistrationNativeIdentityCensorVisitorFold.count leading+(if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0) := by
  simp only [RegistrationNativeIdentityCensorVisitorFold.count,RegistrationNativeIdentityUnissuedCutTrace.count,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
  congr 1
  cases query with
  | inl coin=>rfl
  | inr command=>cases command <;> rfl

private theorem collect_forward (selected position accept cursor : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : FullState)
    (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState))
    (skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query (RegistrationNativeIdentityCensorVisitorFold.count leading)=none)
    (different : ∀ index,query=.inr (.bundle index)→cursor≠position) :
    RegistrationNativeIdentityCensorBundleVisitorReceipt.collect impl(selected,position,placeholder) RegistrationNativeIdentityCensorActualHashSource.project
      target published sample(selected,position,placeholder) position accept (TypedSpec.query query >>=next) before leading cursor=(do
        let result←(impl(selected,position,placeholder) query).run before
        RegistrationNativeIdentityCensorBundleVisitorReceipt.collect impl(selected,position,placeholder) RegistrationNativeIdentityCensorActualHashSource.project
          target published sample(selected,position,placeholder) position accept (next result.1) result.2
            (leading++[⟨query,RegistrationNativeIdentityCensorActualHashSource.project before,result.1,RegistrationNativeIdentityCensorActualHashSource.project result.2⟩])
            (cursor+if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0)) := by
  rw [RegistrationNativeIdentityCensorBundleVisitorReceipt.collect_step,skipped]
  cases query with
  | inl coin=>rfl
  | inr command=>
    cases command <;> try rfl
    rename_i index
    simp only [different index rfl,ite_false,RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle,ite_true]

/-- Every actual positive whole-visitor collector event is contained in the same plain source first-selector success experiment. Before-b callbacks are forwarded literally; the same b stop/resume receipt supplies freshness and generated identity. -/
theorem bound (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query) (work : OracleComp TypedSpec A)
    (before : FullState) (leading : List (RegistrationNativeStageTrace.Call TypedSpec PlainState)) (cursor : Nat)
    (counter : before.1.2.bundles=cursor) (missing : before.1.2.target=none) :
    Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.collect impl(selected,position,placeholder)
      RegistrationNativeIdentityCensorActualHashSource.project target published sample(selected,position,placeholder) position accept work before leading cursor)}[
        RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected result] ≤
    Pr{let result←(RegistrationNativeIdentityCensorPlainSelection.coupled setup.joint selected placeholder
      (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults work
        (before.1,RegistrationNativeIdentityCensorVisitorFold.count leading)) before.2)}[
          RegistrationNativeIdentityCensorPlainSelection.Success setup.joint selected result] := by
  classical
  induction work using OracleComp.inductionOn generalizing before leading cursor with
  | pure value=>
    change Pr{let result←(pure none : ProbComp (Option (Stored (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) A)))}[
      RegistrationNativeIdentityCensorIssuedCollector.Event setup.joint selected result]≤_
    simp only [RegistrationNativeIdentityCensorIssuedCollector.Event,RegistrationNativeIdentityCensorIssuedCollector.PlainEvent,
      RegistrationNativeIdentityCensorBundleVisitorReceipt.forget,Option.map_none,Option.elim_none,prEvent_pure,ite_false]
    exact zero_le
  | query_bind query next ih=>
    cases skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query (RegistrationNativeIdentityCensorVisitorFold.count leading) with
    | some packet=>
      rw [RegistrationNativeIdentityCensorBundleVisitorReceipt.collect_step,skipped]
      simp only [RegistrationNativeIdentityCensorIssuedCollector.Event,RegistrationNativeIdentityCensorIssuedCollector.PlainEvent,
        RegistrationNativeIdentityCensorBundleVisitorReceipt.forget,Option.map_none,Option.elim_none,prEvent_pure,ite_false]
      exact zero_le
    | none=>
      by_cases chosen : ∃index,query=.inr (.bundle index) ∧cursor=position
      · obtain ⟨index,rfl,atPosition⟩ := chosen
        rw [RegistrationNativeIdentityCensorBundleVisitorReceipt.collect_step,skipped]
        simp only [atPosition,ite_true]
        exact bundle_bound setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          selected position accept index placeholder defaults next before leading (counter.trans atPosition) missing
      · have different : ∀ index,query=.inr (.bundle index)→cursor≠position := by
          intro index same atPosition
          exact chosen ⟨index,same,atPosition⟩
        have sourceDifferent : ∀ index,query=.inr (.bundle index)→before.1.2.bundles≠position := by
          intro index same
          rw [counter]
          exact different index same
        have allowed := RegistrationNativeIdentityCensorUnarmedCallbackSyntax.callback selected position placeholder current(placeholder) query before.1 missing sourceDifferent
        rw [collect_forward setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          selected position accept cursor placeholder query next before leading skipped different]
        rw [packet_step selected position accept placeholder current(placeholder) defaults query next before.1 (RegistrationNativeIdentityCensorVisitorFold.count leading) skipped,
          RegistrationNativeIdentityCensorPlainSelectionBind.source setup.joint selected placeholder _ _ allowed before.2]
        rw [←callback_marginal setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
          selected position placeholder query before,bind_map_left]
        apply prEvent_bind_mono_of_forall_le_of_support
        intro after reached
        have markedReached : (after.1.1,(after.1.2,after.2))∈support ((impl(selected,position,placeholder) query).run before) := by
          rw [←callback_marginal setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
            selected position placeholder query before,support_map]
          exact ⟨after,reached,rfl⟩
        have control := RegistrationNativeIdentityCensorBundlePrefix.unarmed_step setup.joint selected position placeholder true current(placeholder)
          query before missing sourceDifferent (after.1.1,(after.1.2,after.2)) markedReached
        have quiet := publication_inactive query after.1.1 after.1.2 control.2.2
        simp only [quiet,Bool.false_eq_true,ite_false]
        have continued := ih after.1.1 (after.1.2,after.2)
          (leading++[⟨query,RegistrationNativeIdentityCensorActualHashSource.project before,after.1.1,
            RegistrationNativeIdentityCensorActualHashSource.project (after.1.2,after.2)⟩])
          (cursor+if RegistrationNativePlatformIdentityCtxSigningTrace.IsBundle query then 1 else 0)
          (by simpa only [counter] using control.1) control.2.1
        simpa only [count_next] using continued

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCollectorSuccess
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCollectorSuccess.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCollectorSuccess.bound
