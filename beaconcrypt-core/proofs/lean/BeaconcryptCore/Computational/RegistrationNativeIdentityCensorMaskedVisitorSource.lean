-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorVisitorJournal
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
/-! A proof-only sampler retains the actual first-selector receipt jointly with the same normalized bundle reply and full poststate. Erasing that receipt recovers the literal callback exactly. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource
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



variable {A : Type}
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "target" => RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "published" => RegistrationNativeIdentityCensorAdaptivePostselection.published (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "impl(" selected "," position "," placeholder "," masked ")" => RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder masked current(placeholder)
local notation "called(" selected "," position "," placeholder "," masked "," query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query before

private theorem handler_run (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (masked : Bool) (query : TypedSpec.Domain) (before : FullState) :
    (impl(selected,position,placeholder,masked) query).run before=called(selected,position,placeholder,masked,query,before) :=
  RegistrationNativeIdentityCensorPublicSource.current setup.joint selected position placeholder masked current(placeholder) query before

/-- The generic complete-state visitor is the literal actual marked before-accept traversal for either private interpretation. -/
theorem visit_eq (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (masked : Bool) (accept : Nat) (work : OracleComp TypedSpec A) (before : FullState) (cursor : Nat) :
    RegistrationNativeIdentityCensorVisitorJournal.visit impl(selected,position,placeholder,masked) target published accept work before cursor=
      RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept work (before,cursor) := by
  induction work using OracleComp.inductionOn generalizing before cursor with
  | pure value=>rfl
  | query_bind query next ih=>
    change (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet=>pure ((target before).map (fun message=>(message,packet)))
      | none=>do
          let reached←(impl(selected,position,placeholder,masked) query).run before
          if published query reached.1 reached.2 then pure none else
            RegistrationNativeIdentityCensorVisitorJournal.visit impl(selected,position,placeholder,masked) target published accept (next reached.1) reached.2
              (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))=
      (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
      | some packet=>pure ((target before).map (fun message=>(message,packet)))
      | none=>do
          let selectedCut←RegistrationNativeIdentityCensorAdaptivePostselection.cut query <$>called(selected,position,placeholder,masked,query,before)
          match selectedCut with
          | none=>pure none
          | some kept=>(RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential view failure allocation
              reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept (next kept.1)
                (kept.2,cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)))
    rw [handler_run setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve]
    cases attempted : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query cursor with
    | some packet=>rfl
    | none=>
      simp only [bind_map_left]
      apply bind_congr
      intro reached
      unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut
      cases stopped : published query reached.1 reached.2 with
      | true=>simp only [ite_true]
      | false=>simpa only [Bool.false_eq_true,ite_false] using ih reached.1 reached.2 (cursor+if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)

/-- Closing the actual executable packet visitor gives that same generic complete-state source visitor; only its unused final private state is projected. -/
theorem packet_source (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (masked : Bool) (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : FullState) (cursor : Nat) :
    (simulateQ (RegistrationNativeIdentityCensorAdaptiveSource.sourceBackend setup.joint selected placeholder masked)
      (RegistrationNativeIdentityCensorPacketClient.visit selected position accept placeholder current(placeholder) defaults work (before.1,cursor))).run' before.2=
    RegistrationNativeIdentityCensorVisitorJournal.visit impl(selected,position,placeholder,masked) target published accept work before cursor := by
  rw [visit_eq]
  exact RegistrationNativeIdentityCensorAdaptiveSource.source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked accept defaults work (before,cursor)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource.visit_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource.visit_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource.packet_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource.packet_source
