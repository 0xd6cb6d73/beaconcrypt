-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorMapped
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
/-! The literal normalized typed bundle callback retains the same actual first selector and genuine history freshness across its public entry and full output packing. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorCallback
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

omit primitives in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$>work) before=Prod.map change id <$>work before := StateT.run_map change work before

private theorem callback_code (selected position index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (before : NativeState × Mode) :
    (callback(selected,position,placeholder) (.inr (.bundle index))).run before=
      (fun result=> (result.1.1,(RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder result.1.2,result.2))) <$>
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
          ((RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created writer index).run before.1)).run
            (RegistrationNativeIdentityCensorCompiler.enter position (.inr (.bundle index)) before.2)) := by
  simp only [RegistrationNativeIdentityCensorPublicClient.callback,RegistrationNativeIdentityCensorAdaptivePostselection.normalized,
    RegistrationNativePlatformIdentityCtxTyped.handler,StateT.run,simulateQ_map,bind_pure_comp]
  simp only [map_apply,Functor.map_map]
  rfl

/-- At the correct original public bundle ordinal, the actual normalized callback's first selector is the newly signed wanted message and is fresh at that same cut. Both private interpretations and every bundle/writer failure are retained. -/
theorem callback (selected position index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (before : NativeState × Mode) (ordinal : before.2.bundles=position) (missing : before.2.target=none)
    (privateBefore : Private) (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected privateBefore.pool)
    (cut : RegistrationNativeIdentityTemplateSelectionCut.Original.Cut (RustM (Option Pqxdh.Bytes) × (NativeState × Mode)) × Private)
    (stopped : cut∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop ((callback(selected,position,placeholder) (.inr (.bundle index))).run before))).run privateBefore))
    (result : (RustM (Option Pqxdh.Bytes) × (NativeState × Mode)) × Private)
    (resumed : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2))
    (member : wanted∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected result.2.pool) :
    ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
      wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected cut.2.pool := by
  have entered : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed
      (RegistrationNativeIdentityCensorCompiler.enter position (.inr (.bundle index)) before.2) := by
    simp only [RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed,RegistrationNativeIdentityCensorCompiler.enter,ordinal,beq_self_eq_true,missing,and_self]
  rw [callback_code setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
    selected position index placeholder before] at stopped
  exact RegistrationNativeIdentityCensorFirstSelectorMapped.lifecycle setup checks representation created selected index placeholder masked wanted writer role
    before.1 (RegistrationNativeIdentityCensorCompiler.enter position (.inr (.bundle index)) before.2) entered privateBefore fresh _ cut stopped result resumed member

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorCallback
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorCallback.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorCallback.callback
