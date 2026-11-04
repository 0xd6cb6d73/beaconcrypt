-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorCallback
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
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample
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


abbrev Reply := RustM (Option Pqxdh.Bytes)
abbrev Value := Reply × (NativeState × Mode)
abbrev Receipt := RegistrationNativeIdentityTemplateSelectionCut.Original.Cut (Value (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)) × Private
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)

noncomputable def sample (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (index : Nat) (before : FullState) : ProbComp (Receipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) × (Reply × FullState)) := do
  let cut←(simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
    (RegistrationNativeIdentityTemplateSelectionCut.Original.stop ((callback(selected,position,placeholder) (.inr (.bundle index))).run before.1))).run before.2
  let result←(simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
    (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2
  pure (cut,(result.1.1,(result.1.2,result.2)))

/-- The sampled same-run first-selector receipt is a pure proof coordinate: erasing it gives the actual complete marked normalized b callback, without removing any source call. -/
theorem marginal (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (index : Nat) (before : FullState) :
    Prod.snd <$>sample setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder index before=
    (RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder true current(placeholder) (.inr (.bundle index))).run before := by
  unfold sample
  simp only [map_bind,map_pure]
  change (do
    let cut←(simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop ((callback(selected,position,placeholder) (.inr (.bundle index))).run before.1))).run before.2
    let result←(simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2
    pure (result.1.1,(result.1.2,result.2)))=
    (fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ (RegistrationNativeIdentityCensorSource.censored setup.joint selected placeholder)
        ((callback(selected,position,placeholder) (.inr (.bundle index))).run before.1)).run before.2
  conv_rhs => rw [RegistrationNativeIdentityTemplateSelectionCut.Original.execution]
  simp only [map_bind,bind_pure_comp]

/-- A fresh wanted history crossing at the retained b poststate identifies that same sampled first selector and its genuine generated row. No independently chosen supported cut is used. -/
theorem selected (selected position : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (index : Nat) (before : FullState) (ordinal : before.1.2.bundles=position) (missing : before.1.2.target=none)
    (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected before.2.pool)
    (seed : PqxdhJointIdentity.IdentitySeed) (row : before.2.pool.seeds[selected]?=some seed)
    (result : Receipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) × (Reply × FullState))
    (supported : result∈support (sample setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder index before))
    (member : wanted∈RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected result.2.2.2.pool) :
    ∃ continued,result.1.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
      wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.poolMessages selected result.1.2.pool ∧
      result.1.2.pool.seeds[selected]?=some seed := by
  simp only [sample,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨cut,stopped,after,resumed,rfl⟩ := supported
  obtain ⟨continued,kind,freshAt⟩ := RegistrationNativeIdentityCensorFirstSelectorCallback.callback setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position index placeholder true wanted role before.1 ordinal missing before.2 fresh cut stopped after resumed member
  have rowAt := RegistrationNativeIdentityCensorSelectedInvariant.row_program setup.joint selected placeholder true seed
    (RegistrationNativeIdentityTemplateSelectionCut.Original.stop ((callback(selected,position,placeholder) (.inr (.bundle index))).run before.1)) before.2 row cut stopped
  exact ⟨continued,kind,freshAt,rowAt⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample.marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample.marginal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample.selected
