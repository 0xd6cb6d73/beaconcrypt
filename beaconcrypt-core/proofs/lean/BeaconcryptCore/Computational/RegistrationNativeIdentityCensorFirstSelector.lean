-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorHistory
/-! A correct first-bundle history crossing identifies the same original stopped selector and retains freshness at its literal private source cut. No writer or signing-success condition is an input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (poolMessages)
open RegistrationNativePlatformIdentityCtxBundleMessageScope (UsesSourceMessage)
open PqxdhEd25519EufCma (Ed25519Signature)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Original.Cut
variable {A : Type}

/-- The actual first selector is the newly signed wanted source operand; the same reached source pool still has it fresh. -/
theorem program (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (fixed wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp Source A) (scope : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool)
    (cut : Cut (A × Mode) × State)
    (stopped : cut∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before))
    (result : (A × Mode) × State)
    (resumed : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2))
    (member : wanted∈poolMessages selected result.2.pool) :
    ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
      wanted∉poolMessages selected cut.2.pool := by
  have full : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before) := by
    rw [RegistrationNativeIdentityTemplateSelectionCut.Original.execution,mem_support_bind_iff]
    exact ⟨cut,stopped,resumed⟩
  have same := RegistrationNativeIdentityCensorFirstSelectorHistory.crossing joint selected placeholder masked fixed wanted role
    work scope mode before fresh result full member
  subst fixed
  exact RegistrationNativeIdentityCensorFirstSelectorPrefix.selected joint selected placeholder masked wanted role work scope mode held before fresh cut stopped result resumed member

open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The literal captured bundled body derives its own source-message scope; failed source writers and optional signing replies remain present. -/
theorem bundled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (selected index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (placeholder : Ed25519Signature) (masked : Bool) (wanted : Pqxdh.Bytes)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (nativeBefore : RegistrationNativeIdentityMain.State n KemSK source × Platform)
    (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool)
    (cut : Cut (((RustM (Option (alloc.vec.Vec U8)) ×
      (RegistrationNativeIdentityMain.State n KemSK source × Platform)) × Mode)) × State)
    (stopped : cut∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
          ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
            (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer)).run nativeBefore)).run mode))).run before))
    (result : ((RustM (Option (alloc.vec.Vec U8)) ×
      (RegistrationNativeIdentityMain.State n KemSK source × Platform)) × Mode) × State)
    (resumed : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2))
    (member : wanted∈poolMessages selected result.2.pool) :
    ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
      wanted∉poolMessages selected cut.2.pool := by
  obtain ⟨started,built,tagged⟩ := RegistrationNativeIdentitySigningRole.initial
    ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩
  exact program setup.joint selected placeholder masked (PqxdhRefinement.absBytes started.message.one_time_key) wanted role _
    (RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled setup checks representation created index owner scalar writer started built tagged nativeBefore)
    mode held before fresh cut stopped result resumed member

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector.bundled


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelector.program
