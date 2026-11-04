-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorLifecycle
/-! Any pure normalization of the complete public bundle result preserves its first stopped selector and same private source-pool receipt. The normalizer may include Main/platform and Mode output fields. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorMapped
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (poolMessages)
open PqxdhEd25519EufCma (Ed25519Signature)
open PqxdhServerAuthExperiment (Setup Checks)
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Original.Cut
variable {A B : Type}

private def mapCut (change : A → B) : Cut A → Cut B
  | .returned value => .returned (change value)
  | .selected message next => .selected message (fun reply=>change <$> next reply)

private theorem stop_map (change : A → B) (work : OracleComp Old A) :
    RegistrationNativeIdentityTemplateSelectionCut.Original.stop (change <$> work)=
      mapCut change <$> RegistrationNativeIdentityTemplateSelectionCut.Original.stop work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [map_pure,RegistrationNativeIdentityTemplateSelectionCut.Original.stop]; rfl
  | query_bind query next ih =>
      rw [map_bind,RegistrationNativeIdentityTemplateSelectionCut.Original.step,
        RegistrationNativeIdentityTemplateSelectionCut.Original.step]
      rcases query with (((protocol|message)|scanned)|hash)|marker
      · simp only [map_bind,ih]
      · simp only [map_pure]; rfl
      · simp only [map_bind,ih]
      · simp only [map_bind,ih]
      · simp only [map_bind,ih]

private theorem resume_map (change : A → B) (cut : Cut A) :
    RegistrationNativeIdentityTemplateSelectionCut.Original.resume (mapCut change cut)=
      change <$> RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut := by
  cases cut with
  | returned value => simp only [mapCut,RegistrationNativeIdentityTemplateSelectionCut.Original.resume,map_pure]
  | selected message next => simp only [mapCut,RegistrationNativeIdentityTemplateSelectionCut.Original.resume,map_bind]; rfl

private def Receipt (implementation : QueryImpl Old (StateT State ProbComp)) (selected : Nat) (wanted : Pqxdh.Bytes)
    (work : OracleComp Old A) (before : State) : Prop :=
  ∀ cut : Cut A × State,cut∈support ((simulateQ implementation (RegistrationNativeIdentityTemplateSelectionCut.Original.stop work)).run before) →
    ∀ result : A × State,result∈support ((simulateQ implementation (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2) →
      wanted∈poolMessages selected result.2.pool →
        ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
          wanted∉poolMessages selected cut.2.pool

private theorem mapped (implementation : QueryImpl Old (StateT State ProbComp)) (selected : Nat) (wanted : Pqxdh.Bytes)
    (work : OracleComp Old A) (before : State) (change : A → B) (original : Receipt implementation selected wanted work before) :
    Receipt implementation selected wanted (change <$> work) before := by
  intro cut stopped result resumed member
  rw [stop_map,simulateQ_map,StateT.run_map,support_map] at stopped
  obtain ⟨originalCut,called,same⟩ := stopped
  subst cut
  rw [resume_map,simulateQ_map,StateT.run_map,support_map] at resumed
  obtain ⟨originalResult,reached,same⟩ := resumed
  subst result
  obtain ⟨next,chosen,fresh⟩ := original originalCut called originalResult reached member
  dsimp only
  rw [chosen]
  exact ⟨_,rfl,fresh⟩

variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (selected index : Nat) (placeholder : Ed25519Signature) (masked : Bool) (wanted : Pqxdh.Bytes)
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "NativeState" => RegistrationNativeIdentityMain.State n KemSK source × Platform
local notation "action" => RegistrationNativePlatformIdentityCtxLifecycle.bundle (n := n) (source := source) setup checks representation created writer index

/-- Arbitrary pure normalization of the complete original bundle result retains its same first-selector and private-pool receipt. -/
theorem lifecycle (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (nativeBefore : NativeState) (mode : Mode) (held : RegistrationNativeIdentityCensorFirstSelectorPrefix.Armed mode)
    (before : State) (fresh : wanted∉poolMessages selected before.pool)
    (change : ((RustM (Option Pqxdh.Bytes) × NativeState) × Mode) → B)
    (cut : Cut B × State)
    (stopped : cut∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop (change <$> ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) ((action).run nativeBefore)).run mode)))).run before))
    (result : B × State)
    (resumed : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2))
    (member : wanted∈poolMessages selected result.2.pool) :
    ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected wanted continued ∧
      wanted∉poolMessages selected cut.2.pool := by
  have plain : Receipt (RegistrationNativeIdentityCensorTargetSync.lower setup.joint selected placeholder masked)
      selected wanted ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) ((action).run nativeBefore)).run mode) before :=
    RegistrationNativeIdentityCensorFirstSelectorLifecycle.lifecycle setup checks representation created selected index placeholder masked wanted writer
      role nativeBefore mode held before fresh
  exact mapped _ selected wanted _ before change plain cut stopped result resumed member

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorMapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorMapped.lifecycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorMapped.lifecycle
