-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSelectedInvariant
/-! The actual armed source prefix stops before its first one-time signing selector. Its complete private source pool still has the selected message fresh at that same cut. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (poolMessages)
open RegistrationNativePlatformIdentityCtxBundleMessageScope (UsesSourceMessage)
open PqxdhEd25519EufCma (Ed25519Signature)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
abbrev Cut := RegistrationNativeIdentityTemplateSelectionCut.Original.Cut
variable {A : Type}

def Armed (mode : Mode) : Prop := mode.armed=true ∧ mode.active=false ∧ mode.target=none

def Trigger (selected : Nat) : Source.Domain → Prop
  | .inl (.inl (.inr (.service handle (.sign message)))) =>
      handle=selected ∧ RegistrationNativeIdentitySigningRole.oneTime message=true
  | _ => False

private def forward (request : Source.Domain) : OracleComp Old (Source.Range request) :=
  simulateQ RegistrationNativeIdentityCensorOperational.embed (RegistrationNativeIdentityCensorPrefix.embed request)

private theorem forward_query (selected : Nat) (placeholder : Ed25519Signature)
    (request : Source.Domain) (mode : Mode) (held : Armed mode) (quiet : ¬Trigger selected request) :
    (RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode =
      (do let reply ← forward request; pure (reply,RegistrationNativeIdentityCensorPrefix.next mode request)) := by
  rcases request with ((coin|request)|report)|bytes
  · rfl
  · cases request with
    | create | reveal handle => rfl
    | service handle request => cases request with
      | staticDh peer => rfl
      | sign message =>
          change ¬(handle=selected ∧ RegistrationNativeIdentitySigningRole.oneTime message=true) at quiet
          have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run mode=pure ((),mode) := by
            simp only [RegistrationNativeIdentityCensorCompiler.prepare,StateT.run,quiet,ite_false]
          change (RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode = _
          rw [RegistrationNativeIdentityCensorOperational.signing,StateT.run_bind]
          change (do
            let prepared ← simulateQ RegistrationNativeIdentityCensorOperational.embed
              ((RegistrationNativeIdentityCensorCompiler.prepare selected handle message).run mode)
            _) = _
          rw [prepared,simulateQ_pure,pure_bind]
          have absent : ¬(handle=selected ∧ mode.target=some message) := by
            intro impossible
            rw [held.2.2] at impossible
            cases impossible.2
          simp only [StateT.run_bind,StateT.run_get,pure_bind,absent,ite_false]
          rfl
  · rfl
  · change (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
      | none => _) = _
    simp only [RegistrationNativeIdentityCensorCompiler.hashInput,held.2.1,Bool.false_eq_true,ite_false]
    unfold RegistrationNativeIdentityCensorOperational.promote RegistrationNativeIdentityCensorCompiler.implementation
    dsimp only [StateT.run]
    simp only [RegistrationNativeIdentityCensorCompiler.hashInput,held.2.1,Bool.false_eq_true,ite_false,
      held.2.2,simulateQ_bind,simulateQ_spec_query,simulateQ_pure]
    simp only [held.2.1,held.2.2,forward,
      RegistrationNativeIdentityCensorPrefix.embed,RegistrationNativeIdentityCensorPrefix.next,
      simulateQ_spec_query]
    congr 1
    rw [held.2.1,held.2.2]
    rfl

private theorem selecting_query (selected : Nat) (placeholder : Ed25519Signature)
    (message : Pqxdh.Bytes) (mode : Mode) (held : Armed mode)
    (role : RegistrationNativeIdentitySigningRole.oneTime message=true) :
    ∃ next : Bool → OracleComp Old (Option Ed25519Signature × Mode),
      (RegistrationNativeIdentityCensorOperational.implementation selected placeholder
        (.inl (.inl (.inr (.service selected (.sign message)))))).run mode =
      (Old.query (.inl (.inl (.inl (.inr message)))) : OracleComp Old Bool) >>= next := by
  have prepared : ∃ later : Bool → OracleComp Old (Unit × Mode),
      (RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected selected message)).run mode =
      ((Old.query (.inl (.inl (.inl (.inr message)))) : OracleComp Old Bool) >>= later) := by
    change ∃ later : Bool → OracleComp Old (Unit × Mode),
      simulateQ RegistrationNativeIdentityCensorOperational.embed
        ((RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run mode) = _
    simp only [RegistrationNativeIdentityCensorCompiler.prepare,StateT.run,role,and_self,ite_true,
      held.1,held.2.2,RegistrationNativeIdentityCensorCompiler.select,simulateQ_bind,
      simulateQ_spec_query,RegistrationNativeIdentityCensorOperational.embed]
    exact ⟨_,rfl⟩
  obtain ⟨later,prepared⟩ := prepared
  change (∃ next, (RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode = _)
  rw [RegistrationNativeIdentityCensorOperational.signing,StateT.run_bind,prepared,bind_assoc]
  exact ⟨_,rfl⟩

private theorem forward_stop {B : Type} (request : Source.Domain)
    (next : Source.Range request → OracleComp Old B) :
    RegistrationNativeIdentityTemplateSelectionCut.Original.stop (forward request >>= next) =
      (do let reply ← forward request; RegistrationNativeIdentityTemplateSelectionCut.Original.stop (next reply)) := by
  cases request <;> rfl

private theorem forward_source (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : Ed25519Signature) (masked : Bool) (request : Source.Domain) (before : State) :
    (fun result => (result.1,(result.2.pool,result.2.hash))) <$>
      (simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked) (forward request)).run before =
    (RegistrationNativePlatformIdentityCtxSource.implementation joint request).run (before.pool,before.hash) := by
  cases request with
  | inl request => cases masked <;>
      simp only [forward,RegistrationNativeIdentityCensorPrefix.embed,RegistrationNativeIdentityCensorCompiler.protocol,
        simulateQ_spec_query,RegistrationNativeIdentityCensorOperational.embed,RegistrationNativeIdentityCensorTargetSync.lower,
        Bool.false_eq_true,ite_false,ite_true,RegistrationNativeIdentityCensorSource.censored,
        RegistrationNativeIdentityCensorSource.implementation,RegistrationNativeIdentityCensorSource.protocol,
        RegistrationNativePlatformIdentityCtxSource.implementation,StateT.run,Functor.map_map]
  | inr bytes => cases masked <;>
      simp only [forward,RegistrationNativeIdentityCensorPrefix.embed,simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed,RegistrationNativeIdentityCensorTargetSync.lower,
        Bool.false_eq_true,ite_false,ite_true,RegistrationNativeIdentityCensorSource.censored,
        RegistrationNativeIdentityCensorSource.implementation,RegistrationNativeIdentityCensorSource.physical,
        RegistrationNativePlatformIdentityCtxSource.implementation,StateT.run,Functor.map_map]

private theorem original_fresh (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (wanted : Pqxdh.Bytes)
    (query : Source.Domain) (other : query≠.inl (.inl (.inr (.service selected (.sign wanted)))))
    (before : RegistrationNativePlatformIdentityCtxSource.State)
    (result : Source.Range query × RegistrationNativePlatformIdentityCtxSource.State)
    (supported : result∈support ((RegistrationNativePlatformIdentityCtxSource.implementation joint query).run before))
    (fresh : wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages selected before)
    (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted∉RegistrationNativePlatformIdentityCtxSigningHistoryFrame.messages selected result.2 := by
  intro member
  by_cases quiet : RegistrationNativePlatformIdentityCtxSigningHistoryFrame.NoSignFor selected query
  · have same := RegistrationNativePlatformIdentityCtxSigningHistoryFrame.query joint selected query quiet before result supported
    exact fresh (same ▸ member)
  · rcases query with ((coin|request)|report)|bytes
    · exact quiet trivial
    · cases request with
      | create | reveal handle => exact quiet trivial
      | service handle request => cases request with
        | staticDh peer => exact quiet trivial
        | sign message =>
            have same : handle=selected := by
              by_contra different
              exact quiet different
            subst handle
            have unequal : message≠wanted := fun equal => other (by cases equal; rfl)
            have crossed := RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.query joint selected message
              (.inl (.inl (.inr (.service selected (.sign message))))) (fun _=>rfl) before result supported wanted member role
            exact crossed.elim fresh (fun equal=>unequal equal.symm)
    · exact quiet trivial
    · exact quiet trivial

def ResultFresh (selected : Nat) (fixed : Pqxdh.Bytes) (result : Cut (A × Mode) × State) : Prop :=
  fixed∉poolMessages selected result.2.pool ∧ match result.1 with
  | .returned value => Armed value.2
  | .selected message _ => message=fixed

/-- The original first-selector cut preserves source freshness and identifies its literal source operand before any signing reply. -/
theorem stopped (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (fixed : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime fixed=true)
    (work : OracleComp Source A) (scope : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (mode : Mode) (held : Armed mode) (before : State) (fresh : fixed∉poolMessages selected before.pool)
    (result : Cut (A × Mode) × State)
    (supported : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before)) :
    ResultFresh selected fixed result := by
  induction work using OracleComp.inductionOn generalizing mode before result with
  | pure value =>
      change result∈support (pure (.returned (value,mode),before)) at supported
      obtain rfl := eq_of_mem_support_pure _ supported
      exact ⟨fresh,held⟩
  | query_bind request next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at scope
      by_cases triggered : Trigger selected request
      · rcases request with ((coin|request)|report)|bytes
        · cases triggered
        · cases request with
          | create | reveal handle => cases triggered
          | service handle request => cases request with
            | staticDh peer => cases triggered
            | sign message =>
                obtain ⟨same,tagged⟩ := triggered
                subst handle
                obtain ⟨later,queryEq⟩ := selecting_query selected placeholder message mode held tagged
                simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind] at supported
                rw [queryEq,bind_assoc,RegistrationNativeIdentityTemplateSelectionCut.Original.step] at supported
                simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
                cases supported
                exact ⟨fresh,scope.1 tagged⟩
        · cases triggered
        · cases triggered
      · simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind] at supported
        rw [forward_query selected placeholder request mode held triggered,bind_assoc] at supported
        simp only [pure_bind] at supported
        rw [forward_stop] at supported
        simp only [simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
        obtain ⟨middle,called,continued⟩ := supported
        have projected : (middle.1,(middle.2.pool,middle.2.hash))∈support
            ((RegistrationNativePlatformIdentityCtxSource.implementation joint request).run (before.pool,before.hash)) := by
          rw [←forward_source joint selected placeholder masked request before,support_map]
          exact ⟨middle,called,rfl⟩
        have other : request≠.inl (.inl (.inr (.service selected (.sign fixed)))) := by
          intro same
          subst request
          exact triggered ⟨rfl,role⟩
        have retained := original_fresh joint selected fixed request other (before.pool,before.hash)
          (middle.1,(middle.2.pool,middle.2.hash)) projected fresh role
        have armed : Armed (RegistrationNativeIdentityCensorPrefix.next mode request) := by
          cases request <;> exact held
        exact ih middle.1 (scope.2 middle.1) _ armed middle.2 retained result continued

/-- Resuming that same cut cannot produce a newly signed fixed message without having stopped at its selector. -/
theorem selected (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (fixed : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime fixed=true)
    (work : OracleComp Source A) (scope : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (mode : Mode) (held : Armed mode) (before : State) (fresh : fixed∉poolMessages selected before.pool)
    (cut : Cut (A × Mode) × State)
    (stopped : cut∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.stop
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode))).run before))
    (result : (A × Mode) × State)
    (resumed : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      (RegistrationNativeIdentityTemplateSelectionCut.Original.resume cut.1)).run cut.2))
    (member : fixed∈poolMessages selected result.2.pool) :
    ∃ continued,cut.1=RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected fixed continued ∧ fixed∉poolMessages selected cut.2.pool := by
  have facts := RegistrationNativeIdentityCensorFirstSelectorPrefix.stopped joint selected placeholder masked fixed role work scope mode held before fresh cut stopped
  rcases cut with ⟨cut,current⟩
  cases cut with
  | returned value =>
      change result∈support (pure (value,current)) at resumed
      obtain rfl := eq_of_mem_support_pure _ resumed
      exact False.elim (facts.1 member)
  | selected message continued =>
      have same : message=fixed := facts.2
      exact ⟨continued,congrArg (fun m=>RegistrationNativeIdentityTemplateSelectionCut.Original.Cut.selected m continued) same,facts.1⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix.stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorPrefix.selected
