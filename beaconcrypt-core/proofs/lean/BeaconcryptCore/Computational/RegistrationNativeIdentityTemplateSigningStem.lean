-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOperational
/-! The actual armed one-time signing call exposes its first selector and literal accepted-choice scan/omission continuation before any private source interpretation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old Cut stop)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {A : Type}
private theorem promote_run (work : StateT Mode (OracleComp RegistrationNativeIdentityCensorCompiler.Spec) A) (before : Mode) :
    (RegistrationNativeIdentityCensorOperational.promote work).run before =
      simulateQ RegistrationNativeIdentityCensorOperational.embed (work.run before) := rfl

/-- The literal source signing call selects its current one-time message first; a positive reply scans the complete current prefix, then issues exactly the canonical omission marker before resuming. -/
theorem selection_tail (selected : Nat) (message : Pqxdh.Bytes) (mode : Mode)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (arming : mode.armed = true) (held : mode.target = none) (inactive : mode.active = false) :
    ∃ continued : Bool → OracleComp Old (Option Ed25519Signature × Mode),
      stop ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode) =
        pure (Cut.selected message continued) ∧
      continued true = (do
          let _ ← Old.query (.inl (.inl (.inr (message,mode.knownInputs))))
          let answer ← Old.query (.inr (.omitted selected message))
          pure (answer, {mode with active := true,target := some message})) := by
  rcases mode with ⟨bundles,armed,active,target,inputs⟩
  change armed = true at arming
  change target = none at held
  change active = false at inactive
  subst armed
  subst target
  subst active
  have prepared : (RegistrationNativeIdentityCensorCompiler.prepare selected selected message).run
      ⟨bundles,true,false,none,inputs⟩ = (do
        let chosen ← RegistrationNativeIdentityCensorCompiler.select message
        if chosen then RegistrationNativeIdentityCensorCompiler.inspect message inputs else pure ()
        pure ((), (⟨bundles,true,(if chosen then some message else none) == some message,
          (if chosen then some message else none),inputs⟩ : Mode))) := by
    simp [RegistrationNativeIdentityCensorCompiler.prepare, StateT.run, role]
  simp only [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, promote_run,
    prepared, simulateQ_bind, RegistrationNativeIdentityCensorCompiler.select, simulateQ_spec_query,
    RegistrationNativeIdentityCensorOperational.embed, bind_assoc]
  rw [RegistrationNativeIdentityTemplateSelectionCut.Original.step]
  refine ⟨_,rfl,?_⟩
  simp [RegistrationNativeIdentityCensorCompiler.inspect, RegistrationNativeIdentityCensorOperational.embed,
    StateT.run_lift]
  rfl

/-- The literal source signing call selects its current one-time message first; a positive reply scans the complete current prefix, then issues exactly the canonical omission marker before resuming. -/
theorem selection (selected : Nat) (message : Pqxdh.Bytes) (mode : Mode)
    (role : RegistrationNativeIdentitySigningRole.oneTime message = true)
    (arming : mode.armed = true) (held : mode.target = none) (inactive : mode.active = false) :
    ∃ continued : Bool → OracleComp Old (Option Ed25519Signature × Mode),
      stop ((RegistrationNativeIdentityCensorOperational.signing selected selected message).run mode) =
        pure (Cut.selected message continued) ∧
      ∃ rest : Option Ed25519Signature → OracleComp Old (Option Ed25519Signature × Mode),
        continued true = (do
          let _ ← Old.query (.inl (.inl (.inr (message,mode.knownInputs))))
          let answer ← Old.query (.inr (.omitted selected message))
          rest answer) := by
  obtain ⟨continued,cut,rest⟩ := selection_tail selected message mode role arming held inactive
  exact ⟨continued,cut,fun answer => pure (answer,{mode with active := true,target := some message}),rest⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem.selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem.selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem.selection_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSigningStem.selection_tail
