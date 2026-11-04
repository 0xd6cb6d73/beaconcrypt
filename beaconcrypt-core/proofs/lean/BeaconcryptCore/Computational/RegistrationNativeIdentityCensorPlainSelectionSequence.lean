-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection
/-! The same first-selector coupling factors arbitrary original source sequencing, retaining its literal future-bearing selected continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old Cut stop resume)
variable {A X : Type}

/-- Factor the actual first-selector coupling at an arbitrary original prefix. -/
theorem source (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp Old X)
    (next : X → OracleComp Old A) (before : RegistrationNativeIdentityCensorSource.State) :
    RegistrationNativeIdentityCensorPlainSelection.coupled joint selected placeholder (work >>=next) before=(do
      let cut←(simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (stop work)).run before
      match cut.1 with
      | .returned value=>RegistrationNativeIdentityCensorPlainSelection.coupled joint selected placeholder (next value) cut.2
      | .selected message continued=>do
          let final←(simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
            (resume (.selected message (fun reply=>continued reply >>=next)))).run cut.2
          pure ((Cut.selected message (fun reply=>continued reply >>=next),cut.2),final)) := by
  unfold RegistrationNativeIdentityCensorPlainSelection.coupled
  rw [RegistrationNativeIdentityTemplateSelectionCut.Original.bind]
  simp only [simulateQ_bind,StateT.run_bind,bind_assoc]
  apply bind_congr
  intro cut
  cases cut.1 with
  | returned value=>rfl
  | selected message continued=>simp only [simulateQ_pure,StateT.run_pure,pure_bind]

/-- Resuming the global selected cut executes the same local selected callback before its literal suffix. -/
theorem resume_selected (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (message : Pqxdh.Bytes)
    (continued : Bool → OracleComp Old X) (next : X → OracleComp Old A)
    (before : RegistrationNativeIdentityCensorSource.State) :
    (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
      (resume (.selected message (fun reply=>continued reply >>=next)))).run before=(do
      let middle←(simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder)
        (resume (.selected message continued))).run before
      (simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) (next middle.1)).run middle.2) := by
  have joined : (resume (Cut.selected message continued) >>=next)=resume (Cut.selected message (fun reply=>continued reply >>=next)) := by
    simp only [resume,bind_assoc]
    rfl
  rw [←joined,simulateQ_bind,StateT.run_bind]
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence.resume_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionSequence.resume_selected
