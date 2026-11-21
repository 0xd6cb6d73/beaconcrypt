-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelection
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectionPrefixForward
/-! A genuine forwarded prefix precedes the same first-selector coupling, with its complete reached private state and original continuation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionBind
open RegistrationNativeIdentityTemplateSelectionCut.Original (Old)
variable {A X : Type}

/-- The actual forwarded source prefix can be executed before the same plain first-selector stop/resume coupling. -/
theorem source (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (placeholder : PqxdhEd25519EufCma.Ed25519Signature) (work : OracleComp Old X)
    (next : X → OracleComp Old A) (allowed : work.AllQueriesSatisfy RegistrationNativeIdentityTemplatePublicPrefix.Allowed)
    (before : RegistrationNativeIdentityCensorSource.State) :
    RegistrationNativeIdentityCensorPlainSelection.coupled joint selected placeholder (work >>=next) before=(do
      let middle←(simulateQ (RegistrationNativeIdentityCensorSource.censored joint selected placeholder) work).run before
      RegistrationNativeIdentityCensorPlainSelection.coupled joint selected placeholder (next middle.1) middle.2) := by
  unfold RegistrationNativeIdentityCensorPlainSelection.coupled
  rw [RegistrationNativeIdentityTemplateSelectionPrefixScope.stop_bind_forwarded work next allowed]
  simp only [simulateQ_bind,StateT.run_bind,bind_assoc]
end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionBind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionBind.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPlainSelectionBind.source
