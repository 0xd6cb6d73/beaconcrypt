-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasExposureBound
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatLiteral

/-! A same-run selected installation is either genuinely opaque or exposes the candidate in the existing recovery log event. This uses neither a repeated-role failure nor a new recovery game. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure
open PqxdhJointIdentity (Primitives IdentitySeed DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhKemIndCca (MlKemSharedSecret)
open RegistrationNativeSecretWord (Word)
open RegistrationNativeSecretWordMessage (Message input eval)
open RegistrationNativeSecretWordFrontendTrace (Event)
open PqxdhRecordLiftInterface (Role)

/-- The exact selected installation event either carries the atom or witnesses the already defined same-client recovery exposure. -/
theorem atom_or_exposure (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : MlKemSharedSecret) (target : Option DhOutput)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (role : Role) (message : Message) (bytes : Pqxdh.Bytes)
    (member : Event.install role message ∈ trace.events ∨ Event.installAttempt role message ∈ trace.events)
    (formed : RegistrationNativeRelatedFamily.input joint dh seed scalar (eval candidate message)=some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate bytes=true) :
    message.kem=Word.atom ∨ RegistrationNativeSecretWordAliasExposureBound.Exposure
      (input joint dh seed scalar) (RegistrationNativeSecretWordProtection.inside target) candidate trace := by
  obtain ⟨key,wordFormed,word,value,inside⟩ :=
    RegistrationNativeSecretWordAtomRepeatLiteral.selected_input joint dh seed scalar candidate target message bytes formed selected
  cases shape : message.kem with
  | atom => exact Or.inl rfl
  | literal literal =>
      have same : literal=candidate := by simpa only [word,shape,Word.eval] using value
      subst literal
      exact Or.inr ⟨role,message,key,member,wordFormed,inside,word.trans shape⟩

/-- Outside that exact existing exposure event, the same selected event's KEM operand is the genuine atom. -/
theorem no_exposure_atom (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : MlKemSharedSecret) (target : Option DhOutput)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (role : Role) (message : Message) (bytes : Pqxdh.Bytes)
    (member : Event.install role message ∈ trace.events ∨ Event.installAttempt role message ∈ trace.events)
    (formed : RegistrationNativeRelatedFamily.input joint dh seed scalar (eval candidate message)=some bytes)
    (selected : RegistrationNativeSelectiveHiddenService.selected (RegistrationNativeKeyFamilyPreparation.inside target) candidate bytes=true)
    (safe : ¬RegistrationNativeSecretWordAliasExposureBound.Exposure
      (input joint dh seed scalar) (RegistrationNativeSecretWordProtection.inside target) candidate trace) :
    message.kem=Word.atom :=
  (atom_or_exposure joint dh seed scalar candidate target trace role message bytes member formed selected).resolve_right safe

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure.atom_or_exposure' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure.atom_or_exposure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure.no_exposure_atom' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposure.no_exposure_atom
