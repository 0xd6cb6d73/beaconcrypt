-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
/-! A genuinely retained Server Ready carries the exact descriptor requested at its own earlier preparation in the same actual source trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedAccept
open RegistrationNativeSecretWordInterface (Spec LocalSpec prepare liftLocal)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared prepare_recorded)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformLorSourceRetainedCore (lower Auxiliary)
variable {n : Nat} {I KemSK Private Reader E A B : Type} {base : OracleSpec I}
variable (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp)) (input : Message → Option Key)
variable (echo : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) →
  result.1=(input message).map (fun _=>message))
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
local notation "Trace" => RegistrationNativeSecretWordFrontendTrace.State

attribute [local irreducible] RegistrationNativePlatformLorStatefulSupport.trace
  RegistrationAuthenticationCompiler.program PqxdhDeploymentTranscript.acceptedKeys RegistrationNativePlatformServerReferenceAccept.pin
open RegistrationNativePlatformLorSourceRetainedControl (close State)
private theorem agreement_support (setup : Setup base KemSK) (checks : Checks) (routed : Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State (Trace × Private)) (result : RustM (Option ServerReady) × State (Trace × Private))
    (supported : result ∈ support ((close (RegistrationNativePlatformSecretWordOpen.agreement (actual ∘ₛ liftLocal routed) setup checks packet authenticated)).run before)) :
    ((result.1,result.2.1),(result.2.2.1,result.2.2.2)) ∈ support
      ((lower (actual ∘ₛ liftLocal routed) ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run (before.2.1,before.2.2)) := by
  have sourceEq : (close (RegistrationNativePlatformSecretWordOpen.agreement (actual ∘ₛ liftLocal routed) setup checks packet authenticated)).run before =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (lower (actual ∘ₛ liftLocal routed) ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run (before.2.1,before.2.2) := by
    simp only [RegistrationNativePlatformLorSourceRetainedControl.close,RegistrationNativePlatformSecretWordOpen.agreement,
      RegistrationNativePlatformLorSourceRetainedCore.lower,StateT.run,Functor.map_map]
  rw [sourceEq,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  exact called

include echo in
/-- A successful actual OPEN accept stores its own Ready with an earlier preparation in its same returned trace. -/
theorem accept_prepared (setup : Setup base KemSK) (checks : Checks) (routed : Bool)
    (reserve : StateT (Trace × Private) ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before after : State (Trace × Private)) (handle : Nat)
    (supported : (.ok (some handle),after)∈support ((close
      (RegistrationNativePlatformSecretWordOpen.accept (actual ∘ₛ liftLocal routed) reserve setup checks verify packet)).run before)) :
    ∃ready : ServerReady,after.1.sessions[handle]?=some (some ready) ∧Prepared ready.reference after.2.2.1 := by
  obtain ⟨pinned,_pinAt,afterPinAt⟩ := RegistrationNativePlatformLorSourceRetainedControl.accept setup checks
    (actual ∘ₛ liftLocal routed) reserve packet verify before after handle supported
  obtain ⟨_pin,_events,authenticated,checked,_pinReply,_authenticatedAt,_checkedReply,afterAuthenticationAt⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_pin setup checks (actual ∘ₛ liftLocal routed) reserve packet verify pinned.1 pinned.2 after handle afterPinAt
  obtain ⟨_reserved,ready,agreed,_reservedAt,_admitted,agreedAt,agreedReply,retainedAt,stored⟩ :=
    RegistrationNativePlatformLorSourceRetainedControl.after_authentication setup checks (actual ∘ₛ liftLocal routed) reserve packet authenticated checked.2 after handle afterAuthenticationAt
  have localAgreement := agreement_support implementation setup checks routed packet authenticated _ agreed agreedAt
  rw [agreedReply] at localAgreement
  have prepared := RegistrationNativePlatformLorSourcePreparedAgreement.agreement_prepared implementation input echo
    setup checks routed packet authenticated _ _ _ _ ready localAgreement
  have unchanged := (RegistrationNativePlatformLorSourceRetainedControl.retain_stored ready agreed.2 after handle retainedAt).2
  refine ⟨ready,stored,?_⟩
  rw [unchanged]
  exact prepared
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedAccept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedAccept.accept_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedAccept.accept_prepared
