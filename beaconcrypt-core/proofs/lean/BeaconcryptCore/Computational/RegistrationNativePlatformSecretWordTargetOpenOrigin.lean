-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter
/-! Successful corrected OPEN control exposes the same reserve, authentication and agreement calls rather than a separate existential session. The complete Server/environment/platform/private states and all failure arms remain in the actual support relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerReady)
open RegistrationNativePlatformSecretWordAtomOpenRun (State Base close)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I}
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
  (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))

/-- A successful one-use retain stores exactly its supplied Ready at its returned slot. -/
theorem retain_stored (ready : ServerReady) (before after : State n KemSK Platform) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support
      ((close implementation (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    after.1.sessions[handle]? = some (some ready) ∧ after.2 = before.2 := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.retain_run] at supported
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.1.consumed with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordServerMaterial.retain,consumed,mem_support_pure_iff] at supported
    cases supported
  | ok pair =>
    rcases pair with ⟨entry,history⟩
    cases entry with
    | none =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain,consumed,mem_support_pure_iff] at supported
      cases supported
    | some token =>
      simp only [RegistrationNativeSecretWordServerMaterial.retain,consumed,mem_support_pure_iff,
        Prod.mk.injEq,RustM.ok.injEq,Option.some.injEq] at supported
      obtain ⟨rfl,rfl⟩ := supported
      exact ⟨by simp only [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero],rfl⟩

variable (setup : Setup base KemSK) (checks : Checks) (selected : Bool) (reserve : Base n KemSK Platform Bool)
    (packet : registration.InitPacket)

/-- Actual reservation is followed by the very agreement whose Ready is retained on success. -/
theorem after_authentication (authenticated : registration.AuthenticatedInit)
    (before after : State n KemSK Platform) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal selected) reserve setup checks packet authenticated)).run before)) :
    ∃ reserved ready agreed,
      reserved ∈ support ((close implementation (StateT.lift (StateT.lift reserve))).run before) ∧
      reserved.1 = true ∧
      agreed ∈ support ((close implementation
        (RegistrationNativePlatformSecretWordOpen.agreement (wordLocal selected) setup checks packet authenticated)).run reserved.2) ∧
      agreed.1 = .ok (some ready) ∧
      (.ok (some handle),after) ∈ support ((close implementation
        (RegistrationNativePlatformSecretWordOpen.retain ready)).run agreed.2) ∧
      after.1.sessions[handle]? = some (some ready) := by
  rw [RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
    RegistrationNativePlatformSecretWordAtomOpenRun.get_run,pure_bind] at supported
  split at supported
  · rw [RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
    cases supported
  · rw [RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,mem_support_bind_iff] at supported
    obtain ⟨reserved,called,supported⟩ := supported
    cases allowed : reserved.1 with
    | false =>
      simp only [allowed,Bool.false_eq_true,ite_false,
        RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
      cases supported
    | true =>
      simp only [allowed,ite_true,RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
        mem_support_bind_iff] at supported
      obtain ⟨agreed,reached,supported⟩ := supported
      cases outcome : agreed.1 with
      | fail error | div =>
        simp only [outcome,RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
        cases supported
      | ok value => cases value with
        | none =>
          simp only [outcome,RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
          cases supported
        | some ready =>
          simp only [outcome] at supported
          exact ⟨reserved,ready,agreed,called,allowed,reached,outcome,supported,
            (retain_stored implementation ready agreed.2 after handle supported).1⟩

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativePlatformServerReferenceAccept.pin

/-- The corrected post-pin callback exposes its actual successful mandatory authentication. -/
theorem after_pin (verify : MldsaTranscriptAuth.Verify) (current : RegistrationNativeServerPinRecompute.PinReply)
    (before after : State n KemSK Platform) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal selected) reserve setup checks verify packet current)).run before)) :
    ∃ pin events authenticated checked,
      current = .ok (.Some pin) ∧
      checked ∈ support ((close implementation (StateT.lift (StateT.lift
        (simulateQ (RegistrationNativePlatformSecretWordOpen.effects (wordLocal selected))
          (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet))))).run before) ∧
      checked.1 = .ok (events,.Accepted authenticated) ∧
      (.ok (some handle),after) ∈ support ((close implementation
        (RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal selected) reserve setup checks packet authenticated)).run checked.2) := by
  cases current with
  | fail error | div =>
    rw [RegistrationNativePlatformSecretWordOpen.afterPin,
      RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
    cases supported
  | ok value => cases value with
    | none =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
      cases supported
    | some pin =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,mem_support_bind_iff] at supported
      obtain ⟨checked,called,supported⟩ := supported
      cases checkedEq : checked.1 with
      | fail error | div =>
        simp only [checkedEq,RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
        cases supported
      | ok checkedValue =>
        rcases checkedValue with ⟨events,verdict⟩
        cases verdict <;> simp only [checkedEq] at supported
        all_goals try {
          rw [RegistrationNativePlatformSecretWordAtomOpenRun.pure_run,mem_support_pure_iff] at supported
          cases supported }
        case Accepted authenticated => exact ⟨pin,events,authenticated,checked,rfl,called,checkedEq,supported⟩

/-- Successful corrected OPEN acceptance retains the actual repeated-pin call and supported continuation. -/
theorem accept (verify : MldsaTranscriptAuth.Verify) (before after : State n KemSK Platform) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close implementation
      (RegistrationNativePlatformSecretWordOpen.accept (wordLocal selected) reserve setup checks verify packet)).run before)) :
    ∃ pinned,
      pinned ∈ support ((close implementation (StateT.lift (StateT.lift
        (RegistrationNativePlatformServerReferenceAccept.pin
          (RegistrationNativePlatformSecretWordOpen.effects (wordLocal selected)) before.1.pin)))).run before) ∧
      (.ok (some handle),after) ∈ support ((close implementation
        (RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal selected) reserve setup checks verify packet pinned.1)).run pinned.2) := by
  rw [RegistrationNativePlatformSecretWordOpen.accept,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,
    RegistrationNativePlatformSecretWordAtomOpenRun.get_run,pure_bind,
    RegistrationNativePlatformSecretWordAtomOpenRun.bind_run,mem_support_bind_iff] at supported
  exact supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.retain_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.retain_stored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin.accept
