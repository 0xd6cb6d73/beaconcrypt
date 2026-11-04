-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen
/-! Supported successful corrected OPEN control retains its own actual reserve, authentication and agreement calls under any persistent private interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerReady ServerState)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {I KemSK Private A B : Type} {base : OracleSpec I}
abbrev State (Private : Type) := ServerState × (Environment × Private)
abbrev Work (Private : Type) := RegistrationNativePlatformSecretWordOpen.PublicM (StateT Private ProbComp)

def close (work : Work Private A) : StateT (State Private) ProbComp A := fun before =>
  (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2)))) <$>
    (((work.run before.1).run before.2.1).run before.2.2)

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value,before) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before,before) := rfl

private theorem pure_run (value : A) (before : State Private) :
    (close (pure value)).run before = pure (value,before) := by
  simp only [close,StateT.run,pure_apply,map_pure]
private theorem get_run (before : State Private) :
    (close get).run before = pure (before.1,before) := by
  simp only [close,StateT.run,get_apply,pure_apply,map_pure]
private theorem bind_run (work : Work Private A) (next : A → Work Private B) (before : State Private) :
    (close (work >>= next)).run before = (do let reached ← (close work).run before; (close (next reached.1)).run reached.2) := by
  simp only [close,StateT.run,bind_apply,map_bind,bind_map_left]
private theorem retain_run (ready : ServerReady) (before : State Private) :
    (close (RegistrationNativePlatformSecretWordOpen.retain ready)).run before =
      match RegistrationNativeSecretWordServerMaterial.retain ready before.1 with
      | .fail error => pure (.fail error,before)
      | .div => pure (.div,before)
      | .ok (reply,after) => pure (.ok reply,(after,before.2)) := by
  cases kept : RegistrationNativeSecretWordServerMaterial.retain ready before.1 <;>
    simp only [close,RegistrationNativePlatformSecretWordOpen.retain,kept,StateT.run,pure_apply,map_pure]

/-- A successful one-use retain stores exactly its supplied Ready at its returned slot. -/
theorem retain_stored (ready : ServerReady) (before after : State Private) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support
      ((close (RegistrationNativePlatformSecretWordOpen.retain ready)).run before)) :
    after.1.sessions[handle]? = some (some ready) ∧ after.2 = before.2 := by
  rw [RegistrationNativePlatformLorSourceRetainedControl.retain_run] at supported
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

variable (setup : Setup base KemSK) (checks : Checks)
    (localImpl : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT Private ProbComp))
    (reserve : StateT Private ProbComp Bool)
    (packet : registration.InitPacket)

/-- Actual reservation is followed by the very agreement whose Ready is retained on success. -/
theorem after_authentication (authenticated : registration.AuthenticatedInit)
    (before after : State Private) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.afterAuthentication localImpl reserve setup checks packet authenticated)).run before)) :
    ∃ reserved ready agreed,
      reserved ∈ support ((close (StateT.lift (StateT.lift reserve))).run before) ∧
      reserved.1 = true ∧
      agreed ∈ support ((close
        (RegistrationNativePlatformSecretWordOpen.agreement localImpl setup checks packet authenticated)).run reserved.2) ∧
      agreed.1 = .ok (some ready) ∧
      (.ok (some handle),after) ∈ support ((close
        (RegistrationNativePlatformSecretWordOpen.retain ready)).run agreed.2) ∧
      after.1.sessions[handle]? = some (some ready) := by
  rw [RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    RegistrationNativePlatformLorSourceRetainedControl.bind_run,
    RegistrationNativePlatformLorSourceRetainedControl.get_run,pure_bind] at supported
  split at supported
  · rw [RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
    cases supported
  · rw [RegistrationNativePlatformLorSourceRetainedControl.bind_run,mem_support_bind_iff] at supported
    obtain ⟨reserved,called,supported⟩ := supported
    cases allowed : reserved.1 with
    | false =>
      simp only [allowed,Bool.false_eq_true,ite_false,
        RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
      cases supported
    | true =>
      simp only [allowed,ite_true,RegistrationNativePlatformLorSourceRetainedControl.bind_run,
        mem_support_bind_iff] at supported
      obtain ⟨agreed,reached,supported⟩ := supported
      cases outcome : agreed.1 with
      | fail error | div =>
        simp only [outcome,RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
        cases supported
      | ok value => cases value with
        | none =>
          simp only [outcome,RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
          cases supported
        | some ready =>
          simp only [outcome] at supported
          exact ⟨reserved,ready,agreed,called,allowed,reached,outcome,supported,
            (retain_stored ready agreed.2 after handle supported).1⟩

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  RegistrationNativePlatformServerReferenceAccept.pin

/-- The corrected post-pin callback exposes its actual successful mandatory authentication. -/
theorem after_pin (verify : MldsaTranscriptAuth.Verify) (current : RegistrationNativeServerPinRecompute.PinReply)
    (before after : State Private) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.afterPin localImpl reserve setup checks verify packet current)).run before)) :
    ∃ pin events authenticated checked,
      current = .ok (.Some pin) ∧
      checked ∈ support ((close (StateT.lift (StateT.lift
        (simulateQ (RegistrationNativePlatformSecretWordOpen.effects localImpl)
          (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet))))).run before) ∧
      checked.1 = .ok (events,.Accepted authenticated) ∧
      (.ok (some handle),after) ∈ support ((close
        (RegistrationNativePlatformSecretWordOpen.afterAuthentication localImpl reserve setup checks packet authenticated)).run checked.2) := by
  cases current with
  | fail error | div =>
    rw [RegistrationNativePlatformSecretWordOpen.afterPin,
      RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
    cases supported
  | ok value => cases value with
    | none =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
      cases supported
    | some pin =>
      rw [RegistrationNativePlatformSecretWordOpen.afterPin,
        RegistrationNativePlatformLorSourceRetainedControl.bind_run,mem_support_bind_iff] at supported
      obtain ⟨checked,called,supported⟩ := supported
      cases checkedEq : checked.1 with
      | fail error | div =>
        simp only [checkedEq,RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
        cases supported
      | ok checkedValue =>
        rcases checkedValue with ⟨events,verdict⟩
        cases verdict <;> simp only [checkedEq] at supported
        all_goals try {
          rw [RegistrationNativePlatformLorSourceRetainedControl.pure_run,mem_support_pure_iff] at supported
          cases supported }
        case Accepted authenticated => exact ⟨pin,events,authenticated,checked,rfl,called,checkedEq,supported⟩

/-- Successful corrected OPEN acceptance retains the actual repeated-pin call and supported continuation. -/
theorem accept (verify : MldsaTranscriptAuth.Verify) (before after : State Private) (handle : Nat)
    (supported : (.ok (some handle),after) ∈ support ((close
      (RegistrationNativePlatformSecretWordOpen.accept localImpl reserve setup checks verify packet)).run before)) :
    ∃ pinned,
      pinned ∈ support ((close (StateT.lift (StateT.lift
        (RegistrationNativePlatformServerReferenceAccept.pin
          (RegistrationNativePlatformSecretWordOpen.effects localImpl) before.1.pin)))).run before) ∧
      (.ok (some handle),after) ∈ support ((close
        (RegistrationNativePlatformSecretWordOpen.afterPin localImpl reserve setup checks verify packet pinned.1)).run pinned.2) := by
  rw [RegistrationNativePlatformSecretWordOpen.accept,
    RegistrationNativePlatformLorSourceRetainedControl.bind_run,
    RegistrationNativePlatformLorSourceRetainedControl.get_run,pure_bind,
    RegistrationNativePlatformLorSourceRetainedControl.bind_run,mem_support_bind_iff] at supported
  exact supported

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.retain_stored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.retain_stored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRetainedControl.accept
