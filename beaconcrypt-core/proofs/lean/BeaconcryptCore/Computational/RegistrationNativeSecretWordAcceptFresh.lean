-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit

/-! The actual open Word accept controller changes its session table only by appending the exact returned handle's Ready. This support fact holds before every subsequent private interpretation and includes authentication, replay and preparation failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFresh
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

def Shape (before : List (Option ServerReady)) (reply : RustM (Option Nat)) (after : List (Option ServerReady)) : Prop :=
  (after = before ∧ ∀ handle, reply ≠ .ok (some handle)) ∨ ∃ ready, after = before ++ [some ready] ∧ reply = .ok (some before.length)

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem retain_shape (ready : ServerReady) (before : ServerState) (env : Environment)
    (result : (RustM (Option Nat) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.retain (n := n) (KemSK := KemSK) ready).run before).run env)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.consumed with
  | fail error | div =>
      simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
        consumed, StateT.run] at supported
      cases supported
      exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
  | ok pair =>
      rcases pair with ⟨entry, history⟩
      cases entry with
      | none =>
          simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
            consumed, StateT.run] at supported
          cases supported
          exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
      | some token =>
          simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
            consumed, StateT.run] at supported
          cases supported
          exact Or.inr ⟨ready, rfl, rfl⟩

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun result => pure (result, before)) = _
  rw [bind_pure_comp]

private theorem agreement_server (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (result : (RustM (Option ServerReady) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.agreement (n := n) setup checks packet authenticated).run before).run env)) :
    result.1.2 = before := by
  simp only [RegistrationNativeSecretWordServerCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_assoc, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases formed : collected.1 with
  | none =>
      simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some pending =>
      simp only [formed, StateT.run, lift_apply, map_apply, Functor.map_map, support_map] at supported
      obtain ⟨returned, _possible, equal⟩ := supported
      exact (congrArg (fun result => result.1.2) equal).symm

private theorem after_shape (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (result : (RustM (Option Nat) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.afterAuthentication (n := n) setup checks packet authenticated).run before).run env)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  simp only [RegistrationNativeSecretWordServerCompiler.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind] at supported
  split at supported
  · simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
  · split at supported
    · simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      have same := agreement_server setup checks packet authenticated before env completed reached
      cases formed : completed.1.1 with
      | fail error | div =>
          simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl ⟨congrArg (fun server => server.sessions) same, fun handle impossible => by cases impossible⟩
      | ok reply => cases reply with
        | none =>
            simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
            cases supported
            exact Or.inl ⟨congrArg (fun server => server.sessions) same, fun handle impossible => by cases impossible⟩
        | some ready =>
            simp only [formed] at supported
            have shape := retain_shape ready completed.1.2 completed.2 result supported
            simpa only [same] using shape
    · simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Actual acceptance preserves every earlier session or appends one Ready at the returned fresh handle. -/
private theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) (env : Environment)
    (result : (RustM (Option Nat) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.accept (n := n) setup checks verify packet).run before).run env)) :
    Shape before.sessions result.1.1 result.1.2.sessions := by
  rw [RegistrationNativeSecretWordTargetServerReceipt.accept_program_source] at supported
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨checked, _reached, supported⟩ := supported
  cases checked with
  | fail error | div =>
      simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩
  | ok reply =>
      rcases reply with ⟨events, verdict⟩
      cases verdict <;> first
        | exact after_shape setup checks packet _ before env result supported
        | (simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported; cases supported; exact Or.inl ⟨rfl, fun handle impossible => by cases impossible⟩)

/-- A successful actual accept returns its fresh append index and grows the roster by exactly one. -/
theorem success (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) (env : Environment)
    (after : ServerState) (reached : Environment) (handle : Nat)
    (supported : ((.ok (some handle), after), reached) ∈ support
      (((RegistrationNativeSecretWordServerCompiler.accept (n := n) setup checks verify packet).run before).run env)) :
    handle = before.sessions.length ∧ after.sessions.length = before.sessions.length + 1 := by
  have shape := accept setup checks verify packet before env ((.ok (some handle), after), reached) supported
  rcases shape with ⟨_same, impossible⟩ | ⟨ready, same, returned⟩
  · exact (impossible handle rfl).elim
  · simp only [RustM.ok.injEq, Option.some.injEq] at returned
    exact ⟨returned, by simpa only [List.length_append, List.length_singleton] using congrArg List.length same⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFresh.success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFresh.success
