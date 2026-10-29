-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt

/-! The actual open Word accept controller preserves the original Server authentication pin through authentication, replay admission, collection, preparation and retention. The support receipt precedes every arbitrary private interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem retain_pin (ready : ServerReady) (before : ServerState) (env : Environment)
    (result : (RustM (Option Nat) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.retain (n := n) (KemSK := KemSK) ready).run before).run env)) :
    result.1.2.pin = before.pin := by
  cases consumed : RegistrationReplaySchedule.consume
      (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.consumed with
  | fail error | div =>
      simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
        consumed, StateT.run] at supported
      cases supported
      rfl
  | ok pair =>
      rcases pair with ⟨entry, history⟩
      cases entry with
      | none =>
          simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
            consumed, StateT.run] at supported
          cases supported
          rfl
      | some token =>
          simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
            consumed, StateT.run] at supported
          cases supported
          rfl

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

private theorem after_pin (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment)
    (result : (RustM (Option Nat) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.afterAuthentication (n := n) setup checks packet authenticated).run before).run env)) :
    result.1.2.pin = before.pin := by
  simp only [RegistrationNativeSecretWordServerCompiler.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind] at supported
  split at supported
  · simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
    cases supported
    rfl
  · split at supported
    · simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      have same := agreement_server setup checks packet authenticated before env completed reached
      cases formed : completed.1.1 with
      | fail error | div =>
          simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          exact congrArg (fun server => server.pin) same
      | ok reply => cases reply with
        | none =>
            simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
            cases supported
            exact congrArg (fun server => server.pin) same
        | some ready =>
            simp only [formed] at supported
            have shape := retain_pin ready completed.1.2 completed.2 result supported
            simpa only [same] using shape
    · simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
      cases supported
      rfl

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Actual acceptance keeps the original Server authentication pin on every outcome. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) (env : Environment)
    (result : (RustM (Option Nat) × ServerState) × Environment)
    (supported : result ∈ support (((RegistrationNativeSecretWordServerCompiler.accept (n := n) setup checks verify packet).run before).run env)) :
    result.1.2.pin = before.pin := by
  rw [RegistrationNativeSecretWordTargetServerReceipt.accept_program_source] at supported
  simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨checked, _reached, supported⟩ := supported
  cases checked with
  | fail error | div =>
      simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok reply =>
      rcases reply with ⟨events, verdict⟩
      cases verdict <;> first
        | exact after_pin setup checks packet _ before env result supported
        | (simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported; cases supported; rfl)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPin.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPin.accept
