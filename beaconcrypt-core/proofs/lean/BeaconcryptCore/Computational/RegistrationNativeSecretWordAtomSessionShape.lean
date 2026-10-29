-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit

/-! The actual open Word accept controller changes its session table only by appending the exact returned handle's Ready. This support fact holds before every subsequent private interpretation and includes authentication, replay and preparation failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationNativeSecretWordInterface (LocalSpec)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

def Shape (before : List (Option ServerReady)) (reply : RustM (Option Nat)) (after : List (Option ServerReady)) : Prop :=
  after = before ∨ ∃ ready, after = before ++ [some ready] ∧ reply = .ok (some before.length)

private theorem weight_le (ready : ServerReady) : RegistrationNativeSecretWordAtomSessionCredit.weight (some ready) ≤ 1 := by
  cases formed : ready.reference.kem <;> simp only [RegistrationNativeSecretWordAtomSessionCredit.weight, formed] <;> decide

/-- One actual append can create at most one atom token, independently of aliases among stored descriptors. -/
theorem count_le (before after : List (Option ServerReady)) (reply : RustM (Option Nat))
    (shape : Shape before reply after) :
    RegistrationNativeSecretWordAtomSessionCredit.count after ≤ RegistrationNativeSecretWordAtomSessionCredit.count before + 1 := by
  rcases shape with same | ⟨ready, same, _returned⟩
  · rw [same]
    omega
  · rw [same, RegistrationNativeSecretWordAtomSessionCredit.append]
    simp only [RegistrationNativeSecretWordAtomSessionCredit.count, Nat.add_zero]
    have bounded := weight_le ready
    omega

/-- A returned ordinary reference prevents an actual append from creating any atom token. -/
theorem count_ordinary (before after : List (Option ServerReady)) (reply : RustM (Option Nat))
    (shape : Shape before reply after)
    (ordinary : ∀ handle, reply = .ok (some handle) → ∃ ready, after[handle]? = some (some ready) ∧
      RegistrationNativeSecretWordAtomSessionCredit.weight (some ready) = 0) :
    RegistrationNativeSecretWordAtomSessionCredit.count after = RegistrationNativeSecretWordAtomSessionCredit.count before := by
  rcases shape with same | ⟨ready, same, returned⟩
  · rw [same]
  · obtain ⟨other, found, zero⟩ := ordinary before.length returned
    rw [same, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero] at found
    have equal := Option.some.inj (Option.some.inj found)
    subst other
    rw [same, RegistrationNativeSecretWordAtomSessionCredit.append]
    simp only [RegistrationNativeSecretWordAtomSessionCredit.count, zero, Nat.add_zero]

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
      exact Or.inl rfl
  | ok pair =>
      rcases pair with ⟨entry, history⟩
      cases entry with
      | none =>
          simp only [RegistrationNativeSecretWordServerCompiler.retain, RegistrationNativeSecretWordServerMaterial.retain,
            consumed, StateT.run] at supported
          cases supported
          exact Or.inl rfl
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
    exact Or.inl rfl
  · split at supported
    · simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      have same := agreement_server setup checks packet authenticated before env completed reached
      cases formed : completed.1.1 with
      | fail error | div =>
          simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl (congrArg (fun server => server.sessions) same)
      | ok reply => cases reply with
        | none =>
            simp only [formed, StateT.run_pure, mem_support_pure_iff] at supported
            cases supported
            exact Or.inl (congrArg (fun server => server.sessions) same)
        | some ready =>
            simp only [formed] at supported
            have shape := retain_shape ready completed.1.2 completed.2 result supported
            simpa only [same] using shape
    · simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Actual acceptance preserves every earlier session or appends one Ready at the returned fresh handle. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
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
      exact Or.inl rfl
  | ok reply =>
      rcases reply with ⟨events, verdict⟩
      cases verdict <;> first
        | exact after_shape setup checks packet _ before env result supported
        | (simp only [StateT.run, pure_apply, mem_support_pure_iff] at supported; cases supported; exact Or.inl rfl)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape.count_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape.count_le
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape.count_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionShape.count_ordinary
