-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSourceFuel
import BeaconcryptCore.PanicFreedom.KeyAgreement
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual Core agreement schedule requires a successful local identity conversion before decapsulation, DH or root derivation. A private readiness guard can therefore be instrumented and erased on the genuine entry program; no key, agreement success or security conclusion is assumed. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard
open RegistrationAgreementExecutor

def NeedsIdentity : agreement.AgreementEffect → Prop
  | .Decapsulate _ | .Dh _ | .RootKdf _ => True
  | _ => False

def Ready (phase : agreement.AgreementEffect) (flag : Bool) : Prop := NeedsIdentity phase → flag = true

private theorem rejected (state : agreement.AgreementState) (final : agreement.AgreementEffect)
    (flag : Bool) (actual : state.reject = .ok final) : Ready final flag := by
  rw [BeaconcryptCore.Refinement.KeyAgreement.rejection_refines] at actual
  cases RustM.ok.inj actual
  exact False.elim

theorem progress {initial final : agreement.AgreementEffect} (edge : Step initial final)
    (flag : Bool) (nonsecret : ∀ pending, initial ≠ .ConvertSecret pending)
    (prior : Ready initial flag) : Ready final flag := by
  cases edge with
  | convertPublic pending request reply final requested resumed =>
    cases reply with
    | none => exact rejected pending.state final flag resumed
    | some key =>
      simp only [agreement.PublicConversionPending.resume] at resumed
      cases RustM.ok.inj resumed
      exact False.elim
  | convertSecret pending request reply final requested resumed =>
    exact False.elim (nonsecret pending rfl)
  | generate pending request reply final requested resumed =>
    cases reply with
    | none => exact rejected pending.state final flag resumed
    | some key =>
      simp only [agreement.EphemeralPending.resume] at resumed
      cases RustM.ok.inj resumed
      exact False.elim
  | encapsulate pending request reply final requested resumed =>
    cases reply with
    | none => exact rejected pending.state final flag resumed
    | some pair =>
      rcases pair with ⟨ciphertext, shared⟩
      simp only [agreement.EncapsulationPending.resume, ratchet.RatchetChain.from_bytes, bind_tc_ok] at resumed
      cases RustM.ok.inj resumed
      exact False.elim
  | decapsulate pending request reply final requested resumed =>
    exact fun _ => prior trivial
  | dh pending request reply final requested resumed =>
    exact fun _ => prior trivial
  | root pending request reply final requested resumed =>
    exact fun _ => prior trivial
  | rejected aborted | server completed | beacon completed => exact False.elim
theorem converted (pending : agreement.SecretConversionPending) (reply : Bool)
    (final : agreement.AgreementEffect) (resumed : pending.resume reply = .ok final) : Ready final reply := by
  cases reply with
  | false =>
    apply rejected pending.state final false
    simpa only [agreement.SecretConversionPending.resume, Bool.false_eq_true, ↓reduceIte] using resumed
  | true => exact fun _ => rfl
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def implementation (base : QueryImpl Spec m) : QueryImpl Spec (StateT Bool m)
  | .convertSecret role => do
    let reply : Bool ← StateT.lift (base (.convertSecret role))
    set reply
    pure reply
  | .dh request => fun flag =>
    match request.secret_role with
    | .LocalIdentity => if flag then (fun reply => (reply, flag)) <$> base (.dh request) else pure (.None, flag)
    | _ => (fun reply => (reply, flag)) <$> base (.dh request)
  | query => StateT.lift (base query)

theorem secret_run (base : QueryImpl Spec m) (role : agreement.DhSecretRole) (flag : Bool) :
    (implementation base (.convertSecret role)).run flag =
      (fun reply => (reply, reply)) <$> base (.convertSecret role) := by
  unfold implementation
  change ((do let reply ← (StateT.lift (base (.convertSecret role)) : StateT Bool m Bool)
              set reply
              pure reply) : StateT Bool m Bool).run flag = _
  simp only [StateT.run_bind, StateT.run_map, StateT.run_lift, StateT.run_set,
      map_pure, bind_pure_comp, Functor.map_map]
  rfl

omit [LawfulMonad m] in
theorem dh_ready (base : QueryImpl Spec m) (request : agreement.DhRequest) :
    (implementation base (.dh request)).run true = (fun reply => (reply, true)) <$> base (.dh request) := by
  rcases request with ⟨role, publicKey⟩
  cases role <;> rfl

theorem drive_erasure (base : QueryImpl Spec m) (fuel : Nat) (phase : agreement.AgreementEffect)
    (flag : Bool) (ready : Ready phase flag) :
    Prod.fst <$> ((simulateQ (implementation base) (drive fuel phase)).run flag) =
      simulateQ base (drive fuel phase) := by
  induction fuel generalizing phase flag with
  | zero => simp only [drive, simulateQ_pure, StateT.run_pure, map_pure]
  | succ fuel ih =>
    cases phase with
    | Rejected aborted | ServerComplete completed | BeaconComplete completed =>
      simp only [drive, step, continueWith, pure_bind]
      exact ih _ flag ready
    | ConvertPublic pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_key_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.public_conversion_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag
      apply progress (.convertPublic pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | ConvertSecret pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_role_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  secret_run, StateT.run_bind,    pure_bind, map_bind, bind_map_left,  bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.secret_conversion_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final reply
      exact converted pending reply final resumed
    | GenerateEphemeral pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_role_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.ephemeral_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag
      apply progress (.generate pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | Encapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_key_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.encapsulation_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag
      apply progress (.encapsulate pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | Decapsulate pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_ciphertext_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.decapsulation_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag
      apply progress (.decapsulate pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
    | Dh pending =>
      have yes : flag = true := ready trivial
      subst flag
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_request_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  dh_ready, StateT.run_bind,    pure_bind, map_bind, bind_map_left,  bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.dh_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final true
      apply progress (.dh pending request reply final requested resumed) true
      · intro secret impossible
        cases impossible
      · exact ready
    | RootKdf pending =>
      obtain ⟨request, requested⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_request_total pending
      simp only [drive, step, requested, continueWith, simulateQ_bind, simulateQ_spec_query,  implementation, StateT.run_bind, StateT.run_lift,   pure_bind, map_bind,   bind_assoc]
      apply bind_congr
      intro reply
      obtain ⟨final, resumed⟩ := BeaconcryptCore.PanicFreedom.KeyAgreement.root_kdf_resume_total pending reply
      rw [resumed]
      simp only []
      apply ih final flag
      apply progress (.root pending request reply final requested resumed) flag
      · intro secret impossible
        cases impossible
      · exact ready
end BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.progress

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.converted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.converted

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.secret_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.secret_run

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.dh_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.dh_ready

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.drive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementIdentityGuard.drive_erasure
