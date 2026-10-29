-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationRecordPrimitives
import BeaconcryptCore.Refinement.KeyAgreement
import VCVio.OracleComp.CanReturn

/-!
This controller invokes the actual extracted agreement getters and resumes. The primitive interface retains source secret roles, optional conversion/KEM/DH replies and the complete root request. Nine steps cover the longest native entry path; a terminal effect remains terminal and a fuel boundary returns the reached effect without inventing rejection or completion. Native completion therefore remains an actual capability consumed by the first-record controllers.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationAgreementExecutor

inductive Request where
  | convertPublic (key : Array Std.U8 32#usize)
  | convertSecret (role : agreement.DhSecretRole)
  | generate (role : agreement.EphemeralRole)
  | encapsulate (key : core.option.Option (Array Std.U8 1184#usize))
  | decapsulate (ciphertext : core.option.Option (Array Std.U8 1088#usize))
  | dh (request : agreement.DhRequest)
  | root (request : agreement.RootKdfRequest)

def Spec : OracleSpec Request
  | .convertPublic _ => core.option.Option (Array Std.U8 32#usize)
  | .convertSecret _ => Bool
  | .generate _ => core.option.Option (Array Std.U8 32#usize)
  | .encapsulate _ => core.option.Option (Array Std.U8 1088#usize × Array Std.U8 32#usize)
  | .decapsulate _ => core.option.Option (Array Std.U8 32#usize)
  | .dh _ => core.option.Option (Array Std.U8 32#usize)
  | .root _ => core.option.Option (Array Std.U8 32#usize)

def continueWith {Input : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM agreement.AgreementEffect)) :
    OracleComp Spec (RustM agreement.AgreementEffect) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def step : agreement.AgreementEffect → OracleComp Spec (RustM agreement.AgreementEffect)
  | .ConvertPublic pending => continueWith pending.public_key fun request => do
      let reply ← Spec.query (.convertPublic request)
      pure (pending.resume reply)
  | .ConvertSecret pending => continueWith pending.secret_role fun request => do
      let reply ← Spec.query (.convertSecret request)
      pure (pending.resume reply)
  | .GenerateEphemeral pending => continueWith pending.role fun request => do
      let reply ← Spec.query (.generate request)
      pure (pending.resume reply)
  | .Encapsulate pending => continueWith pending.public_key fun request => do
      let reply ← Spec.query (.encapsulate request)
      pure (pending.resume reply)
  | .Decapsulate pending => continueWith pending.ciphertext fun request => do
      let reply ← Spec.query (.decapsulate request)
      pure (pending.resume reply)
  | .Dh pending => continueWith pending.request fun request => do
      let reply ← Spec.query (.dh request)
      pure (pending.resume reply)
  | .RootKdf pending => continueWith pending.request fun request => do
      let reply ← Spec.query (.root request)
      pure (pending.resume reply)
  | terminal@(.Rejected _) => pure (.ok terminal)
  | terminal@(.ServerComplete _) => pure (.ok terminal)
  | terminal@(.BeaconComplete _) => pure (.ok terminal)

def drive : Nat → agreement.AgreementEffect → OracleComp Spec (RustM agreement.AgreementEffect)
  | 0, phase => pure (.ok phase)
  | fuel + 1, phase => do
      let next ← step phase
      continueWith next (drive fuel)

def server (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) : OracleComp Spec (RustM agreement.AgreementEffect) :=
  continueWith (agreement.begin_server_agreement control status authenticated) (drive 9)

def beacon (authenticated : registration.AuthenticatedResponse) :
    OracleComp Spec (RustM agreement.AgreementEffect) :=
  continueWith (agreement.begin_beacon_agreement authenticated) (drive 9)

/-- Every edge records the actual getter operand and actual source continuation. -/
inductive Step : agreement.AgreementEffect → agreement.AgreementEffect → Prop where
  | convertPublic (pending) (request) (reply) (final)
      (requested : pending.public_key = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.ConvertPublic pending) final
  | convertSecret (pending) (request) (reply) (final)
      (requested : pending.secret_role = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.ConvertSecret pending) final
  | generate (pending) (request) (reply) (final)
      (requested : pending.role = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.GenerateEphemeral pending) final
  | encapsulate (pending) (request) (reply) (final)
      (requested : pending.public_key = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.Encapsulate pending) final
  | decapsulate (pending) (request) (reply) (final)
      (requested : pending.ciphertext = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.Decapsulate pending) final
  | dh (pending) (request) (reply) (final)
      (requested : pending.request = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.Dh pending) final
  | root (pending) (request) (reply) (final)
      (requested : pending.request = .ok request) (resumed : pending.resume reply = .ok final) :
      Step (.RootKdf pending) final
  | rejected (aborted) : Step (.Rejected aborted) (.Rejected aborted)
  | server (completed) : Step (.ServerComplete completed) (.ServerComplete completed)
  | beacon (completed) : Step (.BeaconComplete completed) (.BeaconComplete completed)

inductive Run : agreement.AgreementEffect → agreement.AgreementEffect → Prop where
  | refl (phase) : Run phase phase
  | cons {initial middle final} (first : Step initial middle) (rest : Run middle final) : Run initial final

private theorem continueWith_support {Input : Type} (result : RustM Input)
    (next : Input → OracleComp Spec (RustM agreement.AgreementEffect)) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (continueWith result next)) :
    ∃ value, result = .ok value ∧ .ok final ∈ support (next value) := by
  cases result <;> simp_all [continueWith]

private theorem query_resume_support (query : Request)
    (resume : Spec.Range query → RustM agreement.AgreementEffect) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (do
      let reply ← (Spec.query query : OracleComp Spec _)
      pure (resume reply))) :
    ∃ reply, resume reply = .ok final := by
  simp only [mem_support_bind_iff] at supported
  obtain ⟨reply, _, returned⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff] at returned
  exact ⟨reply, returned.symm⟩

theorem step_sound (initial final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (step initial)) : Step initial final := by
  cases initial with
  | ConvertPublic pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.public_key _ final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.convertPublic request) pending.resume final called
      exact .convertPublic pending request reply final requested resumed
  | ConvertSecret pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.secret_role
        (fun request => do let reply ← (Spec.query (.convertSecret request) : OracleComp Spec _); pure (pending.resume reply))
        final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.convertSecret request) pending.resume final called
      exact .convertSecret pending request reply final requested resumed
  | GenerateEphemeral pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.role
        (fun request => do let reply ← (Spec.query (.generate request) : OracleComp Spec _); pure (pending.resume reply))
        final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.generate request) pending.resume final called
      exact .generate pending request reply final requested resumed
  | Encapsulate pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.public_key _ final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.encapsulate request) pending.resume final called
      exact .encapsulate pending request reply final requested resumed
  | Decapsulate pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.ciphertext _ final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.decapsulate request) pending.resume final called
      exact .decapsulate pending request reply final requested resumed
  | Dh pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.request _ final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.dh request) pending.resume final called
      exact .dh pending request reply final requested resumed
  | RootKdf pending =>
      obtain ⟨request, requested, called⟩ := continueWith_support pending.request _ final supported
      obtain ⟨reply, resumed⟩ := query_resume_support (.root request) pending.resume final called
      exact .root pending request reply final requested resumed
  | Rejected aborted =>
      simp only [step, support_pure, Set.mem_singleton_iff, RustM.ok.injEq] at supported
      subst final
      exact .rejected aborted
  | ServerComplete completed =>
      simp only [step, support_pure, Set.mem_singleton_iff, RustM.ok.injEq] at supported
      subst final
      exact .server completed
  | BeaconComplete completed =>
      simp only [step, support_pure, Set.mem_singleton_iff, RustM.ok.injEq] at supported
      subst final
      exact .beacon completed

theorem drive_sound (fuel : Nat) (initial final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (drive fuel initial)) : Run initial final := by
  induction fuel generalizing initial final with
  | zero =>
      simp only [drive, support_pure, Set.mem_singleton_iff, RustM.ok.injEq] at supported
      subst final
      exact .refl initial
  | succ fuel ih =>
      simp only [drive, mem_support_bind_iff] at supported
      obtain ⟨result, first, returned⟩ := supported
      obtain ⟨middle, resultEq, continued⟩ := continueWith_support result _ final returned
      subst result
      exact .cons (step_sound initial middle first) (ih middle final continued)

attribute [local irreducible] drive agreement.begin_server_agreement agreement.begin_beacon_agreement

theorem server_sound (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus)
    (authenticated : registration.AuthenticatedInit) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (server control status authenticated)) :
    ∃ initial, agreement.begin_server_agreement control status authenticated = .ok initial ∧ Run initial final := by
  obtain ⟨initial, started, ran⟩ := continueWith_support _ _ final supported
  exact ⟨initial, started, drive_sound 9 initial final ran⟩

theorem beacon_sound (authenticated : registration.AuthenticatedResponse) (final : agreement.AgreementEffect)
    (supported : .ok final ∈ support (beacon authenticated)) :
    ∃ initial, agreement.begin_beacon_agreement authenticated = .ok initial ∧ Run initial final := by
  obtain ⟨initial, started, ran⟩ := continueWith_support _ _ final supported
  exact ⟨initial, started, drive_sound 9 initial final ran⟩

end BeaconcryptCore.Computational.RegistrationAgreementExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.step_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.step_sound
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.drive_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.drive_sound
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.server_sound
/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementExecutor.beacon_sound
