-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret
import BeaconcryptCore.Refinement.RegistrationPublication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! The exact source response publication controller retains its original rollback control and complete binding/kernel on every optional signature or writer outcome. Enclosing writer failure and divergence remain explicit, with every reached stateful effect preserved. -/
namespace BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot
open RegistrationNativePlatformServerPublication (continueWith continueResult ready signing program)
open BeaconcryptCore.Refinement.RegistrationPublication
inductive Request where
  | signing (request : RegistrationSigningShared.Request)
  | encoding (view : registration.SignedResponseView)
abbrev Spec (Encoded : Type) : OracleSpec Request
  | .signing request => RegistrationSigningShared.Spec.Range request
  | .encoding _ => RustM (core.option.Option Encoded)

def Post {Encoded : Type} (candidate : pqxdh.ServerRegistrationCandidate) (binding : session.RegistrationBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) :
    RustM (RegistrationWorldServerPublication.Result Encoded) → Prop
  | .fail _ | .div => True
  | .ok (.Err previous) => previous = candidate.previous_state
  | .ok (.Ok published) => published.control = candidate.next_state ∧
      published.binding = completedBinding binding candidate.key_id ∧ published.kernel = kernel

variable {Encoded : Type}
theorem ready_post (pending : registration.ServerResponseReady)
    (output : RustM (RegistrationWorldServerPublication.Result Encoded))
    (supported : output ∈ support (ready (m := OracleComp (Spec Encoded))
      (fun view => (Spec Encoded).query (.encoding view)) pending)) :
    Post pending.candidate pending.binding pending.kernel output := by
  unfold ready at supported
  cases requested : pending.message with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok view =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨encoded, _called, returned⟩ := supported
    simp only [support_pure, Set.mem_singleton_iff] at returned
    cases returned
    cases encoded with
    | fail error | div => trivial
    | ok encoded =>
      simp only [bind_tc_ok, server_publication_refines]
      cases encoded with
      | none => rfl
      | some bytes => exact ⟨rfl, rfl, rfl⟩

theorem signing_post (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning)
    (output : RustM (RegistrationWorldServerPublication.Result Encoded))
    (supported : output ∈ support (signing (m := OracleComp (Spec Encoded))
      (fun request => (Spec Encoded).query (.signing request))
      (fun view => (Spec Encoded).query (.encoding view)) payload digest pending)) :
    Post pending.candidate pending.binding pending.kernel output := by
  unfold signing at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok request =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨signature, _called, continued⟩ := supported
    cases signature with
    | none =>
      have missing : pending.resume .None = .ok (.Err pending.candidate.previous_state) := rfl
      simp only [missing, continueResult, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rfl
    | some bytes =>
      obtain ⟨result, resumed, fields⟩ := server_signature_admission_refines pending bytes
      rw [resumed] at continued
      cases result with
      | Err previous =>
        simp only [continueResult, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact fields.1
      | Ok next =>
        change output ∈ support (ready _ next) at continued
        have retained := ready_post next output continued
        simpa only [fields.1, fields.2.1, fields.2.2.1] using retained

theorem program_post (pending : registration.ServerResponseHash)
    (output : RustM (RegistrationWorldServerPublication.Result Encoded))
    (supported : output ∈ support (program (m := OracleComp (Spec Encoded))
      (fun request => (Spec Encoded).query (.signing request))
      (fun view => (Spec Encoded).query (.encoding view)) pending)) :
    Post pending.candidate pending.binding pending.kernel output := by
  unfold program at supported
  cases requested : pending.request with
  | fail error | div =>
    simp only [requested, continueWith, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    trivial
  | ok request =>
    simp only [requested, continueWith, mem_support_bind_iff] at supported
    obtain ⟨digest, _called, continued⟩ := supported
    obtain ⟨next, resumed, candidateSame, bindingSame, kernelSame, _rest⟩ := server_response_hash_refines pending
      (RegistrationAuthenticationShared.digestArray digest)
    rw [resumed] at continued
    have retained := signing_post ⟨.server, BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request⟩ digest next output continued
    simpa only [candidateSame, bindingSame, kernelSame] using retained

def implementation {m : Type → Type} (signing : QueryImpl RegistrationSigningShared.Spec m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded))) : QueryImpl (Spec Encoded) m
  | .signing request => signing request
  | .encoding view => encode view

theorem interpret {m : Type → Type} [Monad m] [LawfulMonad m]
    (signing : QueryImpl RegistrationSigningShared.Spec m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) :
    simulateQ (implementation signing encode)
      (program (m := OracleComp (Spec Encoded)) (fun request => (Spec Encoded).query (.signing request))
        (fun view => (Spec Encoded).query (.encoding view)) pending) = program signing encode pending := by
  have translated := RegistrationNativePlatformBuildInterpret.Publication.program
    (simulateQ_isMonadHom (implementation signing encode))
    (fun request => ((Spec Encoded).query (.signing request) : OracleComp (Spec Encoded) _))
    (fun view => ((Spec Encoded).query (.encoding view) : OracleComp (Spec Encoded) _)) pending
  simpa only [simulateQ_spec_query, implementation] using translated

theorem stateful {State : Type} (signing : QueryImpl RegistrationSigningShared.Spec (StateT State ProbComp))
    (encode : registration.SignedResponseView → StateT State ProbComp (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (output : RustM (RegistrationWorldServerPublication.Result Encoded))
    (before after : State)
    (supported : (output, after) ∈ support ((program signing encode pending).run before)) :
    Post pending.candidate pending.binding pending.kernel output := by
  rw [← interpret signing encode pending] at supported
  apply program_post pending output
  apply OracleComp.support_simulateQ_run'_subset (implementation signing encode) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported
end BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.ready_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.ready_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.signing_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.signing_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.program_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.program_post

/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.stateful' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerPublicationSnapshot.stateful
