-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldRecords
import BeaconcryptCore.Refinement.RegistrationPublication

/-!
The actual Server response hash/sign/publication phase runs after the consumed first record. Encoding is applied to the actual signed response view after the real optional signature reply; it cannot fabricate a signature or publish a peer on failed signing/encoding. Hashing and all signing coins use the existing instrumented World, and the signing-attempt receipt precedes every later source outcome.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationWorldServerPublication
open RegistrationSigningShared (Spec SignReply State Cached)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (replyBytes)
variable {Encoded : Type}

abbrev Result (Encoded : Type) := core.result.Result (registration.PublishedServerResponse Encoded) pqxdh.ServerState

def continueWith {Input : Type} (action : RustM Input) (next : Input → OracleComp Spec (RustM (Result Encoded))) :
    OracleComp Spec (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp Spec (RustM (Result Encoded))) : OracleComp Spec (RustM (Result Encoded)) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The actual encoder sees the native signed view, including its newly returned signature. -/
def ready (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.message fun view => pure (pending.publish (encode view))

def signing (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let signature ← Spec.query (.sign request payload digest)
    continueResult (pending.resume signature) (ready encode)

/-- This phase begins at the actual post-record hash capability; earlier authentication and Beacon fingerprint work are separate executed phases. -/
def program (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let digest ← Spec.query (.hash request)
    continueResult (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))
      (signing encode ⟨.server, hashBytes request⟩ digest)

private theorem signing_request (pending : registration.ServerResponseSigning) :
    pending.request = .ok ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩ := rfl

/-- Pure source publication, including encoder failure, never changes an already reached signing history. -/
theorem ready_pure (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) :
    ready encode pending = pure (do let view ← pending.message; pending.publish (encode view)) := by
  cases message : pending.message <;> simp [ready, continueWith, message]

/-- Actual signing is attempted once, and the exact selected key/payload/reply is recorded before publication. -/
theorem signing_run (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (state : State) :
    (simulateQ (RegistrationSigningShared.implementation sign) (signing encode payload digest pending)).run state =
      (fun signature =>
        ((match pending.resume signature with
          | .ok (.Ok completed) => do let view ← completed.message; completed.publish (encode view)
          | .ok (.Err previous) => .ok (.Err previous)
          | .fail error => .fail error
          | .div => .div),
          (state.1 ++ [⟨⟨pending.binding.server_pin.public_key, payload, replyBytes signature⟩, digest⟩], state.2))) <$>
          sign ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩ := by
  simp only [signing, signing_request, continueWith, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind]
  change (do
    let signed ← (RegistrationSigningShared.implementation sign (.sign
      ⟨pending.binding.server_pin.public_key, .Server, pending.input, authentication.SIGNING_CONTEXT⟩ payload digest)).run state
    (simulateQ (RegistrationSigningShared.implementation sign)
      (continueResult (pending.resume signed.1) (ready encode))).run signed.2) = _
  rw [RegistrationSigningShared.signing_step, bind_map_left, ← bind_pure_comp]
  apply bind_congr
  intro signature
  cases resumed : pending.resume signature with
  | ok result =>
    cases result <;> simp only [continueResult, ready_pure, simulateQ_pure, StateT.run_pure]
  | fail error => simp only [continueResult, simulateQ_pure, StateT.run_pure]
  | div => simp only [continueResult, simulateQ_pure, StateT.run_pure]

/-- Instrumented execution of the complete response publication is exactly its actual shared source interpretation. -/
theorem world_project {n : Nat}
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (state : RegistrationWorldSigning.State n) :
    Prod.map id RegistrationWorldSigning.project <$>
      (simulateQ (RegistrationWorldSigning.outgoing sign) (program encode pending)).run state =
      (simulateQ (RegistrationSigningShared.implementation sign) (program encode pending)).run
        (RegistrationWorldSigning.project state) :=
  RegistrationWorldSigning.outgoing_program_project sign _ state

/-- The recorded signing attempt remains cached after every signature/encoder/publication outcome. -/
theorem signing_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (state : State) (cached : Cached state)
    (hashed : state.2 ((), payload.transcript) = some digest)
    (result : RustM (Result Encoded) × State)
    (supported : result ∈ support
      ((simulateQ (RegistrationSigningShared.implementation sign) (signing encode payload digest pending)).run state)) :
    Cached result.2 := by
  rw [signing_run] at supported
  obtain ⟨signature, _possible, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  exact RegistrationSigningShared.cached_append state
    ⟨⟨pending.binding.server_pin.public_key, payload, replyBytes signature⟩, digest⟩ cached hashed

/-- Hash provenance and every reached signing receipt are derived by the actual response controller, without a successful-publication premise. -/
theorem program_cached (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (state : State) (cached : Cached state)
    (result : RustM (Result Encoded) × State)
    (supported : result ∈ support
      ((simulateQ (RegistrationSigningShared.implementation sign) (program encode pending)).run state)) :
    Cached result.2 := by
  obtain ⟨request, requested, _⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  simp only [program, requested, continueWith, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨hashed, reached, tail⟩ := supported
  have hashFacts := RegistrationSigningShared.hash_cached sign request state hashed reached
  obtain ⟨next, resumed, _⟩ := BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending
    (RegistrationAuthenticationShared.digestArray hashed.1)
  rw [resumed] at tail
  exact signing_cached sign encode ⟨.server, hashBytes request⟩ hashed.1 next hashed.2
    (RegistrationSigningShared.hash_cached_state sign request state cached hashed reached)
    hashFacts.2 result tail

/-- The actual instrumented World retains those same complete signing histories across failed response publication. -/
theorem world_cached {n : Nat} (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (state : RegistrationWorldSigning.State n)
    (cached : Cached (RegistrationWorldSigning.project state))
    (result : RustM (Result Encoded) × RegistrationWorldSigning.State n)
    (supported : result ∈ support
      ((simulateQ (RegistrationWorldSigning.outgoing sign) (program encode pending)).run state)) :
    Cached (RegistrationWorldSigning.project result.2) := by
  apply program_cached sign encode pending (RegistrationWorldSigning.project state) cached
    (result.1, RegistrationWorldSigning.project result.2)
  rw [← world_project, support_map]
  exact Set.mem_image_of_mem (Prod.map id RegistrationWorldSigning.project) supported

/-- Actual publication success returns exactly the consumed kernel and completed authenticated session metadata. -/
theorem ready_published_fields (pending : registration.ServerResponseReady)
    (encoded : core.option.Option Encoded) (published : registration.PublishedServerResponse Encoded)
    (finished : pending.publish encoded = .ok (.Ok published)) :
    published.kernel = pending.kernel ∧
      PqxdhRecordLiftInterface.PeerBinding.ofSession published.binding = RegistrationRecordBinding.ofRegistration pending.binding ∧
      published.control = pending.candidate.next_state := by
  rw [BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines] at finished
  cases encoded with
  | none => cases finished
  | some bytes =>
    cases RustM.ok.inj finished
    exact ⟨rfl, rfl, rfl⟩

/-- The actual wire encoder runs after signing; only its native successful publication can return a kernel. -/
theorem ready_retains (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (ready encode pending)) :
    published.kernel = pending.kernel ∧
      PqxdhRecordLiftInterface.PeerBinding.ofSession published.binding = RegistrationRecordBinding.ofRegistration pending.binding ∧
      published.control = pending.candidate.next_state := by
  cases message : pending.message with
  | fail error => simp [ready, continueWith, message] at supported
  | div => simp [ready, continueWith, message] at supported
  | ok view =>
    simp only [ready, message, continueWith, mem_support_pure_iff] at supported
    exact ready_published_fields pending (encode view) published supported.symm

/-- Optional signature failure, wrong ML-DSA width and failed encoding cannot publish a peer; every actual success keeps its existing kernel and binding. -/
theorem signing_retains (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (signing encode payload digest pending)) :
    published.kernel = pending.kernel ∧
      PqxdhRecordLiftInterface.PeerBinding.ofSession published.binding = RegistrationRecordBinding.ofRegistration pending.binding ∧
      published.control = pending.candidate.next_state := by
  simp only [signing, signing_request, continueWith, mem_support_bind_iff] at supported
  obtain ⟨signature, _possible, tail⟩ := supported
  cases signature with
  | none =>
    simp [registration.ServerResponseSigning.resume, pqxdh.server_abort_candidate, continueResult] at tail
  | some signature =>
    obtain ⟨result, resumed, fields⟩ :=
      BeaconcryptCore.Refinement.RegistrationPublication.server_signature_admission_refines pending signature
    rw [resumed] at tail
    cases result with
    | Err previous => simp [continueResult] at tail
    | Ok completed =>
      obtain ⟨candidateEq, bindingEq, kernelEq, _⟩ := fields
      obtain ⟨kernel, binding, control⟩ := ready_retains encode completed published tail
      exact ⟨kernel.trans kernelEq, binding.trans (congrArg RegistrationRecordBinding.ofRegistration bindingEq),
        control.trans (congrArg pqxdh.ServerRegistrationCandidate.next_state candidateEq)⟩

/-- The complete actual response hash/sign/encode/publication controller retains the already consumed sequence-one kernel and actual populated AD. -/
theorem program_retains (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded)
    (supported : .ok (.Ok published) ∈ support (program encode pending)) :
    published.kernel = pending.kernel ∧
      PqxdhRecordLiftInterface.PeerBinding.ofSession published.binding = RegistrationRecordBinding.ofRegistration pending.binding ∧
      published.control = pending.candidate.next_state := by
  obtain ⟨request, requested, _⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningTrace.command_request_exact (.server pending)
  change pending.request = .ok request at requested
  simp only [program, requested, continueWith, mem_support_bind_iff] at supported
  obtain ⟨digest, _possible, tail⟩ := supported
  obtain ⟨next, resumed, candidateEq, bindingEq, kernelEq, _⟩ :=
    BeaconcryptCore.Refinement.RegistrationPublication.server_response_hash_refines pending
      (RegistrationAuthenticationShared.digestArray digest)
  rw [resumed] at tail
  obtain ⟨kernel, binding, control⟩ := signing_retains encode ⟨.server, hashBytes request⟩ digest next published tail
  exact ⟨kernel.trans kernelEq, binding.trans (congrArg RegistrationRecordBinding.ofRegistration bindingEq),
    control.trans (congrArg pqxdh.ServerRegistrationCandidate.next_state candidateEq)⟩

end BeaconcryptCore.Computational.RegistrationWorldServerPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.ready_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.ready_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.signing_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.signing_run

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.world_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.world_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.signing_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.signing_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.program_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.program_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.world_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.world_cached

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.ready_published_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.ready_published_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.ready_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.ready_retains

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.signing_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.signing_retains

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerPublication.program_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerPublication.program_retains
