-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentOrder

/-! Actual successful Beacon first-record execution retains its reached pre-commitment KDF callbacks, actual hash/supplied commitment comparison and final AEAD callback. A source ordering theorem excludes bypassing the hash phase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconRecordTrace
open RegistrationRecordPrimitives (Spec)
open RegistrationBeaconRecordExecutor (Result program rank continueWith commitmentMatches)
open RegistrationNativeBeaconCommitmentOrder (BeforeHash)
variable {S : Type}

/-- The actual source KDF prefix before commitment verification, with every reached reply and state. -/
inductive Prefix (implementation : QueryImpl Spec (StateT S ProbComp)) : registration.BeaconInitialOpen → S → registration.BeaconInitialOpen → S → Prop where
  | refl (phase : registration.BeaconInitialOpen) (state : S) : Prefix implementation phase state phase state
  | step (pending : registration.BeaconRecordKdf) (request : ratchet.SymmetricRatchetKdfRequest)
      (reply : Spec.Range (.ratchetKdf request)) (next : registration.BeaconInitialOpen)
      (before middle after : S) (last : registration.BeaconInitialOpen)
      (requested : pending.request = .ok request)
      (called : (reply, middle) ∈ support ((implementation (.ratchetKdf request)).run before))
      (resumed : pending.resume reply = .ok (.Ok next))
      (following : Prefix implementation next middle last after) :
      Prefix implementation (.KdfRequested pending) before last after

/-- Every retained primitive operand belongs to this one actual source execution. -/
structure Trace (implementation : QueryImpl Spec (StateT S ProbComp))
    (phase : registration.BeaconInitialOpen) (completed : registration.CompletedBeacon) (before after : S) where
  commitmentState : registration.BeaconRecordCommitment
  atHash : S
  leading : Prefix implementation phase before (.CommitmentRequested commitmentState) atHash
  transcript : commitment.CommitmentTranscript
  hashReply : Spec.Range (.hash transcript)
  afterHash : S
  supplied : Std.Array U8 64#usize
  aead : registration.BeaconRecordAead
  aeadRequest : record.AeadRequest
  openReply : Spec.Range (.openAead aeadRequest)
  hashRequested : commitmentState.transcript = .ok transcript
  hashCalled : (hashReply, afterHash) ∈ support ((implementation (.hash transcript)).run atHash)
  suppliedRequested : commitmentState.supplied_commitment = .ok supplied
  matched : commitmentMatches hashReply supplied = true
  hashResumed : commitmentState.resume (commitmentMatches hashReply supplied) = .ok (.Ok (.AeadRequested aead))
  aeadRequested : aead.request = .ok (.Some aeadRequest)
  aeadCalled : (openReply, after) ∈ support ((implementation (.openAead aeadRequest)).run afterHash)
  aeadResumed : aead.finish openReply = .ok (.Ok completed)

private theorem with_cut {A : Type} (implementation : QueryImpl Spec (StateT S ProbComp))
    (head : RustM A) (next : A → OracleComp Spec (RustM Result)) (completed : registration.CompletedBeacon)
    (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (continueWith head next)).run before)) :
    ∃ value, head = .ok value ∧ (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (next value)).run before) := by
  cases head with
  | fail error | div => simp [continueWith] at supported
  | ok value => exact ⟨value, rfl, supported⟩

private theorem resume_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (head : RustM (core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted))
    (completed : registration.CompletedBeacon) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (match _actual : head with
      | .ok (.Ok next) => program next
      | .ok (.Err aborted) => pure (.ok (.Err aborted))
      | .fail error => pure (.fail error)
      | .div => pure .div)).run before)) :
    ∃ next, head = .ok (.Ok next) ∧ (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (program next)).run before) := by
  cases head with
  | fail error | div => simp at supported
  | ok result => cases result with
    | Err aborted => simp at supported
    | Ok next => exact ⟨next, rfl, supported⟩

private theorem no_plaintext (pending : registration.BeaconRecordAead) (completed : registration.CompletedBeacon)
    (actual : pending.finish .None = .ok (.Ok completed)) : False := by
  simp [registration.BeaconRecordAead.finish, record_effects.RecordReceiveAead.finish, record.OpenAead.finish,
    ratchet.concrete.ReceiveOpen.finish, pqxdh.BeaconRegistrationCandidate.server_key_id, pqxdh.BeaconAborted.new] at actual

private theorem aead_cut (implementation : QueryImpl Spec (StateT S ProbComp))
    (pending : registration.BeaconRecordAead) (completed : registration.CompletedBeacon) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (program (.AeadRequested pending))).run before)) :
    ∃ request reply, pending.request = .ok (.Some request) ∧
      (reply, after) ∈ support ((implementation (.openAead request)).run before) ∧ pending.finish reply = .ok (.Ok completed) := by
  rw [program.eq_def] at supported
  obtain ⟨requested, requestEq, continued⟩ := with_cut implementation pending.request _ completed before after supported
  cases requested with
  | none =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at continued
    exact False.elim (no_plaintext pending completed continued.1.symm)
  | some request =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨⟨reply, returned⟩, called, finished⟩ := continued
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at finished
    obtain ⟨resumed, stateEq⟩ := finished
    subst returned
    exact ⟨request, reply, requestEq, called, resumed.symm⟩

/-- Successful original execution from a pre-commitment phase exposes its actual checked hash and actual final AEAD source callback. -/
theorem run (implementation : QueryImpl Spec (StateT S ProbComp))
    (phase : registration.BeaconInitialOpen) (completed : registration.CompletedBeacon) (before after : S)
    (beforeHash : BeforeHash phase)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (program phase)).run before)) :
    Nonempty (Trace implementation phase completed before after) := by
  cases phaseShape : phase with
  | KdfRequested pending =>
    rw [program.eq_def, phaseShape] at supported
    obtain ⟨request, requested, continued⟩ := with_cut implementation pending.request _ completed before after supported
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨⟨reply, middle⟩, called, continued⟩ := continued
    obtain ⟨next, resumed, continued⟩ := resume_cut implementation (pending.resume reply) completed middle after continued
    obtain ⟨trace⟩ := run implementation next completed middle after (RegistrationNativeBeaconCommitmentOrder.kdf pending reply next resumed) continued
    exact ⟨{trace with leading := (.step pending request reply next before middle trace.atHash
      (.CommitmentRequested trace.commitmentState) requested called resumed trace.leading)}⟩
  | CommitmentRequested pending =>
    rw [program.eq_def, phaseShape] at supported
    obtain ⟨transcript, requested, continued⟩ := with_cut implementation pending.transcript _ completed before after supported
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨⟨hashReply, middle⟩, hashCalled, continued⟩ := continued
    obtain ⟨supplied, suppliedRequested, continued⟩ := with_cut implementation pending.supplied_commitment _ completed middle after continued
    obtain ⟨next, resumed, continued⟩ := resume_cut implementation (pending.resume (commitmentMatches hashReply supplied)) completed middle after continued
    obtain ⟨matched, aead, nextEq⟩ := RegistrationNativeBeaconCommitmentOrder.commitment pending (commitmentMatches hashReply supplied) next resumed
    subst next
    obtain ⟨aeadRequest, openReply, aeadRequested, aeadCalled, aeadResumed⟩ := aead_cut implementation aead completed middle after continued
    exact ⟨⟨pending, before, .refl _ _, transcript, hashReply, middle, supplied, aead, aeadRequest, openReply,
      requested, hashCalled, suppliedRequested, matched, resumed, aeadRequested, aeadCalled, aeadResumed⟩⟩
  | AeadRequested pending => simp only [phaseShape, BeforeHash] at beforeHash
termination_by rank phase

decreasing_by
  simpa only [phaseShape] using RegistrationBeaconRecordExecutor.kdf_rank pending reply next resumed

end BeaconcryptCore.Computational.RegistrationNativeBeaconRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecordTrace.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecordTrace.run
