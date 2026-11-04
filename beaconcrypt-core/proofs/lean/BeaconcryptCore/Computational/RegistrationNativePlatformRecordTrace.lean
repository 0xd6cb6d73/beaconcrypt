-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord

/-! Successful source first-record execution retains its actual five callback cuts and complete intermediate shared states. Enclosing allocator/seal/hash/writer failure and divergence cannot supply an optional reply. Mutable transcript replacement is retained at the hash cut and only its proven irrelevant source lens is normalized. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace
open RegistrationRecordPrimitives (Spec)
open RegistrationServerRecordExecutor (Result)
open RegistrationNativePlatformServerRecord (continueWith continueResult)
variable {S : Type}
abbrev Seal (S : Type) := record_effects.AeadSealRequest → StateT S ProbComp
  (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize)))
abbrev Hash (S : Type) := commitment.CommitmentTranscript → StateT S ProbComp RegistrationNativePlatformCommitment.HashReply
abbrev Write (S : Type) := record_effects.RecordWriteRequest → StateT S ProbComp
  (RustM (core.option.Option (Slice U8)))

/-- All source operands, replies and states of one actual successful first-record execution, before response signing. -/
structure Trace (implementation : QueryImpl Spec (StateT S ProbComp))
    (sealing : Seal S) (hash : Hash S) (write : Write S)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S) where
  initialRequest : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest
  initialReply : Spec.Range (.initialKdf initialRequest)
  first : S
  ratchet : registration.ServerInitialSeal
  ratchetRequest : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest
  ratchetReply : Spec.Range (.ratchetKdf ratchetRequest)
  second : S
  aead : registration.ServerRecordAead
  aeadRequest : record_effects.AeadSealRequest
  aeadReply : Spec.Range (.seal aeadRequest)
  third : S
  commitmentState : registration.ServerRecordCommitment
  transcript : commitment.CommitmentTranscript
  digestReply : Spec.Range (.hash transcript)
  erased : commitment.CommitmentTranscript
  fourth : S
  writer : registration.ServerRecordWrite
  writeRequest : record_effects.RecordWriteRequest
  writeReply : Spec.Range (.write writeRequest)
  initialRequested : initial.request = .ok initialRequest
  initialCalled : (initialReply, first) ∈ support ((implementation (.initialKdf initialRequest)).run before)
  initialResumed : initial.resume initialReply = .ok (.Ok ratchet)
  ratchetRequested : ratchet.request = .ok ratchetRequest
  ratchetCalled : (ratchetReply, second) ∈ support ((implementation (.ratchetKdf ratchetRequest)).run first)
  ratchetResumed : ratchet.resume ratchetReply = .ok (.Ok aead)
  aeadRequested : aead.request = .ok aeadRequest
  aeadCalled : (.ok aeadReply, third) ∈ support ((sealing aeadRequest).run second)
  aeadResumed : aead.resume aeadReply = .ok (.Ok commitmentState)
  hashRequested : commitmentState.transcript = .ok transcript
  hashCalled : (.ok (digestReply, erased), fourth) ∈ support ((hash transcript).run third)
  hashResumed : commitmentState.resume digestReply = .ok (.Ok writer)
  writeRequested : writer.request = .ok writeRequest
  writeCalled : (.ok writeReply, after) ∈ support ((write writeRequest).run fourth)
  writeResumed : writer.resume writeReply = .ok (.Ok completed)

private theorem with_cut {A : Type} (head : RustM A) (next : A → StateT S ProbComp (RustM Result)) (completed : registration.ServerResponseHash)
    (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((continueWith head next).run before)) :
    ∃ value, head = .ok value ∧ (.ok (.Ok completed), after) ∈ support ((next value).run before) := by
  cases head with
  | fail error | div => simp [continueWith] at supported
  | ok value => exact ⟨value, rfl, supported⟩

private theorem result_cut {A : Type} (head : RustM (core.result.Result A pqxdh.ServerState)) (next : A → StateT S ProbComp (RustM Result))
    (completed : registration.ServerResponseHash) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((continueResult head next).run before)) :
    ∃ value, head = .ok (.Ok value) ∧ (.ok (.Ok completed), after) ∈ support ((next value).run before) := by
  cases head with
  | fail error | div => simp [continueResult] at supported
  | ok result => cases result with
    | Err state => simp [continueResult] at supported
    | Ok value => exact ⟨value, rfl, supported⟩

private theorem enclosing_cut {A B : Type} (result : RustM A) (next : A → RustM (core.result.Result B pqxdh.ServerState))
    (continuation : B → StateT S ProbComp (RustM Result)) (completed : registration.ServerResponseHash)
    (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((continueResult (do let reply ← result; next reply) continuation).run before)) :
    ∃ reply, result = .ok reply ∧ (.ok (.Ok completed), after) ∈ support
      ((continueResult (next reply) continuation).run before) := by
  cases result with
  | fail error | div => simp [continueResult] at supported
  | ok reply => exact ⟨reply, rfl, supported⟩

private theorem returned_ok (result : RustM (core.option.Option (Slice U8)))
    (writer : registration.ServerRecordWrite) (completed : registration.ServerResponseHash)
    (returned : (do let reply ← result; writer.resume reply) = .ok (.Ok completed)) :
    ∃ reply, result = .ok reply ∧ writer.resume reply = .ok (.Ok completed) := by
  cases result with
  | fail error | div => cases returned
  | ok reply => exact ⟨reply, rfl, returned⟩

/-- Actual supported success supplies all five same-run primitive cuts and their exact source continuation equations. -/
theorem run (implementation : QueryImpl Spec (StateT S ProbComp))
    (sealing : Seal S) (hash : Hash S) (write : Write S)
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((RegistrationNativePlatformSourceRecord.fromInitialWithHash implementation sealing hash write initial).run before)) :
    Nonempty (Trace implementation sealing hash write initial completed before after) := by
  rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash] at supported
  obtain ⟨initialRequest, initialRequested, continued⟩ := with_cut initial.request _ completed before after supported
  simp only [StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨initialReply, first⟩, initialCalled, continued⟩ := continued
  obtain ⟨ratchet, initialResumed, continued⟩ := result_cut (initial.resume initialReply) _ completed first after continued
  rw [RegistrationNativePlatformSourceRecord.fromRatchetWithHash] at continued
  obtain ⟨ratchetRequest, ratchetRequested, continued⟩ := with_cut ratchet.request _ completed first after continued
  simp only [StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨ratchetReply, second⟩, ratchetCalled, continued⟩ := continued
  obtain ⟨aead, ratchetResumed, continued⟩ := result_cut (ratchet.resume ratchetReply) _ completed second after continued
  rw [RegistrationNativePlatformSourceRecord.fromAeadWithHash] at continued
  obtain ⟨aeadRequest, aeadRequested, continued⟩ := with_cut aead.request _ completed second after continued
  simp only [StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨aeadReply, third⟩, aeadCalled, continued⟩ := continued
  obtain ⟨aeadReply, aeadReplyOk, continued⟩ := enclosing_cut aeadReply (fun reply => aead.resume reply) _ completed third after continued
  rw [aeadReplyOk] at aeadCalled
  obtain ⟨commitmentState, aeadResumed, continued⟩ := result_cut (aead.resume aeadReply) _ completed third after continued
  rw [RegistrationNativePlatformCommitment.normalize] at continued
  let transcript := commitmentState.pending.transcript
  have hashRequested : commitmentState.transcript = .ok transcript := rfl
  simp only [StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨digestReply, fourth⟩, hashCalled, continued⟩ := continued
  obtain ⟨digestPair, digestOk, continued⟩ := enclosing_cut digestReply (fun reply => commitmentState.resume reply.1) _ completed fourth after continued
  rw [digestOk] at hashCalled
  obtain ⟨writer, hashResumed, continued⟩ := result_cut (commitmentState.resume digestPair.1) _ completed fourth after continued
  rw [RegistrationNativePlatformServerRecord.fromWrite] at continued
  obtain ⟨writeRequest, writeRequested, continued⟩ := with_cut writer.request _ completed fourth after continued
  simp only [StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨writeReply, written⟩, writeCalled, returned⟩ := continued
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  obtain ⟨writeResumed, stateEq⟩ := returned
  obtain ⟨writeReply, writeOk, writeResumed⟩ := returned_ok writeReply writer completed writeResumed.symm
  rw [writeOk] at writeCalled
  subst written
  exact ⟨⟨initialRequest, initialReply, first, ratchet, ratchetRequest, ratchetReply, second,
    aead, aeadRequest, aeadReply, third, commitmentState, transcript, digestPair.1, digestPair.2, fourth, writer, writeRequest, writeReply,
    initialRequested, initialCalled, initialResumed, ratchetRequested, ratchetCalled, ratchetResumed,
    aeadRequested, aeadCalled, aeadResumed, hashRequested, hashCalled, hashResumed, writeRequested, writeCalled, writeResumed⟩⟩

/-- The source result has the original extracted capability path, independently of the optional outer platform effects. -/
theorem Trace.path {implementation : QueryImpl Spec (StateT S ProbComp)}
    {sealing : Seal S} {hash : Hash S} {write : Write S}
    {initial : registration.ServerInitialKdf} {completed : registration.ServerResponseHash} {before after : S}
    (trace : Trace implementation sealing hash write initial completed before after) :
    RegistrationServerRecordExecutor.Path initial completed :=
  .mk trace.initialReply trace.ratchet trace.initialResumed trace.ratchetReply trace.aead trace.ratchetResumed
    trace.aeadReply trace.commitmentState trace.aeadResumed trace.digestReply trace.writer trace.hashResumed
    trace.writeReply trace.writeResumed

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace.Trace.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordTrace.Trace.path
