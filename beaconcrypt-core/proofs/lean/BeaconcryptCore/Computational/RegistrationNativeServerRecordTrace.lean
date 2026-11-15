-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRecordExecutor

/-! Supported actual Server first-record execution retains each of its five reached callbacks and exact source resumes, including the concrete commitment and raw-writer cuts. No abstract-path reply is substituted for a reached primitive result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerRecordTrace
open RegistrationRecordPrimitives (Spec)
open RegistrationServerRecordExecutor (Result continueWith continueResult)
variable {S : Type}

/-- All source operands, replies and states of one actual successful first-record execution, before response signing. -/
structure Trace (implementation : QueryImpl Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S) where
  initialRequest : beaconcrypt_core.ratchet.InitialRatchetKdfRequest
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
  aeadCalled : (aeadReply, third) ∈ support ((implementation (.seal aeadRequest)).run second)
  aeadResumed : aead.resume aeadReply = .ok (.Ok commitmentState)
  hashRequested : commitmentState.transcript = .ok transcript
  hashCalled : (digestReply, fourth) ∈ support ((implementation (.hash transcript)).run third)
  hashResumed : commitmentState.resume digestReply = .ok (.Ok writer)
  writeRequested : writer.request = .ok writeRequest
  writeCalled : (writeReply, after) ∈ support ((implementation (.write writeRequest)).run fourth)
  writeResumed : writer.resume writeReply = .ok (.Ok completed)

private theorem with_cut {A : Type} (implementation : QueryImpl Spec (StateT S ProbComp))
    (head : RustM A) (next : A → OracleComp Spec (RustM Result)) (completed : registration.ServerResponseHash)
    (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (continueWith head next)).run before)) :
    ∃ value, head = .ok value ∧ (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (next value)).run before) := by
  cases head with
  | fail error | div => simp [continueWith] at supported
  | ok value => exact ⟨value, rfl, supported⟩

private theorem result_cut {A : Type} (implementation : QueryImpl Spec (StateT S ProbComp))
    (head : RustM (core.result.Result A pqxdh.ServerState)) (next : A → OracleComp Spec (RustM Result))
    (completed : registration.ServerResponseHash) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (continueResult head next)).run before)) :
    ∃ value, head = .ok (.Ok value) ∧ (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (next value)).run before) := by
  cases head with
  | fail error | div => simp [continueResult] at supported
  | ok result => cases result with
    | Err state => simp [continueResult] at supported
    | Ok value => exact ⟨value, rfl, supported⟩

/-- Actual supported success supplies all five same-run primitive cuts and their exact source continuation equations. -/
theorem run (implementation : QueryImpl Spec (StateT S ProbComp))
    (initial : registration.ServerInitialKdf) (completed : registration.ServerResponseHash) (before after : S)
    (supported : (.ok (.Ok completed), after) ∈ support ((simulateQ implementation (RegistrationServerRecordExecutor.fromInitial initial)).run before)) :
    Nonempty (Trace implementation initial completed before after) := by
  rw [RegistrationServerRecordExecutor.fromInitial] at supported
  obtain ⟨initialRequest, initialRequested, continued⟩ := with_cut implementation initial.request _ completed before after supported
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨initialReply, first⟩, initialCalled, continued⟩ := continued
  obtain ⟨ratchet, initialResumed, continued⟩ := result_cut implementation (initial.resume initialReply) _ completed first after continued
  rw [RegistrationServerRecordExecutor.fromRatchet] at continued
  obtain ⟨ratchetRequest, ratchetRequested, continued⟩ := with_cut implementation ratchet.request _ completed first after continued
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨ratchetReply, second⟩, ratchetCalled, continued⟩ := continued
  obtain ⟨aead, ratchetResumed, continued⟩ := result_cut implementation (ratchet.resume ratchetReply) _ completed second after continued
  rw [RegistrationServerRecordExecutor.fromAead] at continued
  obtain ⟨aeadRequest, aeadRequested, continued⟩ := with_cut implementation aead.request _ completed second after continued
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨aeadReply, third⟩, aeadCalled, continued⟩ := continued
  obtain ⟨commitmentState, aeadResumed, continued⟩ := result_cut implementation (aead.resume aeadReply) _ completed third after continued
  rw [RegistrationServerRecordExecutor.fromCommitment] at continued
  obtain ⟨transcript, hashRequested, continued⟩ := with_cut implementation commitmentState.transcript _ completed third after continued
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨digestReply, fourth⟩, hashCalled, continued⟩ := continued
  obtain ⟨writer, hashResumed, continued⟩ := result_cut implementation (commitmentState.resume digestReply) _ completed fourth after continued
  rw [RegistrationServerRecordExecutor.fromWrite] at continued
  obtain ⟨writeRequest, writeRequested, continued⟩ := with_cut implementation writer.request _ completed fourth after continued
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at continued
  obtain ⟨⟨writeReply, written⟩, writeCalled, returned⟩ := continued
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  obtain ⟨writeResumed, stateEq⟩ := returned
  subst written
  exact ⟨⟨initialRequest, initialReply, first, ratchet, ratchetRequest, ratchetReply, second,
    aead, aeadRequest, aeadReply, third, commitmentState, transcript, digestReply, fourth, writer, writeRequest, writeReply,
    initialRequested, initialCalled, initialResumed, ratchetRequested, ratchetCalled, ratchetResumed,
    aeadRequested, aeadCalled, aeadResumed, hashRequested, hashCalled, hashResumed, writeRequested, writeCalled, writeResumed.symm⟩⟩

end BeaconcryptCore.Computational.RegistrationNativeServerRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordTrace.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordTrace.run
