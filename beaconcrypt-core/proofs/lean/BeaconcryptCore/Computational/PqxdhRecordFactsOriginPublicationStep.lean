-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginGlobal

/-! Literal writer outcomes for newly generated hidden source records. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginReceive
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (Handle Entry)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The actual writer either refused this frame or returned these source ciphertext bytes. -/
def WriterOutcome (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (reply : Option RawCtxSourceSend.Encrypted) (frame : PqxdhDeploymentNative.Frame) : Prop :=
  codec.frameWrite frame = none ∨
    ∃ encrypted, reply = some encrypted ∧ codec.frameRead encrypted.ciphertext = some frame

/-- Every post-seal dictionary entry is old or has the exact current writer outcome. -/
theorem sealing_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.sealing pending)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      label = pending.material ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1 frame := by
  obtain ⟨produced, unchanged | ⟨width, record, inserted, logged, reply⟩⟩ :=
    sealing_trace modes ideal replace setup codec pending before result supported
  · exact Or.inl (unchanged.2.2 label ▸ member)
  · by_cases same : label = pending.material
    · subst label
      rw [inserted, List.mem_cons] at member
      rcases member with rfl | prior
      · refine Or.inr ⟨rfl, ⟨pending.sequence, pending.context.senderId, record.encode⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
        cases written : codec.frameWrite ⟨pending.sequence, pending.context.senderId, record.encode⟩ with
        | none => exact Or.inl written
        | some bytes =>
          refine Or.inr ⟨⟨bytes, pending.context.targetId, pending.sequence⟩, ?_, (readback _ _ written).2⟩
          simpa only [written, Option.map_some] using reply
      · exact Or.inl prior
    · exact Or.inl ((congrArg (fun key : KeyEntry => key.1.successfulSeals)
        (PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending before result supported label same)) ▸ member)

/-- A hidden kernel send attributes every new seal to its actual current coordinate and writer reply. -/
theorem kernelSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n)
    (context : RawCtxSourceSend.SealContext) (before : CtxPrivate n)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot kernel) context)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      label = kernel.send_chain ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.2 frame := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked kernel context
  cases admitted : RawCtxChainSend.normalBegin kernel context with
  | exhausted original prior =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  | requested pending =>
    rw [admitted] at tracked
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨looked, lookupSupported, continued⟩ := supported
    rw [mem_support_bind_iff] at continued
    obtain ⟨sealed, sealSupported, finished⟩ := continued
    simp only [support_pure, Set.mem_singleton_iff] at finished
    subst result
    rcases sealing_entry modes ideal replace setup codec readback _ looked.2 sealed sealSupported
      label entry member with prior | current
    · have kept := lookup_preserves modes replace setup codec pending.request before looked lookupSupported
      exact Or.inl ((congrArg (fun keys => (keys label).1.successfulSeals) kept.1) ▸ prior)
    · right
      simpa only [RawCtxChainSend.ready, tracked.2.2.1] using current

/-- Every newly generated owner-send seal retains its actual installed sender and writer outcome. -/
theorem ownerSend_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label handle ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  unfold PqxdhRecordLiftProtocol.ownerSend at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Or.inl member
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases kind : owner.kernel with
    | hidden slot kernel =>
      rw [kind] at stored reached
      rcases kernelSend_entry modes ideal replace setup codec readback slot kernel _ before inner
        reached label entry member with prior | ⟨same, frame, matched, outcome⟩
      · exact Or.inl prior
      · right
        have claimed := PqxdhRecordFactsOriginSend.sending_claim control safe handle slot kernel stored
        obtain ⟨other, tagged, owned⟩ := claimed
        cases Option.some.inj tagged.symm
        exact ⟨same ▸ owned, frame, matched, outcome⟩
    | known kernel =>
      rw [kind] at reached
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, support_map] at reached
      obtain ⟨native, nativeReached, rfl⟩ := reached
      simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
        PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
        support_map] at nativeReached
      obtain ⟨inner, reached, rfl⟩ := nativeReached
      exact Or.inl member

/-- The actual tagged owner-send publication retains the new seal's literal writer outcome. -/
theorem ownerRun_entry (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun (some handle) sender codec.frameRead (.inl plaintext) owner)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    entry ∈ (before.keys label).1.successfulSeals ∨
      OwnsLabel control label handle ∧ ∃ frame, Matches frame entry ∧ WriterOutcome codec result.1.1 frame := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sendSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerSend_entry modes ideal replace setup codec readback control safe handle owner stored sender
    plaintext before sent sendSupported label entry member

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.sealing_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.sealing_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.kernelSend_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.kernelSend_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.ownerSend_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.ownerSend_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.ownerRun_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationStep.ownerRun_entry
