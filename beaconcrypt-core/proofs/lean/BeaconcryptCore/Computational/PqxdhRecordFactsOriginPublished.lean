-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant

/-! Successful source writers retain an exact ideal dictionary witness on their own handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginReplay PqxdhRecordFactsOriginServices
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginSend
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (FrameTag Handle)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A successful actual hidden writer decodes to the same frame as an entry in its selected post-seal dictionary. -/
theorem sealing_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (before after : CtxPrivate n)
    (encrypted : RawCtxSourceSend.Encrypted)
    (supported : (some encrypted, after) ∈ support
      ((ctxInterpreter modes replace setup codec (.sealing pending)).run before)) :
    ∃ frame, codec.frameRead encrypted.ciphertext = some frame ∧
      ∃ entry ∈ (after.keys pending.material).1.successfulSeals, Matches frame entry := by
  have traced := (sealing_trace modes ideal replace setup codec pending before (some encrypted, after) supported).2
  obtain ⟨width, record, dictionary, pendingEq, reply⟩ := traced.resolve_left (by simp)
  obtain ⟨ciphertext, written, equal⟩ := Option.map_eq_some_iff.mp reply.symm
  subst encrypted
  refine ⟨_, (readback _ _ written).2, ⟨RawCtxSelectedMessageSealing.selectedInput (materialAt before.base.chain pending.material).2 pending.sequence (replaceContext replace pending.context) width, record⟩, ?_, rfl, rfl, rfl⟩
  rw [dictionary]; exact List.mem_cons_self

/-- Every successful opaque hidden send leaves the returned frame in its actual source sending-coordinate dictionary. -/
theorem kernelSend_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (context : RawCtxSourceSend.SealContext) (before : CtxPrivate n)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.2 = some encrypted) :
    ∃ frame, codec.frameRead encrypted.ciphertext = some frame ∧
      ∃ sealedEntry ∈ (result.2.keys entry.send_chain).1.successfulSeals, Matches frame sealedEntry := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  cases admitted : RawCtxChainSend.normalBegin entry context with
  | exhausted original prior =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    simp only [supported, reduceCtorEq] at returned
  | requested pending =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind, mem_support_bind_iff] at supported
    obtain ⟨looked, lookupSupported, sealed, sealSupported, finished⟩ := supported
    obtain rfl := (mem_support_pure_iff _ _).mp finished
    rw [admitted] at tracked
    simpa only [RawCtxChainSend.ready, tracked.2.2.1] using
      sealing_published modes ideal replace setup codec readback
        (RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))
        looked.2 sealed.2 encrypted (by simpa only [← returned, Prod.eta] using sealSupported)

/-- An actual selected caller-known kernel supplies the existing native known-handle classification. -/
theorem known_of_handleKernel (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (kernel : ConcreteRatchetKernel) (stored : handleKernel control handle = some (.known kernel)) :
    PqxdhRecordLiftFlat.KnownAt control handle := by
  cases handle with
  | peer keyId =>
    simp only [handleKernel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at stored
    obtain ⟨server, existing, peer, found, kernelEq⟩ := stored
    exact ⟨server, peer, kernel, existing, found, kernelEq⟩
  | owner index =>
    simp only [handleKernel, Option.bind_eq_some_iff] at stored
    obtain ⟨phase, found, selected⟩ := stored
    cases phase <;> simp_all [PqxdhRecordLiftFlat.KnownAt]

/-- A returned record is caller-known or has a matching dictionary entry owned by its actual sending handle. -/
def Published (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n)
    (handle : Handle) (encrypted : RawCtxSourceSend.Encrypted) : Prop :=
  PqxdhRecordLiftFlat.KnownAt control handle ∨
    ∃ label, OwnsLabel control label handle ∧ ∃ frame, codec.frameRead encrypted.ciphertext = some frame ∧
      ∃ entry ∈ (secret.keys label).1.successfulSeals, Matches frame entry

/-- The actual complete owner send classifies each successful writer by its own stored kernel and sending handle. -/
theorem ownerSend_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
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
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    Published codec control result.2 handle encrypted := by
  cases storedKind : owner.kernel with
  | known kernel =>
    exact Or.inl (known_of_handleKernel control handle kernel (by simpa only [storedKind] using stored))
  | hidden slot entry =>
    simp only [PqxdhRecordLiftProtocol.ownerSend] at supported
    split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      simp only [supported, reduceCtorEq] at returned
    · simp only [storedKind, bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      refine Or.inr ⟨entry.send_chain, ?_, kernelSend_published modes ideal replace setup codec readback
        slot entry _ before inner reached encrypted returned⟩
      simpa [Claims] using sending_claim control safe handle slot entry (by simpa only [storedKind] using stored)

/-- The actual owner command retains the successful send witness through its literal tagged publication callback. -/
theorem ownerRun_published (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
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
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1.1 = some encrypted) :
    Published codec control result.2 handle encrypted := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sendSupported, published, publishSupported, finished⟩ := supported
  rw [PqxdhRecordFactsOriginBuffers.publish_callback, support_pure, Set.mem_singleton_iff] at publishSupported
  subst published
  obtain rfl := (mem_support_pure_iff _ _).mp finished
  exact ownerSend_published modes ideal replace setup codec readback control safe handle owner stored
    sender plaintext before sent sendSupported encrypted returned

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.sealing_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.sealing_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.kernelSend_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.kernelSend_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.known_of_handleKernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.known_of_handleKernel

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.ownerSend_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.ownerSend_published

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.ownerRun_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublished.ownerRun_published
