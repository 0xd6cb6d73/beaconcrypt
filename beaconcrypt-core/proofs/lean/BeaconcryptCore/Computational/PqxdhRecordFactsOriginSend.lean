-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginBuffers
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive

/-! Actual hidden source send attribution through lookup, sealing and owner publication. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginBuffers PqxdhRecordFactsOriginReceive
open PqxdhRecordLiftWorldCompiler (Label StoredKernel LabeledKernel)
open PqxdhDeploymentInterface (FrameTag Handle)
open PqxdhRecordFactsOriginHandles
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- A produced frame tag names an actual installed hidden handle with the coordinate's physical sending direction. -/
def Claims (control : PqxdhRecordLiftProtocol.Control n) (label : Label n) (tag : FrameTag) : Prop :=
  ∃ handle, tag = some handle ∧ OwnsLabel control label handle

/-- The source control and actual handle lookup supply the current hidden sender's label claim. -/
theorem sending_claim (control : PqxdhRecordLiftProtocol.Control n)
    (safe : PqxdhRecordLiftProtocolHistory.Safe control) (handle : Handle)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (stored : handleKernel control handle = some (.hidden slot entry)) :
    Claims control entry.send_chain (some handle) := by
  have oriented := handleKernel_oriented control safe handle (.hidden slot entry) stored
  refine ⟨handle, rfl, ?_, ?_⟩
  · simpa only [oriented.2.1.1] using handleKernel_slot control handle slot entry stored
  · exact oriented.2.2.1.trans (handleRole_direction handle)

/-- Source control evolution retains all established produced-frame claims. -/
theorem claims_step (before after : PqxdhRecordLiftProtocol.Control n)
    (progress : PqxdhRecordLiftProtocolHistory.Step before after)
    (label : Label n) (tag : FrameTag) (claimed : Claims before label tag) : Claims after label tag := by
  obtain ⟨handle, tagged, owned⟩ := claimed
  exact ⟨handle, tagged, ownsLabel_step before after progress label handle owned⟩

/-- The actual hidden source send uses its current sending coordinate, preserving buffered provenance through exhaustion, lookup and every writer result. -/
theorem kernelSend_buffered (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (tag : FrameTag)
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (claimed : claims entry.send_chain tag) (context : RawCtxSourceSend.SealContext)
    (before : CtxPrivate n) (buffered : Buffered claims tag before)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run before)) :
    Buffered claims tag result.2 := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  cases admitted : RawCtxChainSend.normalBegin entry context with
  | exhausted original prior =>
    simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
      admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
      StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact buffered
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
    have lookup := lookup_preserves modes replace setup codec pending.request before looked lookupSupported
    have invariant : Buffered claims tag looked.2 := buffered_preserved claims tag before looked.2 buffered
      (fun label => congrArg (fun keys => (keys label).1.successfulSeals) lookup.1) lookup.2.1 lookup.2.2.1
    apply sealing_buffered modes ideal replace setup codec claims tag _ _ looked.2 invariant sealed sealSupported
    simpa only [RawCtxChainSend.ready, tracked.2.2.1] using claimed

/-- The label premise of the hidden send induction is supplied by actual source handle storage and role orientation. -/
theorem kernelSend_source_buffered (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (slot : PqxdhRecordLiftInterface.Slot n) (entry : LabeledKernel n)
    (stored : handleKernel control handle = some (.hidden slot entry)) (context : RawCtxSourceSend.SealContext)
    (before : CtxPrivate n) (closed : Closed (Claims control) before)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run before)) :
    Buffered (Claims control) (some handle) result.2 :=
  kernelSend_buffered modes ideal replace setup codec (Claims control) (some handle) slot entry
    (sending_claim control safe handle slot entry stored) context before
    (closed_buffered (Claims control) (some handle) before closed) result supported

/-- Caller-known sends preserve every hidden coordinate's already attributed dictionary entry. -/
theorem knownSend_closed (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (claims : Label n → FrameTag → Prop) (before : CtxPrivate n) (closed : Closed claims before)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
    (result : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.knownSend kernel context)).run before)) :
    Closed claims result.2 := by
  simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact closed

/-- The actual owner send obtains its current-coordinate attribution from handle storage, including empty and caller-known sends. -/
theorem ownerSend_buffered (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n) (closed : Closed (Claims control) before)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)).run before)) :
    Buffered (Claims control) (some handle) result.2 := by
  unfold PqxdhRecordLiftProtocol.ownerSend at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact closed_buffered (Claims control) (some handle) before closed
  · simp only [bind_pure_comp, simulateQ_map, StateT.run_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases kind : owner.kernel with
    | hidden slot kernel =>
      rw [kind] at stored reached
      exact kernelSend_source_buffered modes ideal replace setup codec control safe handle slot kernel stored
        _ before closed inner reached
    | known kernel =>
      rw [kind] at reached
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, support_map] at reached
      obtain ⟨native, nativeReached, rfl⟩ := reached
      exact closed_buffered (Claims control) (some handle) _
        (knownSend_closed modes replace setup codec (Claims control) before closed kernel _ native nativeReached)

/-- A complete source owner-send command attributes every newly generated dictionary entry to its actual caller handle and closes the pending writer log. -/
theorem ownerRun_send_closed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (handle : Handle) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (stored : handleKernel control handle = some owner.kernel) (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : CtxPrivate n) (closed : Closed (Claims control) before)
    (result : (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftWorldCompiler.Owner n) × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec)
      (PqxdhRecordLiftProtocol.ownerRun (some handle) sender codec.frameRead (.inl plaintext) owner)).run before)) :
    Closed (Claims control) result.2 ∧ result.2.base.pending = [] := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, PqxdhRecordLiftProtocol.ownerStep,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff] at supported
  obtain ⟨sent, sendSupported, published, publishSupported, finished⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  exact publish_buffered_closed modes replace setup codec (Claims control) (some handle) sent.2
    (ownerSend_buffered modes ideal replace setup codec control safe handle owner stored sender plaintext
      before closed sent sendSupported) published publishSupported

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend


/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.sending_claim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.sending_claim

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.claims_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.claims_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.kernelSend_buffered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.kernelSend_buffered

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.kernelSend_source_buffered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.kernelSend_source_buffered

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.knownSend_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.knownSend_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.ownerSend_buffered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.ownerSend_buffered

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.ownerRun_send_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginSend.ownerRun_send_closed
