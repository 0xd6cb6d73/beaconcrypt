-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhOpenContextBridge
import BeaconcryptCore.Computational.RecordEffectsReceiveProgram

/-! The extracted record controller refines the existing receive program for every primitive reply. The interpreter below only dispatches primitive requests and erases the borrowed transcript; admission, phase selection, retained state and publication are the extracted operations. Native primitive execution, decoding and interpreter fidelity remain external. -/

open CoreModels Aeneas OracleComp
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhRefinement
open BeaconcryptCore.Refinement.RecordEffectsComposition
open BeaconcryptCore.Computational.RawCtxInterpretedOpening (bindResult)
open BeaconcryptCore.Computational.RecordEffectsReceiveRank (rank resume_decreasing)

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RecordEffectsReceiveBridge

open RecordEffectsReceiveProgram

theorem compare_digest_exact (digest : Option Pqxdh.Bytes)
    (pending : record_effects.RecordReceiveCommitment) :
    compareDigest digest pending = PqxdhOpenBridges.compareDigest digest pending.pending := by
  cases digest <;> rfl


theorem open_execution (erased : Std.Array Std.U8 357#usize)
    (opening : ReceiveOpen record.OpenFrameContext) :
    bindResult (record_effects.normalize_receive (.ReceiveOpenRequested opening)) (execute erased) =
      simulateQ RawCtxSourceOpen.openLift (PqxdhOpenBridges.executeOpen erased opening) := by
  obtain ⟨start, run⟩ := BeaconcryptCore.PanicFreedom.Record.begin_total opening
  simp only [record_effects.normalize_receive, PqxdhOpenBridges.executeOpen, run,
    bind_tc_ok, PqxdhOpenBridges.bindResult_ok]
  cases start with
  | OpenRejected => simp only [PqxdhOpenBridges.bindResult_ok, execute, simulateQ_pure]
  | OpenCommitmentRequested pending =>
      simp only [PqxdhOpenBridges.bindResult_ok, execute]
      apply congrArg (simulateQ RawCtxSourceOpen.openLift)
      simp only [executeCommitment, record_effects.RecordReceiveCommitment.transcript,
        record.OpenCommitment.impl.transcript, commitment.CommitmentTranscript.as_bytes,
        PqxdhOpenBridges.bindResult_ok]
      refine bind_congr fun digest => ?_
      simp only [record_effects.RecordReceiveCommitment.transcript_mut,
        record.OpenCommitment.transcript_mut, commitment.CommitmentTranscript.as_mut_bytes,
        PqxdhOpenBridges.bindResult_ok, compare_digest_exact]
      congr 1
      funext matched
      cases matched <;> rfl

theorem normalize_execution (erased : Std.Array Std.U8 357#usize)
    (effect : ReceiveEffect record.OpenFrameContext) :
    bindResult (record_effects.normalize_receive effect) (execute erased) =
      PqxdhOpenContextBridge.executeReceive erased effect := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveKdfRequested pending =>
          simp only [normalize_kdf_exact, PqxdhOpenBridges.bindResult_ok,
            execute_kdf, PqxdhOpenContextBridge.executeReceive_kdf]
          refine bind_congr fun response => ?_
          simp only [record_effects.RecordReceiveKdf.resume, RawCtxOwnerOracle.resume_exact,
            bind_tc_ok, PqxdhOpenBridges.bindResult_ok]
          exact ih _ (by simpa only [hdepth] using
            RawCtxOwnerOracle.resume_rank pending response) _ rfl
      | ReceiveRejected =>
          simp only [normalize_rejected_exact, PqxdhOpenBridges.bindResult_ok, execute,
            PqxdhOpenContextBridge.executeReceive]
      | ReceiveOpenRequested opening =>
          simpa only [PqxdhOpenContextBridge.executeReceive] using open_execution erased opening

theorem receive_execution (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (sequence : Std.U64) (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (sender : Std.U64) :
    receive erased kernel sequence payload ad sender =
      bindResult (record.OpenFrameContext.from_frame payload ad sender) (fun admitted =>
        match admitted with
        | .None => pure (ok (kernel, .None))
        | .Some context => PqxdhOpenContextBridge.executeReceiveFrom erased kernel sequence context) := by
  obtain ⟨admitted, run⟩ := BeaconcryptCore.PanicFreedom.Record.payload_total payload ad sender
  simp only [receive, record_effects.begin_record_receive, run, bind_tc_ok,
    PqxdhOpenBridges.bindResult_ok]
  cases admitted with
  | none => simp only [PqxdhOpenBridges.bindResult_ok, execute]
  | some context =>
      simp only [RawCtxOwnerOracle.begin_exact, bind_tc_ok,
        PqxdhOpenContextBridge.executeReceiveFrom, PqxdhOpenBridges.bindResult_ok]
      exact normalize_execution erased _

/-- Equality includes sender rejection, malformed record admission and every primitive failure. -/
theorem decoded_execution (erased : Std.Array Std.U8 357#usize)
    (kernel : ConcreteRatchetKernel) (expected : Std.U64) (frame : RawCtxReceive.DecodedFrame)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize) :
    decoded erased kernel expected frame payload ad =
      PqxdhOpenContextBridge.executeDecoded erased kernel expected frame payload ad := by
  simp only [decoded, PqxdhOpenContextBridge.executeDecoded, receive_execution]
  rfl

/-- The actual record controller reaches the existing source receive model under explicit byte representation. -/
theorem decoded_native_model (erased : Std.Array Std.U8 357#usize)
    (kernel : ConcreteRatchetKernel) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (associatedData : Pqxdh.Bytes)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = frame.payload)
    (had : absBytes ad = associatedData) :
    decoded erased kernel expected frame payload ad =
      (fun result => ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
        (if RawCtxReceive.ValidFrame expected associatedData frame then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
              ⟨raw, frame, associatedData⟩)
        else pure (kernel, .None)) := by
  rw [decoded_execution]
  exact PqxdhOpenContextBridge.decoded_receive_native erased kernel expected raw frame
    associatedData payload ad hpayload had

/-- Equality preserves the complete state of arbitrary stateful KDF/hash/AEAD interpreters. -/
theorem stateful_execution {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (expected : Std.U64) (frame : RawCtxReceive.DecodedFrame) (payload : Slice Std.U8)
    (ad : Std.Array Std.U8 281#usize) (state : PrimitiveState) :
    (simulateQ impl (decoded erased kernel expected frame payload ad)).run state =
      (simulateQ impl
        (PqxdhOpenContextBridge.executeDecoded erased kernel expected frame payload ad)).run state :=
  congrArg (fun program => (simulateQ impl program).run state)
    (decoded_execution erased kernel expected frame payload ad)

end BeaconcryptCore.Computational.RecordEffectsReceiveBridge

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.compare_digest_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.compare_digest_exact

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.open_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.open_execution

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.normalize_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.normalize_execution

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.receive_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.receive_execution

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.decoded_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.decoded_execution

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.decoded_native_model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.decoded_native_model

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveBridge.stateful_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveBridge.stateful_execution
