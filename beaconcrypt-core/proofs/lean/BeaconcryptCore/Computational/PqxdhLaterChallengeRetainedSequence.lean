import BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedHead
import BeaconcryptCore.Computational.RawCtxNativeSendSequence
import BeaconcryptCore.Computational.PqxdhRecordConfidentialityChallenge

/-! Actual retained native sends preserve the production sequence increment through the full original record frontend and interpreter state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence
open PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhInitialNativeRetained
variable {ι M P I D K X Response Shared A N C Result Origin : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The complete real retained record schedule preserves all additional ambient fields exactly. -/
theorem live_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result) (state : RetainedState A N C) :
    (simulateQ (retained source writer prior external)
      (simulateQ PqxdhInitialPendingPost.liveForward client)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        ((simulateQ (RawCtxPendingRetainedExecution.retained source writer prior) client).run state.1) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhInitialPendingPost.liveForward,
        StateT.run_bind, retained, map_bind]
      simp only [StateT.run, bind_map_left]
      exact bind_congr fun reply => ih reply.1 (reply.2, state.2)

noncomputable def records (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B) :=
  simulateQ (retained source writer prior external)
    (simulateQ PqxdhInitialPendingPost.liveForward
      ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run entry))

/-- The literal original record request runs the actual native calls in the same retained shared state; all additional ambient state is retained in the result. -/
theorem records_run (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B)
    (state : RetainedState A N C) :
    (records source writer prior external sender route decode query entry).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (((RawCtxGenericFamilyLive.impl
          (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native source writer prior))
          (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk)
          sender route decode query).run entry).run state.1) := by
  rw [records, live_run]
  simpa only [RawCtxPendingFamilyLiveTails.program, simulateQ_spec_query,
    RawCtxPendingRetainedExecution.retained, RawCtxFunctionalFamily.native, RawCtxFunctionalFamily.backend] using
    congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work.run state.1)
      (RawCtxPendingFamilyNative.program_interpretation (RawCtxFunctionalFamily.backend source writer prior)
        sender route decode (((RawCtxProtocolReveals.SourceSpec S B).query query) :
          OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) entry)

/-- Every successful actual retained record publication identifies the pre-send kernel and its exact production counter increment. -/
theorem record_kernel (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (entry : RawCtxSourceFamilyPath.LiveState M P I D K S B)
    (state : RetainedState A N C)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × RawCtxSourceFamilyPath.LiveState M P I D K S B) × RetainedState A N C)
    (supported : result ∈ support ((records source writer prior external sender route decode query entry).run state))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (recorded : (owner, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner entry.1 = some kernel ∧
      number.val = kernel.control.send_sequence.val + 1 := by
  rw [records_run, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  exact RawCtxNativeSendSequence.live _ (fun kernel => kernel.control.send_sequence.val)
    (fun entry context state result supported sent published =>
      (RawCtxNativeSendSequence.native _ entry context state result supported sent published).1)
    _ _ sender route decode query entry state.1 actual reached owner number recorded

/-- Successful origin-aware source publication reads the same pre-send kernel; the compiler's full frontend and origin state are retained in the experiment. -/
theorem origin_kernel (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (front : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state : RetainedState A N C)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query ×
      (PqxdhInitialPostContext.NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × RetainedState A N C)
    (supported : result ∈ support ((simulateQ (retained source writer prior external)
      ((PqxdhInitialOriginPost.compiler mark sender route decode (.inl (.inl query))).run (front, trace))).run state))
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (recorded : (owner, number) ∈ RawCtxPublishedRecords.record query result.1.1) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel ∧
      number.val = kernel.control.send_sequence.val + 1 := by
  simp only [PqxdhInitialOriginPost.compiler, StateT.run, bind_pure_comp, simulateQ_map] at supported
  change result ∈ support (StateT.run _ state) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  exact record_kernel source writer prior external sender route decode query front.roles state actual reached owner number recorded

/-- The literal challenge send returns the next sequence of the same pre-send installed kernel in either role. -/
theorem send_kernel (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (plaintext : Pqxdh.Bytes)
    (front : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state : RetainedState A N C)
    (after : (PqxdhInitialPostContext.NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B) × RetainedState A N C)
    (record : RawCtxSourceSend.Encrypted)
    (supported : ((some record, after.1), after.2) ∈ support ((simulateQ (retained source writer prior external)
      ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode)
        (PqxdhRecordConfidentialityChallenge.send owner plaintext)).run (front, trace))).run state)) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel ∧
      record.sequence.val = kernel.control.send_sequence.val + 1 := by
  cases owner with
  | server index peer =>
      exact origin_kernel source writer prior external mark sender route decode
        (.inl (.inl ⟨index, .inl (plaintext, peer)⟩)) front trace state ((some record, after.1), after.2)
        (by simpa only [PqxdhRecordConfidentialityChallenge.send,
          PqxdhRecordConfidentialityChallenge.sendRequest, simulateQ_spec_query] using supported)
        (.server index peer) record.sequence (by simp [RawCtxPublishedRecords.record])
  | beacon index =>
      exact origin_kernel source writer prior external mark sender route decode
        (.inl (.inr (.inl ⟨index, .inl plaintext⟩))) front trace state ((some record, after.1), after.2)
        (by simpa only [PqxdhRecordConfidentialityChallenge.send,
          PqxdhRecordConfidentialityChallenge.sendRequest, simulateQ_spec_query] using supported)
        (.beacon index) record.sequence (by simp [RawCtxPublishedRecords.record])

/-- The admitted equal-length wrapper preserves the actual source reply counter, including the complete resulting wrapper/frontend/native state. -/
theorem challenge_kernel (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (left right : Pqxdh.Bytes) (equal : left.length = right.length)
    (current : PqxdhRecordConfidentialityChallenge.State) (unused : current.pair = none)
    (front : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (state : RetainedState A N C)
    (after : (PqxdhRecordConfidentialityChallenge.State ×
      (PqxdhInitialPostContext.NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) × RetainedState A N C)
    (reply : Option RawCtxSourceSend.Encrypted) (record : RawCtxSourceSend.Encrypted)
    (returned : after.1.1.reply = some (some record))
    (supported : (((reply, after.1.1), after.1.2), after.2) ∈ support
      ((simulateQ (retained source writer prior external)
        ((simulateQ (PqxdhInitialOriginPost.compiler mark sender route decode)
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit (.inr (left, right))).run current)).run
            (front, trace))).run state)) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel ∧
      record.sequence.val = kernel.control.send_sequence.val + 1 := by
  rw [PqxdhRecordConfidentialityChallenge.challenge_step owner number bit left right equal current unused,
    simulateQ_map, StateT.run_map, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨actual, reached, same⟩ := supported
  have value : actual.1.1 = some record := Option.some.inj
    ((congrArg (fun value => value.1.1.2.reply) same).trans returned)
  exact send_kernel source writer prior external mark sender route decode owner (if bit then right else left)
    front trace state (actual.1.2, actual.2) record (by simpa only [← value, Prod.eta] using reached)

end BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.live_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.live_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.records_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.records_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.record_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.record_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.origin_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.origin_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.send_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.send_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.challenge_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence.challenge_kernel
