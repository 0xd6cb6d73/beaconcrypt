-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealAlignment
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalFinalPrefix
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginErasedPublication
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMetadataGlobal

/-! Concrete failed-cut events on the same complete actual erased source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Private)
open PqxdhRecordFactsOriginReplay (Matches)
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Prefix prefix_reach)
open PqxdhRecordFactsOriginResumeConsumer (AcceptedTarget)
open PqxdhRecordFactsOriginMarkerNative (service)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Final source fields selecting an actual accepted coordinate and a retained matching seal whose exact writer rejected its frame. -/
def FailedCutEvent (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (cut : Cut n (Client n E X)) (result : Client n E X × CtxPrivate n) : Prop :=
  AcceptedTarget cut.pending.material route result ∧
    ∃ frame entry, entry ∈ (result.2.keys cut.pending.material).1.successfulSeals ∧
      Matches frame entry ∧ codec.frameWrite frame = none

/-- Removing only the sticky analysis flag preserves support of the same complete source suffix reply and state. -/
theorem suffix_support (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (result : X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec) work).run (state, false))) :
    (result.1, result.2.1) ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run state) := by
  rw [← PqxdhRecordFactsOriginMuteAdaptive.complete_erase target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work (state, false), support_map]
  exact ⟨result, supported, rfl⟩

/-- Every compatible supported callback and marked continuation realizing the concrete event has the actual selected writer reply `none`. -/
theorem event_reply_failed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (cut : Cut n (Client n E X)) (earlier : List (Cut n (Client n E X)))
    (prior : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier)
    (reply : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (answered : reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state))
    (result : Client n E X × (CtxPrivate n × Bool))
    (continued : result ∈ support ((simulateQ (service cut.pending.material modes replace setup codec)
      (cut.next reply.1)).run (reply.2, false)))
    (winning : FailedCutEvent codec route cut (result.1, result.2.1)) : reply.1 = none := by
  obtain ⟨_, frame, entry, present, matched, failed⟩ := winning
  have noSeal := PqxdhRecordFactsOriginMuteFresh.after_seal_noSeal cut.past cut.pending cut.next
    (PqxdhRecordFactsPrivateCacheSource.reach_fresh _
      (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary)
      (prefix_reach _ prior)) reply.1
  exact PqxdhRecordFactsOriginSealAlignment.suffix_failed modes ideal replace setup codec cut.pending cut.state reply answered
    (PqxdhRecordFactsOriginOrdinalReach.source_prefix_empty modes replace setup codec route env serverKid bounds mode adversary
      cut.pending cut.next cut.state cut.past (prefix_reach _ prior))
    (cut.next reply.1) noSeal (result.1, result.2.1)
    (suffix_support cut.pending.material modes replace setup codec (cut.next reply.1) reply.2 result continued) entry present frame matched failed

/-- The concrete failed-cut event raises the literal failed-writer marker on every compatible complete marked resumption. -/
theorem event_marked (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (cut : Cut n (Client n E X)) (earlier : List (Cut n (Client n E X)))
    (prior : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier)
    (result : (Client n E X × CtxPrivate n) × Bool)
    (supported : result ∈ support (PqxdhRecordFactsOriginFailedResume.resumeMarked modes setup codec replace cut))
    (winning : FailedCutEvent codec route cut result.1) : result.2 = true := by
  exact PqxdhRecordFactsOriginResumeConsumer.resume_event_flag modes ideal replace setup codec route env serverKid bounds mode adversary
    cut earlier prior (FailedCutEvent codec route cut) (fun _ good => good.1)
    (event_reply_failed modes ideal replace setup codec route env serverKid bounds mode adversary cut earlier prior) result supported winning

/-- Every supported attempted-ordinal cut discharges the concrete event-to-marker obligation from its actual source prefix. -/
theorem scan_marked (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (index : Nat) (cut : Cut n (Client n E X))
    (selected : Sum.inr cut ∈ support (PqxdhRecordFactsOriginOrdinalCut.scan
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      index (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []))
    (result : (Client n E X × CtxPrivate n) × Bool)
    (supported : result ∈ support (PqxdhRecordFactsOriginFailedResume.resumeMarked modes setup codec replace cut))
    (winning : FailedCutEvent codec route cut result.1) : result.2 = true := by
  obtain ⟨earlier, prior⟩ := PqxdhRecordFactsOriginOrdinalFinalPrefix.reach_prefix _
    (PqxdhRecordFactsOriginOrdinalCut.scan_prefix _ _ index _ [] cut selected).1
  exact event_marked modes ideal replace setup codec route env serverKid bounds mode adversary cut earlier prior result supported winning

/-- A retained failed-frame witness selects its actual insertion cut from this exact complete source path, with no identification of sibling paths. -/
theorem path_cut (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : PqxdhRecordFactsOriginOrdinalTrace.Result n (Client n E X))
    (path : PqxdhRecordFactsOriginOrdinalPath.Path (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) [] result)
    (label : Label n) (accepted : AcceptedTarget label route result.2)
    (frame : RawCtxReceive.DecodedFrame) (entry : CtxSuccessfulSeal)
    (present : entry ∈ (result.2.2.keys label).1.successfulSeals)
    (matched : Matches frame entry) (failed : codec.frameWrite frame = none) :
    ∃ cut ∈ result.1, FailedCutEvent codec route cut result.2 := by
  obtain ⟨cut, reply, earlier, later, finalPast, _, _, material, _, _, _, _, _, _, split⟩ :=
    PqxdhRecordFactsOriginOrdinalFinalPrefix.source_final_entry modes replace setup codec route env serverKid bounds mode budget adversary respects result path label entry present
  refine ⟨cut, ?_, ?_⟩
  · simp only [split, List.mem_append, List.mem_cons, true_or, or_true]
  · simpa only [FailedCutEvent, material] using And.intro accepted ⟨frame, entry, present, matched, failed⟩

/-- The retained result of this same tracked path is supported by the complete underlying source execution. -/
theorem tracked_support (impl : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (work : OracleComp (ServiceSpec n) X) (state : CtxPrivate n) (past : List (Label n))
    (result : PqxdhRecordFactsOriginOrdinalTrace.Result n X)
    (supported : result ∈ support (PqxdhRecordFactsOriginOrdinalTrace.track impl work state past)) :
    result.2 ∈ support ((simulateQ impl work).run state) := by
  rw [← PqxdhRecordFactsOriginOrdinalTrace.track_drop impl work state past, support_map]
  exact ⟨result, supported, rfl⟩

/-- Every actual unpublished acceptance selects a concrete failed-cut event in the cut list of this same complete source execution. -/
theorem source_cover (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : PqxdhRecordFactsOriginOrdinalTrace.Result n (Client n E X))
    (supported : result ∈ support (PqxdhRecordFactsOriginOrdinalTrace.track
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []))
    (unpublished : UnpublishedAccept codec route (ctxView result.2)) :
    ∃ cut ∈ result.1, FailedCutEvent codec route cut result.2 := by
  have ran := tracked_support _ _ _ [] result supported
  have path := PqxdhRecordFactsOriginOrdinalPath.support_path _ _ _ [] result supported
  obtain ⟨value, present, before, event, after, split, failedAt⟩ :=
    PqxdhRecordFactsOriginErasedPublication.erased_unpublished_failed modes ideal replace setup codec route readback env serverKid bounds mode adversary result.2 ran unpublished
  obtain ⟨receiver, raw, opened, handle, label, frame, entry, sender, received, routed, hidden, direction, decoded, recorded, matched, plaintext, owns, failed⟩ := failedAt
  change value ∈ result.2.1.1.map _ at present
  rw [Option.mem_def, Option.map_eq_some_iff] at present
  obtain ⟨actual, actualPresent, rfl⟩ := present
  change actual.2.1.2.transcript = before ++ event :: after at split
  have eventMember : event ∈ actual.2.1.2.transcript := by
    simp only [split, List.mem_append, List.mem_cons, true_or, or_true]
  obtain ⟨actualFrame, actualDecoded, sequence, senderEq⟩ :=
    PqxdhRecordFactsOriginMetadataGlobal.erased_received_metadata label modes replace setup codec route env serverKid bounds mode adversary
      _ result.2 ran actual actualPresent event eventMember receiver raw opened handle label.slot received routed hidden
  have frameEq : actualFrame = frame := Option.some.inj (actualDecoded.symm.trans decoded)
  obtain ⟨finalPast, finalPrefix⟩ := PqxdhRecordFactsOriginOrdinalFinalPrefix.path_prefix _ path
  have coordinate := PqxdhRecordFactsOriginSealAlignment.source_prefix_sequence modes ideal replace setup codec route env serverKid bounds mode budget adversary respects
    (pure result.2.1) result.2.2 finalPast result.1 finalPrefix label entry recorded
  have position : label.position + 1 = opened.sequence.val := by
    simpa only [sequence, frameEq] using coordinate.symm.trans matched.1.symm
  exact path_cut modes replace setup codec route env serverKid bounds mode budget adversary respects result path label
    ⟨actual, actualPresent, event, eventMember, receiver, raw, opened, handle, received, routed, hidden, direction, position⟩
    frame entry recorded matched failed

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.suffix_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.suffix_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.event_reply_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.event_reply_failed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.event_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.event_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.scan_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.scan_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.path_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.path_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.tracked_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.tracked_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.source_cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginCutEvent.source_cover
