-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationPrefixes

/-! The actual unpublished-acceptance event selects a matching frame whose literal writer failed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordLiftInterface PqxdhRecordLiftFlat
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginAccepted PqxdhRecordFactsOriginReplay
open PqxdhRecordFactsOriginPublicationTemporal PqxdhRecordFactsOriginPublicationPrefixes
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Receiver Entry FreshBounds Mode ModeSpec)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The public view preserves the exact initialized receive-prefix witnesses. -/
theorem ctxView_prefixes (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    ∀ value ∈ (ctxView result).result, Prefixes codec route result.1.2 result.2 value.2.1.transcript := by
  intro value member
  change value ∈ result.1.1.map _ at member
  rw [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  exact ctxRun_prefixes modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported original originalMember

/-- The literal successful receive matches an owned hidden seal whose complete decoded frame failed its writer. -/
def FailedWriterAt (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (event : Entry) : Prop :=
  ∃ receiver raw opened handle label frame entry sender,
    event.received = some (receiver, raw, .Some opened) ∧
    receivingHandle route receiver raw = some handle ∧
    handleSlot control handle = some label.slot ∧ label.direction = !handleDirection handle ∧
    codec.frameRead raw = some frame ∧ entry ∈ (secret.keys label).1.successfulSeals ∧
    Matches frame entry ∧ entry.input.plaintext = opened.plaintext ∧
    OwnsLabel control label sender ∧ codec.frameWrite frame = none

/-- Exact receive-prefix evidence rules out every earlier publication alternative of the frozen forged event. -/
theorem forged_failed (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n) (before : List Entry) (event : Entry)
    (history : ReceivedBefore codec route control secret before event)
    (forged : ForgedAt codec route (handleSlot control) before event) :
    FailedWriterAt codec route control secret event := by
  obtain ⟨receiver, raw, opened, handle, slot, frame, received, routed, hidden, decoded, unpublished⟩ := forged
  obtain ⟨actualHandle, actualRouted, accepted⟩ := history receiver raw opened received
  have handleEq : actualHandle = handle := Option.some.inj (actualRouted.symm.trans routed)
  subst actualHandle
  rcases accepted with known | ⟨label, installed, direction, actualFrame, actualDecoded,
    entry, member, matched, plaintext, sender, owned, outcome⟩
  · have absent := known_no_slot control handle known
    rw [absent] at hidden
    cases hidden
  · have slotEq : label.slot = slot := Option.some.inj (installed.symm.trans hidden)
    have frameEq : actualFrame = frame := Option.some.inj (actualDecoded.symm.trans decoded)
    subst actualFrame
    refine ⟨receiver, raw, opened, handle, label, frame, entry, sender, received, routed, installed,
      direction, decoded, member, matched, plaintext, owned, ?_⟩
    rcases outcome with failed | published
    · exact failed
    · have counterpart := counterpart_of_opposite control label sender handle owned direction
      rw [slotEq] at counterpart
      exact False.elim (unpublished sender counterpart published)

/-- Every actual unpublished acceptance in the initialized adaptive source has an exact failed-writer seal witness at that transcript event. -/
theorem ctxRun_unpublished_failed (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (unpublished : UnpublishedAccept codec route (ctxView result)) :
    ∃ value ∈ (ctxView result).result, ∃ before event after,
      value.2.1.transcript = before ++ event :: after ∧
      FailedWriterAt codec route result.1.2 result.2 event := by
  obtain ⟨value, present, before, event, after, split, forged⟩ := unpublished
  have history := ctxView_prefixes modes ideal replace setup codec route readback env serverKid bounds mode adversary
    result supported value present before event after split
  exact ⟨value, present, before, event, after, split, forged_failed codec route result.1.2 result.2 before event history forged⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent.ctxView_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent.ctxView_prefixes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent.forged_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent.forged_failed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent.ctxRun_unpublished_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationEvent.ctxRun_unpublished_failed
