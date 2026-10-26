-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginOrdinalPrefixFlag
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSealFacts

/-! Universal same-execution reconstruction of each selected marked source resumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhRecordFactsOriginHandles
open PqxdhRecordFactsOriginOrdinalCut (Cut)
open PqxdhRecordFactsOriginOrdinalPath (Prefix prefix_reach)
open PqxdhRecordFactsOriginOrdinalMarkedPath (Flagged support_flagged flagged_support)
open PqxdhRecordFactsOriginFailedResume (resumeMarked)
open PqxdhRecordFactsOriginMarkerNative (service)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- A concrete actual final-transcript acceptance selects this physical hidden coordinate using the returned sequence. -/
def AcceptedTarget (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (result : Client n E X × CtxPrivate n) : Prop :=
  ∃ value ∈ result.1.1, ∃ entry ∈ value.2.1.2.transcript, ∃ receiver raw opened handle,
    entry.received = some (receiver, raw, .Some opened) ∧ receivingHandle route receiver raw = some handle ∧
    handleSlot result.1.2 handle = some target.slot ∧ target.direction = !handleDirection handle ∧
    target.position + 1 = opened.sequence.val

/-- A whole literal source run with this concrete final acceptance has raised its own marker. -/
theorem program_target_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool)
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial))
    (accepted : AcceptedTarget target route (result.1, result.2.1)) : result.2.2 = true := by
  obtain ⟨value, present, entry, recorded, receiver, raw, opened, handle, received, routed, slot, direction, position⟩ := accepted
  exact PqxdhRecordFactsOriginMarkerGlobal.program_received_flag target modes replace setup codec route env serverKid bounds mode
    adversary initial result supported value present entry recorded receiver raw opened handle received routed slot direction position

/-- Every compatible literal marked suffix reconstructs the same whole source execution through this actual empty-dictionary prefix; a final selected acceptance therefore raises that suffix's own flag. -/
theorem suffix_target_flag (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (cut : Cut n (Client n E X))
    (earlier : List (Cut n (Client n E X)))
    (prefixPath : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier)
    (reply : (ServiceSpec n).Range (.sealing cut.pending) × CtxPrivate n)
    (answered : reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state))
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service cut.pending.material modes replace setup codec)
      (cut.next reply.1)).run (reply.2, false)))
    (accepted : AcceptedTarget cut.pending.material route (result.1, result.2.1)) : result.2.2 = true := by
  obtain ⟨cuts, flagged⟩ := support_flagged cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) (cut.next reply.1) reply.2
    (cut.past ++ [cut.pending.material]) false result supported
  have empty := PqxdhRecordFactsOriginOrdinalReach.source_prefix_empty modes replace setup codec route env serverKid bounds mode adversary
    cut.pending cut.next cut.state cut.past (prefix_reach _ prefixPath)
  have whole := PqxdhRecordFactsOriginOrdinalPrefixFlag.sealing_prefix_false cut.pending.material codec.frameRead
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
    (fun query state output supported entry present => PqxdhRecordFactsOriginSealFacts.erased_service_mono
      modes ideal replace setup codec query state output supported cut.pending.material entry present)
    cut.pending cut.next prefixPath empty reply answered (cuts, (result.1, result.2.1)) result.2.2 flagged
  exact program_target_flag cut.pending.material modes replace setup codec route env serverKid bounds mode adversary
    (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial, false) result
    (flagged_support cut.pending.material (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) whole) accepted

/-- A concrete selected event with an actual failed callback witness implies the exact failed-writer marker on every supported full resumption, without substituting a sibling execution. -/
theorem resume_event_flag (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (cut : Cut n (Client n E X))
    (earlier : List (Cut n (Client n E X)))
    (prefixPath : Prefix (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial) []
      ((ServiceSpec n).query (.sealing cut.pending) >>= cut.next) cut.state cut.past earlier)
    (event : Client n E X × CtxPrivate n → Prop)
    (accepts : ∀ final, event final → AcceptedTarget cut.pending.material route final)
    (failed : ∀ reply ∈ support ((PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec (.sealing cut.pending)).run cut.state),
      ∀ result ∈ support ((simulateQ (service cut.pending.material modes replace setup codec)
        (cut.next reply.1)).run (reply.2, false)), event (result.1, result.2.1) → reply.1 = none)
    (result : (Client n E X × CtxPrivate n) × Bool)
    (supported : result ∈ support (resumeMarked modes setup codec replace cut))
    (winning : event result.1) : result.2 = true := by
  simp only [resumeMarked, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨reply, answered, final, continued, rfl⟩ := supported
  simpa only [failed reply answered final continued winning, Option.isNone_none, Bool.true_and] using
    suffix_target_flag modes ideal replace setup codec route env serverKid bounds mode adversary cut earlier prefixPath
      reply answered final continued (accepts _ winning)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer.program_target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer.program_target_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer.suffix_target_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer.suffix_target_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer.resume_event_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginResumeConsumer.resume_event_flag
