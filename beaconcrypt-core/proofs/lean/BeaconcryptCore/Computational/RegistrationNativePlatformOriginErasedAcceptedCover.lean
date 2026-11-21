-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerPath
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedPathFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedTemporalWithheld
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAcceptedCover
open RegistrationNativeStageTrace (Call Path Executed)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode handleSlot)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FullSpec Entry Handle FreshBounds)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response E Failure : Type} {base : OracleSpec I}
variable (modes : Label n→KeyMode) (ideal : ∀label,modes label≠.real) (replace : Pqxdh.Bytes→Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat→StateT E ProbComp (core.result.Result Unit Failure)) (serverKeyId : U64) (bounds : FreshBounds)
local notation "Runtime"=>CborRawRecordFlat.NativeState n E
local notation "Whole"=>PqxdhDeploymentSecrecy.Ledger×Runtime
local notation "service"=>PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "full"=>RegistrationNativePlatformGatedRecordFlat.full service env reserve setup.source.crypto codec route serverKeyId bounds
include ideal readback in
/-- A physical original unpublished receive on a same-run erased full path has the exact earlier counted callback with a newly acquired seal and refused original public reply, plus its actual final accepted coordinate. The sequence fact is the source alignment invariant derived by WarmEntrySequence. -/
theorem cover (initial : Runtime) (final : Whole) (calls : List (Call FullSpec Whole))
    (actual : Path full (PqxdhDeploymentSecrecy.Ledger.empty,initial) calls final)
    (safe : PqxdhRecordLiftProtocolHistory.Safe initial.1.2)
    (empty : ∀label,(initial.2.keys label).1.successfulSeals=[])
    (consistent : ∀label entry,entry∈(final.2.2.keys label).1.successfulSeals→entry.input.context.ad.seq=label.position+1)
    (leading : List Entry) (currentEntry : Entry) (later : List Entry)
    (ledger : final.1.transcript=leading++currentEntry::later)
    (forged : PqxdhRecordLiftIdeal.ForgedAt codec route (handleSlot final.2.1.2) leading currentEntry) :
    ∃ (label : Label n) (sealEntry : CtxRomAuth.CtxSuccessfulSeal) (receiver : PqxdhDeploymentInterface.Receiver)
      (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted) (handle : Handle),
      currentEntry.received=some (receiver,raw,.Some opened) ∧
      PqxdhRecordLiftIdeal.receivingHandle route receiver raw=some handle ∧
      handleSlot final.2.1.2 handle=some label.slot ∧
      label.direction = !PqxdhRecordFactsOriginHandles.handleDirection handle ∧label.position+1=opened.sequence.val ∧
      ∃ (current : Call FullSpec Whole),∃pre post,calls=pre++current::post ∧
        RegistrationNativePlatformOriginSendCallbackBudget.Sending current.query ∧
        sealEntry∉(current.before.2.2.keys label).1.successfulSeals ∧
        sealEntry∈(current.after.2.2.keys label).1.successfulSeals ∧
        RegistrationNativePlatformOriginLedgerSendSyntax.reply current.query current.reply=none := by
  obtain ⟨receiver,raw,opened,handle,slot,frame,received,routed,hidden,decoded,unpublished⟩:=forged
  obtain ⟨receiveCall,pre,post,split,sameEntry,beforeLedger,prior,called,future⟩:=
    RegistrationNativePlatformOriginLedgerPath.entry modes replace setup codec route env reserve serverKeyId bounds actual leading currentEntry later
      (by simpa only [PqxdhDeploymentSecrecy.Ledger.empty,List.nil_append] using ledger)
  have receivedCall : (⟨receiveCall.query,receiveCall.reply⟩:Entry).received=some (receiver,raw,.Some opened) := by
    rw [sameEntry];exact received
  have safeBefore:=(RegistrationNativePlatformOriginErasedInitialized.path_step modes replace setup codec route env reserve serverKeyId bounds prior safe).1
  obtain ⟨actualHandle,actualRoute,accepted⟩:=RegistrationNativePlatformOriginErasedReceive.full_received_before modes replace setup codec route env reserve serverKeyId bounds
    receiveCall.query receiveCall.before safeBefore (receiveCall.reply,receiveCall.after) called receiver raw opened receivedCall
  have handleEq : actualHandle=handle := Option.some.inj (actualRoute.symm.trans routed)
  subst actualHandle
  have suffix : Path full receiveCall.before (receiveCall::post) final:=.cons receiveCall called post final future
  have advanced:=RegistrationNativePlatformOriginErasedInitialized.path_step modes replace setup codec route env reserve serverKeyId bounds suffix safeBefore
  have notKnown : ¬PqxdhRecordLiftFlat.KnownAt receiveCall.before.2.1.2 handle := by
    intro known
    have finalKnown:=RegistrationNativePlatformOriginErasedPathFacts.known modes replace setup codec route env reserve serverKeyId bounds suffix handle known
    have absent:=PqxdhRecordFactsOriginAccepted.known_no_slot final.2.1.2 handle finalKnown
    rw [hidden] at absent
    cases absent
  obtain ⟨label,beforeSlot,direction,sourceFrame,sourceDecoded,sealEntry,member,matched,_plaintext⟩:=accepted.resolve_left notKnown
  have frameEq : sourceFrame=frame := Option.some.inj (sourceDecoded.symm.trans decoded)
  subst sourceFrame
  have finalSlot:=PqxdhRecordFactsOriginHandles.handleSlot_step receiveCall.before.2.1.2 final.2.1.2 advanced handle label.slot beforeSlot
  have sameSlot : label.slot=slot :=Option.some.inj (finalSlot.symm.trans hidden)
  have retained:=RegistrationNativePlatformOriginErasedPathFacts.seals modes replace setup codec route env reserve serverKeyId bounds ideal suffix label sealEntry member
  have sequence:=consistent label sealEntry retained
  obtain ⟨metaHandle,metaRoute,metadata⟩:=RegistrationNativePlatformOriginErasedReceive.full_received_sequence modes replace setup codec route env reserve serverKeyId bounds
    receiveCall.query receiveCall.before (receiveCall.reply,receiveCall.after) called receiver raw opened receivedCall frame decoded
  have metaEq : metaHandle=handle :=Option.some.inj (metaRoute.symm.trans routed)
  subst metaHandle
  have openedSequence:=metadata.resolve_left notKnown
  have position : label.position+1=opened.sequence.val :=sequence.symm.trans (matched.1.symm.trans (congrArg (fun value : Std.U64=>value.val) openedSequence.symm))
  obtain ⟨current,earlier,following,firstSplit,earlierPath,currentCalled,followingPath,counted,absent,inserted,refused⟩:=
    RegistrationNativePlatformOriginErasedTemporalWithheld.outer_refused modes ideal replace setup codec route readback env reserve serverKeyId bounds
      initial receiveCall.before final pre (receiveCall::post) prior suffix safe label sealEntry handle frame (empty label) member matched direction
      (by
        intro sender counterpart
        have original:=unpublished sender (by simpa only [sameSlot] using counterpart)
        simpa only [PqxdhDeploymentSecrecy.Ledger.empty,List.nil_append] using beforeLedger ▸ original)
  refine ⟨label,sealEntry,receiver,raw,opened,handle,received,routed,finalSlot,direction,position,current,earlier,following++receiveCall::post,?_,counted,absent,inserted,refused⟩
  rw [split,firstSplit,List.append_assoc,List.cons_append]
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAcceptedCover
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAcceptedCover.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAcceptedCover.cover
