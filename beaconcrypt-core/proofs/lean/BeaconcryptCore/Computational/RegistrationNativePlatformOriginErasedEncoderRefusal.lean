-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedAttribution
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginLedgerSendReply
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginReplyJointObservation
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAccepted
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedEncoderRefusal
open CtxRomAuth PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response E Failure A : Type} {baseSpec : OracleSpec ι}
private theorem nonseal_program (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy (fun query => ∀pending,query≠.sealing pending))
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run before)) :
    ∀label,(result.2.keys label).1.successfulSeals=(before.keys label).1.successfulSeals := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact fun _ => rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    have kept := PqxdhRecordFactsOriginOrdinalServices.service_nonSeal modes
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (PqxdhRecordFactsPrivateCacheWorld.baseInterpreter setup codec) codec.frameWrite replace
      query quiet.1 before middle called
    intro label
    exact (ih middle.1 (quiet.2 middle.1) middle.2 result continued label).trans (kept label)

private theorem source_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E) :
    (RegistrationNativePlatformGatedRecordFlat.native (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      env reserve codec route query).run before =
    RegistrationNativePlatformGatedRecordFlat.join <$>
      (simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
        (RegistrationNativePlatformOriginNativeTails.source env reserve codec route (Spec.query query)
          before.1.1.1 before.1.1.2 before.1.2)).run before.2 := by
  simpa only [simulateQ_spec_query,RegistrationNativePlatformOriginNativeTails.source,
    CborRawRecordOriginFlatten.interpret] using RegistrationNativePlatformGatedRecordFlat.native_program
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route (Spec.query query)
    before.1.1.1 before.1.1.2 before.1.2 before.2


private theorem envelope_refused (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (beforeP : E)
    (work : OracleComp (ServiceSpec n) (((Option RawCtxSourceSend.Encrypted × E) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n))
    (form : RegistrationNativePlatformOriginNativeTails.ReplyEnvelope reserve beforeP work)
    (before : CtxPrivate n)
    (result : (((Option RawCtxSourceSend.Encrypted × E) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n)
    (supported : result∈support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) work).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry∉(before.keys label).1.successfulSeals)
    (present : entry∈(result.2.keys label).1.successfulSeals)
    (frame : RawCtxReceive.DecodedFrame) (matched : PqxdhRecordFactsOriginReplay.Matches frame entry)
    (refused : codec.frameWrite frame=none) : result.1.1.1.1=none := by
  obtain ⟨pending,tag,shell,control,form⟩ := form
  obtain ⟨⟨receipt,afterEq⟩⟩ := RegistrationNativePlatformOriginSendAcquisition.envelope_erased_given modes replace setup codec
    reserve beforeP work pending tag (fun output state => (((output,state),shell),control)) form before result supported label entry absent present
  obtain ⟨_produced,unchanged | ⟨width,record,inserted,_logged,reply⟩⟩ :=
    PqxdhRecordFactsOriginSealFacts.erased_sealing_trace modes ideal replace setup codec receipt.pending receipt.looked.2 receipt.sealed receipt.sealCalled
  · exact (receipt.fresh ((unchanged.2.2 label) ▸ receipt.inserted)).elim
  · have member : entry∈(receipt.sealed.2.keys receipt.pending.material).1.successfulSeals := Eq.mpr (congrArg (fun coordinate => entry∈(receipt.sealed.2.keys coordinate).1.successfulSeals) receipt.material) receipt.inserted
    rw [inserted,List.mem_cons] at member
    rcases member with same | old
    · have generated : PqxdhRecordFactsOriginReplay.Matches
        (⟨receipt.pending.sequence,receipt.pending.context.senderId,record.encode⟩ : RawCtxReceive.DecodedFrame) entry := by
        exact Eq.mpr (congrArg (fun candidate => PqxdhRecordFactsOriginReplay.Matches
          (⟨receipt.pending.sequence,receipt.pending.context.senderId,record.encode⟩ : RawCtxReceive.DecodedFrame) candidate) same)
          ⟨rfl,rfl,rfl⟩
      have frameEq := PqxdhRecordFactsOriginAccepted.matches_unique _ frame entry generated matched
      have sealNone : receipt.sealed.1=none := by
        rw [←frameEq] at refused
        simpa only [refused,Option.map_none] using reply
      have tail := receipt.tailCalled
      rw [afterEq,sealNone] at tail
      simp only [RegistrationNativePlatformOriginReserveContinuationBound.continued,
        RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,simulateQ_bind,simulateQ_spec_query,
        simulateQ_pure,StateT.run_bind,pure_bind] at tail
      rw [mem_support_bind_iff] at tail
      obtain ⟨published,_called,finished⟩ := tail
      have returned := (mem_support_pure_iff _ _).mp finished
      exact congrArg (fun value => value.1.1.1.1) returned
    · apply False.elim
      apply receipt.fresh
      exact Eq.mp (congrArg (fun coordinate => entry∈(receipt.looked.2.keys coordinate).1.successfulSeals) receipt.material) old

/-- A source encoder refusal for the exact newly retained seal is an actual refusal of the same erased native send, including every cursor and allocation branch. -/
theorem query (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (nativeQuery : Spec.Domain)
    (before : CborRawRecordFlat.NativeState n E) (result : Spec.Range nativeQuery × CborRawRecordFlat.NativeState n E)
    (supported : result∈support ((RegistrationNativePlatformGatedRecordFlat.native
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) env reserve codec route nativeQuery).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (absent : entry∉(before.2.keys label).1.successfulSeals)
    (present : entry∈(result.2.2.keys label).1.successfulSeals)
    (frame : RawCtxReceive.DecodedFrame) (matched : PqxdhRecordFactsOriginReplay.Matches frame entry)
    (refused : codec.frameWrite frame=none) :
    RegistrationNativePlatformOriginLedgerSendReply.nativeReply nativeQuery result.1=none := by
  have sending := RegistrationNativePlatformOriginErasedAttribution.query_sending modes replace setup codec route env reserve
    nativeQuery before result supported label entry absent present
  rcases sending with ⟨keyId,plaintext,rfl⟩ | ⟨owner,plaintext,rfl⟩
  · rw [source_run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    rcases RegistrationNativePlatformOriginNativeTails.server_reply_form env reserve codec route
      before.1.1.1 before.1.1.2 before.1.2 keyId plaintext with quiet | form
    · have kept := nonseal_program modes replace setup codec _ (quiet.mono (by
        intro request absent pending same
        exact absent ⟨pending,same⟩)) before.2 inner called label
      exact (absent (kept ▸ present)).elim
    · exact envelope_refused modes ideal replace setup codec reserve before.1.1.1 _ form before.2 inner called
        label entry absent present frame matched refused
  · rw [source_run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    rcases RegistrationNativePlatformOriginNativeTails.beacon_reply_form env reserve codec route
      before.1.1.1 before.1.1.2 before.1.2 owner plaintext with quiet | form
    · have kept := nonseal_program modes replace setup codec _ (quiet.mono (by
        intro request absent pending same
        exact absent ⟨pending,same⟩)) before.2 inner called label
      exact (absent (kept ▸ present)).elim
    · exact envelope_refused modes ideal replace setup codec reserve before.1.1.1 _ form before.2 inner called
        label entry absent present frame matched refused
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedEncoderRefusal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedEncoderRefusal.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedEncoderRefusal.query
