-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate
/-! The actual ordinary source receive preparation and dynamic kernel driver share the complete native raw-owner distribution, including every refused raw attempt and the unchanged writer journal/platform state. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver (Primitive State M liftPrimitive)
variable {Platform E I KemSK Reader Response Metadata A B : Type} {base : OracleSpec I}

noncomputable def sample (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 227#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (expected : U64) (ad : Array U8 151#usize) (bytes : Slice U8) :
    M Platform (RustM AdapterRecordStatefulReceive.Result) :=
  match AdapterPublicOrdinaryEnvelope.prepareReceive bytes expected with
  | .ok (some view) => RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received setup codec erased kernel view.sequence view.ciphertext ad view.sender
  | _ => pure (.ok (kernel,none))

def publish (owner : RawCtxWholeOwner.OwnerState Metadata)
    (outcome : RustM RecordEffectsReceiveProgram.Result) : Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Metadata :=
  match outcome with
  | .ok result => RawCtxWholeOwner.publish owner result
  | _ => RawCtxWholeOwner.publish owner (owner.owner.kernel,none)

def project (owner : RawCtxWholeOwner.OwnerState Metadata) (outcome : RustM AdapterRecordStatefulReceive.Result) :
    Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Metadata :=
  publish owner (AdapterRecordReceive.decodeResult <$>outcome)

private theorem lift_pure (value : A) :
    liftPrimitive (Platform:=Platform) (pure value : StateT Primitive ProbComp A)=pure value := by
  funext before previous
  change ((liftPrimitive (Platform:=Platform) (pure value : StateT Primitive ProbComp A)).run before).run previous=_
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_run,StateT.run_pure,map_pure]
  rfl

private theorem lift_bind (work : StateT Primitive ProbComp A) (next : A →StateT Primitive ProbComp B) :
    liftPrimitive (Platform:=Platform) (work >>=next)=
      (liftPrimitive work >>=fun value =>liftPrimitive (next value)) := by
  funext before previous
  change ((liftPrimitive (Platform:=Platform) (work >>=next)).run before).run previous=
    ((liftPrimitive work >>=fun value =>liftPrimitive (next value)).run before).run previous
  simp only [RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_run,StateT.run_bind,
    map_bind,bind_map_left]

private theorem outer_map (observe : A →B) (work : ProbComp A) :
    (StateT.lift (observe <$>work) : StateT Platform ProbComp B)=observe <$>StateT.lift work := by
  funext previous
  change ((StateT.lift (observe <$>work) : StateT Platform ProbComp B).run previous)=
    (observe <$> (StateT.lift work : StateT Platform ProbComp A)).run previous
  simp only [StateT.run_lift,StateT.run_map,bind_pure_comp,Functor.map_map]

private theorem leaf (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (query : RawCtxSourceOpen.NativeSpec.Domain) :
    simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve) (RawCtxMixedOwner.receiveLift query)=
      liftPrimitive (RegistrationNativeExtractedReceive.primitives setup codec query) := by
  rcases query with request | (bytes | input)
  all_goals simp only [RawCtxMixedOwner.receiveLift,simulateQ_spec_query,
    RegistrationNativeExtractedReceive.primitives,QueryImpl.apply_compose]
  all_goals funext before
  all_goals change ((fun result =>(result.1,(result.2,before.2))) <$>
    (StateT.lift ((PqxdhRecordLiftWorld.primitives setup codec _).run before.1) : StateT Platform ProbComp _))=_
  all_goals exact (outer_map _ _).symm

private theorem program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (work : OracleComp RawCtxSourceOpen.NativeSpec A) :
    simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup codec reserve) (simulateQ RawCtxMixedOwner.receiveLift work)=
      liftPrimitive (simulateQ (RegistrationNativeExtractedReceive.primitives setup codec) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,lift_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,leaf,lift_bind,ih]

theorem received (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 227#usize) (raw : Pqxdh.Bytes)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (sequence : U64) (payload : Slice U8)
    (ad : Array U8 151#usize) (sender : U64) :
    project owner <$>RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received (Platform:=Platform) setup codec erased owner.owner.kernel sequence payload ad sender=
      RawCtxWholeOwner.publish owner <$>liftPrimitive
        (RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.model setup codec raw owner.owner.kernel sequence payload ad sender) := by
  unfold project
  rw [←Functor.map_map,
    RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_model_lift setup codec length erased raw owner.owner.kernel sequence payload ad sender,
    Functor.map_map]
  rfl

private theorem parse_empty (bytes : Slice U8)
    (blank : (TranscriptAuthParts.absSlice bytes).isEmpty=true) :
    RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)=none := by
  obtain ⟨parsed,decoded,projection⟩ := AdapterPublicOrdinaryReceiveGate.decode bytes
  have length : bytes.val.length=0 := by
    simpa only [TranscriptAuthParts.absSlice,List.length_map] using List.isEmpty_iff_length_eq_zero.mp blank
  have absent : parsed=none := RustM.ok.inj (decoded.symm.trans (FrameCodecRoundtrip.decode_short bytes (by omega)))
  rw [absent] at projection
  exact projection

theorem native (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 227#usize) (owner : RawCtxWholeOwner.OwnerState Metadata)
    (ad : Array U8 151#usize) (sameAD : owner.owner.associatedData=PqxdhRefinement.absBytes ad) (bytes : Slice U8) :
    project owner <$>sample setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire)
      erased owner.owner.kernel owner.owner.expectedSender ad bytes=
    simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
      (simulateQ RawCtxMixedOwner.receiveAdapter
        ((RawCtxWholeOwner.rawReceive (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)).run owner)) := by
  have read : (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)=
      CborProductionBoundary.decoded <$>RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes) := by
    rw [AdapterPublicOrdinaryReceiveGate.frame_read,RegistrationNativeConcreteCodec.frame_projection]
  unfold RawCtxMixedOwner.receiveAdapter
  rw [QueryImpl.simulateQ_compose,program]
  unfold sample
  rw [AdapterPublicOrdinaryReceiveGate.prepare]
  by_cases blank : (TranscriptAuthParts.absSlice bytes).isEmpty=true
  · have absent := parse_empty bytes blank
    simp only [absent,Option.bind_none,map_pure,RawCtxWholeOwner.rawReceive,StateT.run,blank,ite_true,simulateQ_pure,lift_pure]
    rfl
  · have nonempty : (TranscriptAuthParts.absSlice bytes).isEmpty=false := Bool.eq_false_iff.mpr blank
    cases parsed : RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes) with
    | none =>
      simp only [Option.bind_none,map_pure,RawCtxWholeOwner.rawReceive,StateT.run,nonempty,Bool.false_eq_true,ite_false,read,parsed]
      rfl
    | some frame =>
      have decoded : (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)=
          some (CborProductionBoundary.decoded frame) := by
        rw [read,parsed]
        rfl
      by_cases sender : frame.sender=owner.owner.expectedSender
      · simp only [Option.bind_some,AdapterPublicOrdinaryReceiveGate.admitted,sender,ite_true]
        rw [received setup (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire) length erased
          (TranscriptAuthParts.absSlice bytes) owner frame.sequence frame.payload ad owner.owner.expectedSender,
          ←RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_map]
        unfold RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.model
        have sameFrame : (⟨frame.sequence,owner.owner.expectedSender,RawCtxNativeFramePrelude.sliceBytes frame.payload⟩ : RawCtxReceive.DecodedFrame)=
            CborProductionBoundary.decoded frame := by
          change (⟨frame.sequence,owner.owner.expectedSender,RawCtxNativeFramePrelude.sliceBytes frame.payload⟩ : RawCtxReceive.DecodedFrame)=
            ⟨frame.sequence,frame.sender,RawCtxNativeFramePrelude.sliceBytes frame.payload⟩
          rw [sender]
        rw [sameFrame,←sameAD]
        simp only [RawCtxWholeOwner.rawReceive,StateT.run,nonempty,Bool.false_eq_true,ite_false,decoded]
        by_cases valid : RawCtxReceive.ValidFrame owner.owner.expectedSender owner.owner.associatedData (CborProductionBoundary.decoded frame)
        · rw [ite_eq_left valid,ite_eq_left valid]
          simp only [bind_pure_comp,simulateQ_map]
          rfl
        · rw [ite_eq_right valid,ite_eq_right valid]
          simp only [simulateQ_pure,map_pure]
      · simp only [Option.bind_some,AdapterPublicOrdinaryReceiveGate.admitted,sender,ite_false,map_pure]
        have invalid : ¬RawCtxReceive.ValidFrame owner.owner.expectedSender owner.owner.associatedData (CborProductionBoundary.decoded frame) :=
          fun valid =>sender valid.1
        simp only [RawCtxWholeOwner.rawReceive,StateT.run,nonempty,Bool.false_eq_true,ite_false,decoded,invalid,
          simulateQ_pure,lift_pure]
        rfl

theorem normal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 227#usize) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (expected : U64) (ad : Array U8 151#usize) (bytes : Slice U8)
    (before after : State) (previous next : Platform) (reply : RustM AdapterRecordStatefulReceive.Result)
    (supported : ((reply,after),next)∈support
      (((sample setup codec erased kernel expected ad bytes).run before).run previous)) :
    ∃returned,reply=.ok returned := by
  unfold sample at supported
  rw [AdapterPublicOrdinaryReceiveGate.prepare] at supported
  cases selected : (RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).bind
      (AdapterPublicOrdinaryReceiveGate.admitted expected) with
  | none =>
      simp only [selected,StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
      cases supported
      exact ⟨(kernel,none),rfl⟩
  | some view =>
      simp only [selected,RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received,
        RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.lift_run,support_map] at supported
      obtain ⟨generated,called,equal⟩ := supported
      have same : generated.1=reply := congrArg (fun result =>result.1.1) equal
      obtain ⟨returned,actual⟩ := RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received_normal setup codec length erased
        (TranscriptAuthParts.absSlice bytes) kernel view.sequence view.ciphertext ad view.sender before.1 generated.2 generated.1 called
      exact ⟨returned,same.symm.trans actual⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.received' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.received

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.normal
