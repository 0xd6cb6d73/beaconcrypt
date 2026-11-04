-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendOperands
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution
import BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformExtractedSdkOrdinarySendOperands (owner sample)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

def finish (before : PqxdhRecordLiftWorld.State n) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (result : (((Option RawCtxSourceSend.Encrypted ×RawCtxWholeOwner.OwnerState Unit) ×
      RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :
    ((Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftWorld.State n) ×Platform) :=
  ((result.1.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inl ([],key))) result.1.2.2
    {before with server:=some {server with records:=
      ⟨RawCtxServerRouting.putPeer server.records.server key peer result.1.1.2.owner.kernel,result.1.1.2.rawAttempts⟩}
                 primitive:=result.1.2.1}),result.2)

def project (before : PqxdhRecordLiftWorld.State n) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (result : ((RustM AdapterRecordStatefulSend.Result ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :=
  finish before server key peer
    ((RegistrationNativePlatformExtractedSdkOrdinarySendCommon.project
      (owner key peer.metadata peer.kernel server.records.rawAttempts) result.1.1,result.1.2),result.2)

omit primitives [FrameDispatchFallback.Operations] in
private theorem input (bytes : Slice U8) (bounded : (TranscriptAuthParts.absSlice bytes).length≤Usize.max) :
    RegistrationNativePlatformOrdinarySourceRouting.plaintext (TranscriptAuthParts.absSlice bytes) bounded=bytes :=
  AdapterPublicConcreteCodecs.input_roundtrip bytes

theorem world (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (bytes : Slice U8)
    (present : before.server=some server) (selected : server.records.server.peers key=some peer) :
    project before server key peer <$>
      (((sample setup (ledgerCodec wire) reserve view failure erased key server.sender peer.metadata peer.kernel bytes).run
        (before.primitive,[])).run previous) =
    if CborRecordWorldClient.nextFits bytes.val.length peer.kernel.refined.control.send_sequence.val server.sender.val then
      (((RegistrationNativePlatformOrdinaryWorld.serverStep setup (ledgerCodec wire) reserve (fun _=>none)
        (.inl (TranscriptAuthParts.absSlice bytes,key))).run before).run previous)
    else pure ((none,before),previous) := by
  have cursor : (CborRecordWorldCursor.worldShell before).server=some
      (⟨server.sender,fun kid=>(server.records.server.peers kid).map (fun p=>p.kernel.refined.control.send_sequence.val)⟩ : CborRecordWorldClient.Server) := by
    simp only [CborRecordWorldCursor.worldShell,present,Option.map_some]
  have size : (TranscriptAuthParts.absSlice bytes).length=bytes.val.length := by
    simp only [TranscriptAuthParts.absSlice,List.length_map]
  have core:=congrArg (fun work=>(work.run (before.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinarySendOperands.native setup (ledgerCodec wire) reserve length view converted failure erased
      key server.sender peer.metadata peer.kernel bytes server.records.rawAttempts)
  simp only [StateT.run_map] at core
  have lifted:=congrArg (fun distribution=>finish before server key peer <$>distribution) core
  simp only [Functor.map_map] at lifted
  unfold project
  cases fits : CborRecordWorldClient.nextFits bytes.val.length peer.kernel.refined.control.send_sequence.val server.sender.val with
  | false=>
      simp only [fits,Bool.false_eq_true,ite_false,StateT.run_pure,map_pure] at lifted
      rw [lifted]
      simp only [Bool.false_eq_true,ite_false]
      have unchanged:=RawCtxServerRouting.putPeer_entry server.records.server key peer selected
      simp only [finish,owner,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil,unchanged,←present]
  | true=>
      simp only [fits,ite_true] at lifted
      have forwarded : CborRecordWorldClient.refusal (n:=n)
          (.inr (.inr (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))))
          (CborRecordWorldCursor.worldShell before)=none := by
        simp only [CborRecordWorldClient.refusal,cursor,selected,Option.map_some,size,fits,ite_true]
      simp only [ite_true]
      rw [←RegistrationNativePlatformOrdinarySourceExecution.server_source setup wire reserve length view converted failure erased (fun _=>none)
        (TranscriptAuthParts.absSlice bytes) key before forwarded]
      have bounded : (TranscriptAuthParts.absSlice bytes).length≤Usize.max := by
        simpa only [size] using bytes.property
      simp only [StateT.run,RegistrationNativePlatformOrdinarySourceExecution.server,present,
        RegistrationNativePlatformOrdinarySourceRouting.serverRecords,selected,dite_eq_left bounded]
      rw [input bytes bounded]
      rw [RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_source setup (ledgerCodec wire) reserve length view converted failure erased
        _ bytes _ _ rfl]
      let work:=RegistrationNativePlatformExtractedSdkOrdinarySendCommon.ownerNative setup (ledgerCodec wire) reserve
        (owner key peer.metadata peer.kernel server.records.rawAttempts) server.sender bytes
      let first:=fun result : Option RawCtxSourceSend.Encrypted ×RawCtxWholeOwner.OwnerState Unit =>
        (result.1,(⟨RawCtxServerRouting.putPeer server.records.server key peer result.2.owner.kernel,result.2.rawAttempts⟩ : RawCtxServerRouting.State Unit (Array U8 281#usize)))
      let last:=fun result : ((Option RawCtxSourceSend.Encrypted ×RawCtxServerRouting.State Unit (Array U8 281#usize)) ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) =>
        (result.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inl (TranscriptAuthParts.absSlice bytes,key))) result.2.2
          {before with server:=some {server with records:=result.1.2},primitive:=result.2.1})
      change _=((last <$> ((first <$>work).run (before.primitive,[]))).run previous)
      rw [StateT.run_map,StateT.run_map,StateT.run_map,Functor.map_map]
      simp only [StateT.run] at lifted
      rw [lifted]
      rfl

theorem guarded (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (bytes : Slice U8)
    (present : before.server=some server) (selected : server.records.server.peers key=some peer) :
    project before server key peer <$>
      (((sample setup (ledgerCodec wire) reserve view failure erased key server.sender peer.metadata peer.kernel bytes).run
        (before.primitive,[])).run previous) =
    (((RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserve route
      (.inr (.inr (.inl (.inl (TranscriptAuthParts.absSlice bytes,key)))))).run before).run previous) := by
  refine (world setup wire reserve length view converted failure erased before previous server key peer bytes present selected).trans ?_
  have cursor : (CborRecordWorldCursor.worldShell before).server=some
      (⟨server.sender,fun kid=>(server.records.server.peers kid).map (fun p=>p.kernel.refined.control.send_sequence.val)⟩ : CborRecordWorldClient.Server) := by
    simp only [CborRecordWorldCursor.worldShell,present,Option.map_some]
  have size : (TranscriptAuthParts.absSlice bytes).length=bytes.val.length := by
    simp only [TranscriptAuthParts.absSlice,List.length_map]
  simp only [StateT.run,RegistrationNativePlatformOrdinaryWorld.guarded,CborRecordWorldClient.refusal,cursor,selected,Option.map_some,size]
  split_ifs <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerSendWorld.guarded
