-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (ledgerCodec)
open RegistrationNativePlatformExtractedSdkOrdinaryDriver (State)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}

def owner (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) : RawCtxWholeOwner.OwnerState Unit :=
  ⟨MldsaServerRouting.selected PqxdhRefinement.absBytes key peer,server.records.rawAttempts⟩

def finish (before : PqxdhRecordLiftWorld.State n) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (result : (((Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Unit) ×State) ×Platform)) :
    ((Option RawCtxWholeOwner.Decrypted ×PqxdhRecordLiftWorld.State n) ×Platform) :=
  ((result.1.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inr [])) result.1.2.2
    {before with server:=some {server with records:=
      ⟨RawCtxServerRouting.putPeer server.records.server key peer result.1.1.2.owner.kernel,result.1.1.2.rawAttempts⟩}
                 primitive:=result.1.2.1}),result.2)

def project (before : PqxdhRecordLiftWorld.State n) (server : PqxdhRecordLiftWorld.Server) (key : U64)
    (peer : RawCtxServerRouting.Peer (Array U8 281#usize))
    (result : ((RustM AdapterRecordStatefulReceive.Result ×State) ×Platform)) :=
  finish before server key peer
    ((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.project (owner server key peer) result.1.1,result.1.2),result.2)

noncomputable def model (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (bytes : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.M n Platform (Option RawCtxWholeOwner.Decrypted) := fun before=>
  match before.server with
  | none=>pure (none,before)
  | some server=>do
      let result←(simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
        ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _=>server.sender) route
          (ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (.inr bytes)).run server.records)).run (before.primitive,[])
      pure (result.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inr bytes)) result.2.2
        {before with server:=some {server with records:=result.1.2},primitive:=result.2.1})

theorem model_source (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n) :
    (model setup reserve route bytes).run before=
      (RegistrationNativePlatformOrdinaryWorld.serverStep setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve route (.inr bytes)).run before := by
  cases present:before.server with
  | none=>simp only [model,RegistrationNativePlatformOrdinaryWorld.serverStep,StateT.run,present]
  | some server=>
      have journal : simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
          ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _=>server.sender) route
            (ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (.inr bytes)).run server.records) (before.primitive,[]) =
          PqxdhRecordLiftLoggedAdapters.swapResult <$>
            simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
              (PqxdhDeploymentNative.logged
                ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _=>server.sender) route
                  (ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (.inr bytes)).run server.records)) before.primitive :=
        RegistrationNativePlatformOrdinaryLogged.program_source _ _ before.primitive []
      simp only [model,RegistrationNativePlatformOrdinaryWorld.serverStep,StateT.run,present]
      simp only [StateT.run] at journal
      rw [journal]
      simp only [bind_map_left,PqxdhRecordLiftLoggedAdapters.swapResult]

theorem world (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto) (erased : Array U8 357#usize)
    (route : RawCtxServerRouting.SenderDecoder)
    (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (bytes : Slice U8)
    (present : before.server=some server) (selected : server.records.server.peers key=some peer)
    (routed : route (TranscriptAuthParts.absSlice bytes)=some key) :
    project before server key peer <$>
      (((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup (ledgerCodec RegistrationNativeConcreteCodec.wire)
        erased peer.kernel key peer.metadata bytes).run (before.primitive,[])).run previous) =
    (((RegistrationNativePlatformOrdinaryWorld.serverStep setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve route
      (.inr (TranscriptAuthParts.absSlice bytes))).run before).run previous) := by
  have core:=congrArg (fun work=>(work.run (before.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.native setup reserve length erased
      (owner server key peer) peer.metadata rfl bytes)
  simp only [StateT.run_map] at core
  have lifted:=congrArg (fun distribution=>finish before server key peer <$>distribution) core
  simp only [Functor.map_map] at lifted
  rw [←model_source setup reserve route (TranscriptAuthParts.absSlice bytes) before]
  simp only [StateT.run,model,present]
  simp only [StateT.run,MldsaServerRouting.handler,MldsaServerRouting.receive,routed,selected,
    RawCtxMixedOwner.ownerImpl,simulateQ_bind,simulateQ_pure]
  let work:=simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
    (simulateQ RawCtxMixedOwner.receiveAdapter
      ((RawCtxWholeOwner.rawReceive (ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)).run (owner server key peer)))
  let first:=fun result : Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Unit=>
    (result.1,(⟨RawCtxServerRouting.putPeer server.records.server key peer result.2.owner.kernel,result.2.rawAttempts⟩ : RawCtxServerRouting.State Unit (Array U8 281#usize)))
  let last:=fun result : ((Option RawCtxWholeOwner.Decrypted ×RawCtxServerRouting.State Unit (Array U8 281#usize)) ×State)=>
    (result.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inr (TranscriptAuthParts.absSlice bytes))) result.2.2
      {before with server:=some {server with records:=result.1.2},primitive:=result.2.1})
  change _=((last <$> ((first <$>work).run (before.primitive,[]))).run previous)
  rw [StateT.run_map,StateT.run_map,StateT.run_map,Functor.map_map]
  simp only [StateT.run] at lifted
  unfold project
  dsimp only [owner,MldsaServerRouting.selected] at lifted ⊢
  rw [lifted]
  rfl

theorem guarded (setup : Setup base KemSK)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto) (erased : Array U8 357#usize)
    (route : RawCtxServerRouting.SenderDecoder)
    (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (server : PqxdhRecordLiftWorld.Server)
    (key : U64) (peer : RawCtxServerRouting.Peer (Array U8 281#usize)) (bytes : Slice U8)
    (present : before.server=some server) (selected : server.records.server.peers key=some peer)
    (routed : route (TranscriptAuthParts.absSlice bytes)=some key) :
    project before server key peer <$>
      (((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup (ledgerCodec RegistrationNativeConcreteCodec.wire)
        erased peer.kernel key peer.metadata bytes).run (before.primitive,[])).run previous) =
    (((RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve route
      (.inr (.inr (.inl (.inr (TranscriptAuthParts.absSlice bytes)))))).run before).run previous) := by
  exact world setup reserve length erased route before previous server key peer bytes present selected routed

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.model_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.model_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryServerReceiveWorld.guarded
