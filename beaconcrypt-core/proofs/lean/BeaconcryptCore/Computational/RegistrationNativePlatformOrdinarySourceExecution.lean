-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceReceive
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformOrdinaryWorld (M)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
noncomputable def server (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (bytes : Pqxdh.Bytes) (keyId : U64) :
    M n Platform (Option RawCtxSourceSend.Encrypted) := fun before =>
  match before.server with
  | none => pure (none,before)
  | some server => do
      let result←(RegistrationNativePlatformOrdinarySourceRouting.serverRecords setup (ledgerCodec wire) reserve view failure erased
        server bytes keyId).run (before.primitive,[])
      pure (result.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.serverTag (.inl (bytes,keyId))) result.2.2
        {before with server:=some {server with records:=result.1.2},primitive:=result.2.1})
noncomputable def beacon (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (index : Nat) (bytes : Pqxdh.Bytes) :
    M n Platform (Option RawCtxSourceSend.Encrypted) := fun before =>
  match before.owners[index]? with
  | none => pure (none,before)
  | some phase => do
      let result←(RegistrationNativePlatformOrdinarySourceRouting.beaconRecords setup (ledgerCodec wire) reserve view failure erased
        ⟨phase,before.ownerRaw index⟩ bytes).run (before.primitive,[])
      pure (result.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag index) result.2.2
        { before with
          owners := before.owners.set index result.1.2.phase
          ownerRaw := Function.update before.ownerRaw index result.1.2.rawAttempts
          primitive := result.2.1 })
noncomputable def handler (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (M n Platform)
  | .inr (.inr (.inl (.inl (bytes,keyId))))=>server setup wire reserve view failure erased bytes keyId
  | .inr (.inr (.inl (.inr bytes)))=>RegistrationNativePlatformOrdinarySourceReceive.server setup wire erased.bytes route bytes
  | .inr (.inr (.inr (index,.inl bytes)))=>beacon setup wire reserve view failure erased index bytes
  | .inr (.inr (.inr (index,.inr bytes)))=>RegistrationNativePlatformOrdinarySourceReceive.beacon setup wire erased.bytes index bytes
  | query=>RegistrationNativePlatformOrdinaryWorld.handler setup (ledgerCodec wire) reserve route query
noncomputable def guarded (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (M n Platform) :=
  fun query before=>match CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply=>pure (reply,before)
  | none=>(handler setup wire reserve view failure erased route query).run before

omit primitives [FrameDispatchFallback.Operations] in
private theorem journal_apply {A : Type} (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (primitive : PqxdhRecordLiftWorld.Primitive) :
    simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (ledgerCodec wire) reserve) work (primitive,[]) =
      PqxdhRecordLiftLoggedAdapters.swapResult <$>
        simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec wire) reserve)
          (PqxdhDeploymentNative.logged work) primitive :=
  RegistrationNativePlatformOrdinaryLogged.program_source _ work primitive []
theorem server_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (bytes : Pqxdh.Bytes) (keyId : U64) (before : PqxdhRecordLiftWorld.State n)
    (forwarded : CborRecordWorldClient.refusal (n:=n) (.inr (.inr (.inl (.inl (bytes,keyId)))))
      (CborRecordWorldCursor.worldShell before)=none) :
    (server setup wire reserve view failure erased bytes keyId).run before =
      (RegistrationNativePlatformOrdinaryWorld.serverStep setup (ledgerCodec wire) reserve route (.inl (bytes,keyId))).run before := by
  cases present : before.server with
  | none => simp only [StateT.run,server,RegistrationNativePlatformOrdinaryWorld.serverStep,present]
  | some selected =>
      have fits : ∀peer,selected.records.server.peers keyId=some peer→bytes.length≤Usize.max := by
        intro peer found
        exact RegistrationNativePlatformSourceSendAdmission.server (CborRecordWorldCursor.worldShell before)
          ⟨selected.sender,fun kid=>(selected.records.server.peers kid).map (fun p=>p.kernel.refined.control.send_sequence.val)⟩
          keyId bytes peer.kernel.refined.control.send_sequence.val
          (by simp only [CborRecordWorldCursor.worldShell,present,Option.map_some])
          (by simp only [found,Option.map_some]) forwarded
      simp only [StateT.run,server,RegistrationNativePlatformOrdinaryWorld.serverStep,present]
      rw [RegistrationNativePlatformOrdinarySourceRouting.serverRecords_source setup (ledgerCodec wire) reserve length view converted failure erased selected bytes keyId fits]
      rw [journal_apply]
      simp only [bind_map_left,PqxdhRecordLiftLoggedAdapters.swapResult]
      rfl
theorem beacon_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (index : Nat) (bytes : Pqxdh.Bytes) (before : PqxdhRecordLiftWorld.State n)
    (forwarded : CborRecordWorldClient.refusal (n:=n) (.inr (.inr (.inr (index,.inl bytes))))
      (CborRecordWorldCursor.worldShell before)=none) :
    (beacon setup wire reserve view failure erased index bytes).run before =
      (RegistrationNativePlatformOrdinaryWorld.beaconStep setup (ledgerCodec wire) reserve index (.inl bytes)).run before := by
  cases found : before.owners[index]? with
  | none => simp only [StateT.run,beacon,RegistrationNativePlatformOrdinaryWorld.beaconStep,found,PqxdhDeploymentNative.absent]
  | some phase =>
      have fits : ∀shell kernel,phase=.established shell kernel→bytes.length≤Usize.max := by
        intro shell kernel active
        subst phase
        exact RegistrationNativePlatformSourceSendAdmission.owner (CborRecordWorldCursor.worldShell before)
          ⟨shell.identityKeyId,kernel.refined.control.send_sequence.val⟩ index bytes
          (by simp only [CborRecordWorldCursor.worldShell,found,Option.bind_some]) forwarded
      simp only [StateT.run,beacon,RegistrationNativePlatformOrdinaryWorld.beaconStep,found]
      rw [RegistrationNativePlatformOrdinarySourceRouting.beaconRecords_source setup (ledgerCodec wire) reserve length view converted failure erased
        ⟨phase,before.ownerRaw index⟩ bytes (by simpa only using fits)]
      rw [journal_apply]
      simp only [bind_map_left,PqxdhRecordLiftLoggedAdapters.swapResult]
      rfl
/-- The four current ordinary record routes execute their actual extracted source controllers with the same complete World and persistent platform state. -/
theorem guarded_source (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder) :
    guarded (n:=n) setup wire reserve view failure erased route =
      RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserve route := by
  funext query before
  cases refused : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply => simp only [guarded,RegistrationNativePlatformOrdinaryWorld.guarded,refused]
  | none =>
      simp only [guarded,RegistrationNativePlatformOrdinaryWorld.guarded,refused]
      rcases query with created | (effect | (serverQuery | ⟨index,beaconQuery⟩))
      · rfl
      · rfl
      · cases serverQuery with
        | inl pair =>
          rcases pair with ⟨bytes,keyId⟩
          exact server_source setup wire reserve sealLength view converted failure erased route bytes keyId before refused
        | inr bytes =>
          exact congrFun (RegistrationNativePlatformOrdinarySourceReceive.server_source setup wire reserve openLength erased.bytes route bytes) before
      · cases beaconQuery with
        | inl bytes => exact beacon_source setup wire reserve sealLength view converted failure erased index bytes before refused
        | inr bytes =>
          exact congrFun (RegistrationNativePlatformOrdinarySourceReceive.beacon_source setup wire reserve openLength erased.bytes index bytes) before

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution.server_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution.beacon_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution.guarded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution.guarded_source
