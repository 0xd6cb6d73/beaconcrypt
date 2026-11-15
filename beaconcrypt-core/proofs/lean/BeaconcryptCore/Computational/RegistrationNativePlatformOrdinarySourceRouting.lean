-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceLoggedWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformOrdinarySourceJournal (native)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
def plaintext (bytes : Pqxdh.Bytes) (fits : bytes.length≤Usize.max) : Slice U8 :=
  ⟨bytes.map ProtocolComposition.concreteByte, by simpa only [List.length_map] using fits⟩
@[simp] private theorem plaintext_bytes (bytes : Pqxdh.Bytes) (fits : bytes.length≤Usize.max) :
    TranscriptAuthParts.absSlice (plaintext bytes fits)=bytes := by
  simp [plaintext,TranscriptAuthParts.absSlice,List.map_map,Function.comp_def]
noncomputable def serverRecords [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (server : PqxdhRecordLiftWorld.Server)
    (bytes : Pqxdh.Bytes) (keyId : U64) :
    StateT RegistrationNativePlatformOrdinarySourceJournal.State (StateT Platform ProbComp)
      (Option RawCtxSourceSend.Encrypted × RawCtxServerRouting.State Unit (Array U8 151#usize)) :=
  match server.records.server.peers keyId with
  | none => pure (none,server.records)
  | some peer =>
      if fits : bytes.length≤Usize.max then do
        let result←RegistrationNativePlatformOrdinarySourceLoggedWorld.owner setup codec reserve view failure erased
          ⟨MldsaServerRouting.selected PqxdhRefinement.absBytes keyId peer,server.records.rawAttempts⟩
          (plaintext bytes fits) server.sender peer.metadata
        pure (result.1,⟨RawCtxServerRouting.putPeer server.records.server keyId peer result.2.owner.kernel,
          result.2.rawAttempts⟩)
      else pure (none,server.records)
theorem serverRecords_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (server : PqxdhRecordLiftWorld.Server) (bytes : Pqxdh.Bytes) (keyId : U64)
    (fits : ∀peer,server.records.server.peers keyId=some peer→bytes.length≤Usize.max) :
    serverRecords setup codec reserve view failure erased server bytes keyId =
      simulateQ (native setup codec reserve)
        ((MldsaServerRouting.handler PqxdhRefinement.absBytes (fun _=>server.sender)
          (fun _=>none) codec.frameRead (.inl (bytes,keyId))).run server.records) := by
  cases found : server.records.server.peers keyId with
  | none => simp only [serverRecords,found,StateT.run,MldsaServerRouting.handler,MldsaServerRouting.send,simulateQ_pure]
  | some peer =>
      simp only [serverRecords,found,dite_eq_left (fits peer found)]
      rw [RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_source setup codec reserve length view converted failure erased
        _ _ _ _ rfl]
      simp only [plaintext_bytes,StateT.run,MldsaServerRouting.handler,MldsaServerRouting.send,found,
        RawCtxMixedOwner.ownerImpl,simulateQ_bind,simulateQ_pure]
      rfl
noncomputable def beaconRecords [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (before : PqxdhRecordLiftBeacon.State)
    (bytes : Pqxdh.Bytes) : StateT RegistrationNativePlatformOrdinarySourceJournal.State (StateT Platform ProbComp)
      (Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftBeacon.State) :=
  match before.phase with
  | .inactive _ => pure (none,before)
  | .established shell kernel =>
      if fits : bytes.length≤Usize.max then do
        let result←RegistrationNativePlatformOrdinarySourceLoggedWorld.owner setup codec reserve view failure erased
          ⟨⟨kernel,shell.control.server_binding.identity_key_id,PqxdhRefinement.absBytes shell.associatedData,()⟩,before.rawAttempts⟩
          (plaintext bytes fits) shell.identityKeyId shell.associatedData
        pure (result.1,⟨.established shell result.2.owner.kernel,result.2.rawAttempts⟩)
      else pure (none,before)
theorem beaconRecords_source [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (before : PqxdhRecordLiftBeacon.State) (bytes : Pqxdh.Bytes)
    (fits : ∀shell kernel,before.phase=.established shell kernel→bytes.length≤Usize.max) :
    beaconRecords setup codec reserve view failure erased before bytes =
      simulateQ (native setup codec reserve) ((PqxdhRecordLiftBeacon.handler codec.frameRead (.inl bytes)).run before) := by
  cases phase : before.phase with
  | inactive phase => simp only [beaconRecords,phase,StateT.run,PqxdhRecordLiftBeacon.handler,
      PqxdhRecordLiftBeacon.rejected,simulateQ_pure]
  | established shell kernel =>
      simp only [beaconRecords,phase,dite_eq_left (fits shell kernel phase)]
      rw [RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_source setup codec reserve length view converted failure erased
        _ _ _ _ rfl]
      simp only [plaintext_bytes,StateT.run,PqxdhRecordLiftBeacon.handler,phase,
        RawCtxMixedOwner.ownerImpl,simulateQ_bind,simulateQ_pure]
      rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting.serverRecords_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting.serverRecords_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting.beaconRecords_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceRouting.beaconRecords_source
