-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSendAdmission
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability
open BeaconcryptCore.Refinement
variable {n :Nat} {I KemSK E P Reader Response :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}

def slice (bytes :Pqxdh.Bytes) (fits :bytes.length≤Usize.max) :Slice U8 :=
  RegistrationNativePlatformOrdinarySourceRouting.plaintext bytes fits

theorem slice_bytes (bytes :Pqxdh.Bytes) (fits :bytes.length≤Usize.max) :TranscriptAuthParts.absSlice (slice bytes fits)=bytes :=by
  simp [slice,RegistrationNativePlatformOrdinarySourceRouting.plaintext,TranscriptAuthParts.absSlice,List.map_map,Function.comp_def]

theorem slice_roundtrip (raw :Slice U8) (fits :(TranscriptAuthParts.absSlice raw).length≤Usize.max) :
    slice (TranscriptAuthParts.absSlice raw) fits=raw :=by
  apply Subtype.ext
  simp only [slice,RegistrationNativePlatformOrdinarySourceRouting.plaintext,TranscriptAuthParts.absSlice,List.map_map]
  change List.map (fun byte=>ProtocolComposition.concreteByte (PqxdhRefinement.absByte byte)) raw.val=raw.val
  simp only [FrameCodecReadBack.concrete_abs_byte]
  exact List.map_id raw.val

private theorem no_frame (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) (sequence sender :Nat) :
    CborRecordWorldClient.nextFits bytes.length sequence sender=false :=by
  cases fits :CborRecordWorldClient.nextFits bytes.length sequence sender with
  | false=>rfl
  | true=>exact False.elim (oversized (RegistrationNativePlatformSourceSendAdmission.representable _ _ _ fits))

private theorem set_same {A :Type} (items :List A) (index :Nat) (value :A) (found :items[index]?=some value) :
    items.set index value=items :=by
  induction items generalizing index with
  | nil=>simp at found
  | cons head tail ih=>cases index with
    | zero=>simp only [List.getElem?_cons_zero,Option.some.injEq] at found;cases found;rfl
    | succ index=>simpa using congrArg (List.cons head) (ih index (by simpa using found))

private theorem applied_pure {S A :Type} {m :Type →Type} [Monad m] (value :A) (before :S) :
    (pure value :StateT S m A) before=pure (value,before) :=rfl

variable [primitive :AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]
local notation "Base"=>StateT P ProbComp

theorem server (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
    (reserve :Nat →Base (core.result.Result Unit E))
    (view :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (erased :commitment.CommitmentTranscript) (route :RawCtxServerRouting.SenderDecoder)
    (keyId :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max)
    (before :PqxdhRecordLiftWorld.State n) :
    (RegistrationNativePlatformOrdinarySourceExecution.guarded (n:=n) setup wire reserve view failure erased route
      (.inr (.inr (.inl (.inl (bytes,keyId)))))).run before=pure (none,before) :=by
  unfold RegistrationNativePlatformOrdinarySourceExecution.guarded
  dsimp only [StateT.run]
  cases present :before.server with
  | none=>
    simp only [CborRecordWorldClient.refusal,CborRecordWorldCursor.worldShell,present,Option.map_none]
    change (RegistrationNativePlatformOrdinarySourceExecution.server setup wire reserve view failure erased bytes keyId).run before=_
    simp only [StateT.run,RegistrationNativePlatformOrdinarySourceExecution.server,present]
  | some selected=>
    cases peer :selected.records.server.peers keyId with
    | none=>
      simp only [CborRecordWorldClient.refusal,CborRecordWorldCursor.worldShell,present,Option.map_some,peer,Option.map_none]
      change (RegistrationNativePlatformOrdinarySourceExecution.server setup wire reserve view failure erased bytes keyId).run before=_
      simp only [StateT.run,RegistrationNativePlatformOrdinarySourceExecution.server,present,peer,
        RegistrationNativePlatformOrdinarySourceRouting.serverRecords,applied_pure,pure_bind,
        PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil]
      rw [←present]
    | some known=>
      simp only [CborRecordWorldClient.refusal,
        CborRecordWorldCursor.worldShell,present,Option.map_some,peer,no_frame bytes oversized,Bool.false_eq_true,ite_false]

theorem beacon (setup :PqxdhServerAuthExperiment.Setup base KemSK) (wire :RegistrationNativeWire.Wire)
    (reserve :Nat →Base (core.result.Result Unit E))
    (view :RegistrationNativePlatformSourceSeal.KeyView) (failure :primitive.Error)
    (erased :commitment.CommitmentTranscript) (route :RawCtxServerRouting.SenderDecoder)
    (index :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max)
    (before :PqxdhRecordLiftWorld.State n) :
    (RegistrationNativePlatformOrdinarySourceExecution.guarded (n:=n) setup wire reserve view failure erased route
      (.inr (.inr (.inr (index,.inl bytes))))).run before=pure (none,before) :=by
  unfold RegistrationNativePlatformOrdinarySourceExecution.guarded
  dsimp only [StateT.run]
  cases present :before.owners[index]? with
  | none=>
    simp only [CborRecordWorldClient.refusal,CborRecordWorldCursor.worldShell,present,Option.bind_none]
    change (RegistrationNativePlatformOrdinarySourceExecution.beacon setup wire reserve view failure erased index bytes).run before=_
    simp only [StateT.run,RegistrationNativePlatformOrdinarySourceExecution.beacon,present]
  | some phase=>cases phase with
    | inactive metadata=>
      simp only [CborRecordWorldClient.refusal,CborRecordWorldCursor.worldShell,present,Option.bind_some]
      change (RegistrationNativePlatformOrdinarySourceExecution.beacon setup wire reserve view failure erased index bytes).run before=_
      simp only [StateT.run,RegistrationNativePlatformOrdinarySourceExecution.beacon,present,
        RegistrationNativePlatformOrdinarySourceRouting.beaconRecords,applied_pure,pure_bind,
        PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil,Function.update_eq_self,set_same _ _ _ present]
    | established metadata kernel=>
      simp only [CborRecordWorldClient.refusal,
        CborRecordWorldCursor.worldShell,present,Option.bind_some,no_frame bytes oversized,Bool.false_eq_true,ite_false]

variable [AdapterInitEdPrimitive.Operations]
theorem raw_server (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential :RegistrationNativeMldsa.Credential source) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (reserveRegistration reservePeer :Base Bool) (reserveFrame :Nat →Base (core.result.Result Unit E))
    (erased :commitment.CommitmentTranscript)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base) (key :U64) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    RegistrationNativePlatformPublicAdapterRawModel.raw (n:=n) (Platform:=P) (source:=source) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend key bytes))=pure none :=by
  rw [RegistrationNativePlatformPublicAdapterRawModel.server_send]
  funext before
  change (fun result=>(result.1,RegistrationNativePlatformExtractedExperiment.replaceWorld before result.2)) <$>
    (RegistrationNativePlatformOrdinarySourceExecution.guarded (n:=n) setup RegistrationNativeConcreteCodec.wire reserveFrame view failure erased
      RegistrationNativePlatformPublicAdapterRouting.route (.inr (.inr (.inl (.inl (bytes,key)))))).run before.server.world.world.1=pure (none,before)
  rw [server setup RegistrationNativeConcreteCodec.wire reserveFrame view failure erased RegistrationNativePlatformPublicAdapterRouting.route key bytes oversized]
  simp only [map_pure]
  rfl

theorem raw_beacon (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential :RegistrationNativeMldsa.Credential source) (view :RegistrationNativePlatformSourceSeal.KeyView)
    (failure :primitive.Error) (allocation :RegistrationNativePlatformSourceSeal.Allocation E Base)
    (reserveRegistration reservePeer :Base Bool) (reserveFrame :Nat →Base (core.result.Result Unit E))
    (erased :commitment.CommitmentTranscript)
    (helper :QueryImpl (AdapterRecordHelperRequestMonad.Spec E) Base)
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) Base) (index :Nat) (bytes :Pqxdh.Bytes) (oversized :¬bytes.length≤Usize.max) :
    RegistrationNativePlatformPublicAdapterRawModel.raw (n:=n) (Platform:=P) (source:=source) setup checks representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index bytes))=pure none :=by
  rw [RegistrationNativePlatformPublicAdapterRawModel.beacon_send]
  funext before
  unfold RegistrationNativePlatformExtractedExperiment.record
  dsimp only [StateT.run]
  cases owned :before.beacons[index]? with
  | none=>rfl
  | some owner=>
    change (fun result=>(result.1,RegistrationNativePlatformExtractedExperiment.replaceWorld before result.2)) <$>
      (RegistrationNativePlatformOrdinarySourceExecution.guarded (n:=n) setup RegistrationNativeConcreteCodec.wire reserveFrame view failure erased
        RegistrationNativePlatformPublicAdapterRouting.route (.inr (.inr (.inr (owner.worldOwner,.inl bytes))))).run before.server.world.world.1=pure (none,before)
    rw [beacon setup RegistrationNativeConcreteCodec.wire reserveFrame view failure erased RegistrationNativePlatformPublicAdapterRouting.route owner.worldOwner bytes oversized]
    simp only [map_pure]
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.slice_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.slice_roundtrip' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.slice_roundtrip

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.raw_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.raw_server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.raw_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSendRepresentability.raw_beacon
