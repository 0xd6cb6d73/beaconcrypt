-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinarySendCommon
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativePlatformExtractedSdkOrdinarySendCommon (owner ownerNative sample)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

def shell (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) : PqxdhRecordLiftInterface.BeaconShell :=
  ⟨self.identity_key_kid,control,binding.associated_data⟩

def finish (before : PqxdhRecordLiftWorld.State n) (index : Nat) (sourceShell : PqxdhRecordLiftInterface.BeaconShell)
    (result : (((Option RawCtxSourceSend.Encrypted ×RawCtxWholeOwner.OwnerState Unit) ×
      RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :
    ((Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftWorld.State n) ×Platform) :=
  ((result.1.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag index) result.1.2.2
    {before with owners:=before.owners.set index (.established sourceShell result.1.1.2.owner.kernel)
                 ownerRaw:=Function.update before.ownerRaw index result.1.1.2.rawAttempts
                 primitive:=result.1.2.1}),result.2)

def project (before : PqxdhRecordLiftWorld.State n) (index : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (result : ((RustM AdapterRecordStatefulSend.Result ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :=
  finish before index (shell self control binding)
    ((RegistrationNativePlatformExtractedSdkOrdinarySendCommon.project (owner control binding kernel (before.ownerRaw index)) result.1.1,result.1.2),result.2)

omit material ed primitives [FrameDispatchFallback.Operations] in
private theorem input (bytes : Slice U8) (bounded : (TranscriptAuthParts.absSlice bytes).length≤Usize.max) :
    RegistrationNativePlatformOrdinarySourceRouting.plaintext (TranscriptAuthParts.absSlice bytes) bounded=bytes := by
  exact AdapterPublicConcreteCodecs.input_roundtrip bytes

omit material ed primitives [FrameDispatchFallback.Operations] in
private theorem set_same {A : Type} (values : List A) (index : Nat) (value : A)
    (found : values[index]?=some value) : values.set index value=values := by
  obtain ⟨below,selected⟩ := List.getElem?_eq_some_iff.mp found
  rw [←selected]
  exact List.set_getElem_self below

theorem world (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript)
    (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (index : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (present : before.owners[index]?=some (.established (shell self control binding) kernel)) :
    project before index self control binding kernel <$>
      (((sample setup (ledgerCodec wire) reserve view failure erased self control binding kernel bytes).run
        (before.primitive,[])).run previous) =
    if CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val self.identity_key_kid.val then
      (((RegistrationNativePlatformOrdinaryWorld.beaconStep setup (ledgerCodec wire) reserve index
        (.inl (TranscriptAuthParts.absSlice bytes))).run before).run previous)
    else pure ((none,before),previous) := by
  have cursor : (CborRecordWorldCursor.worldShell before).owners index=some
      (⟨self.identity_key_kid,kernel.refined.control.send_sequence.val⟩ : CborRecordWorldClient.Cursor) := by
    simp only [CborRecordWorldCursor.worldShell,present,Option.bind_some,shell]
  have size : (TranscriptAuthParts.absSlice bytes).length=bytes.val.length := by
    simp only [TranscriptAuthParts.absSlice,List.length_map]
  have core:=congrArg (fun work=>(work.run (before.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.sample_native setup (ledgerCodec wire) reserve length view converted failure erased
      self control binding kernel bytes (before.ownerRaw index))
  simp only [StateT.run_map] at core
  have lifted:=congrArg (fun distribution=>finish before index (shell self control binding) <$>distribution) core
  simp only [Functor.map_map] at lifted
  unfold project
  cases fits : CborRecordWorldClient.nextFits bytes.val.length kernel.refined.control.send_sequence.val self.identity_key_kid.val with
  | false=>
      simp only [fits,Bool.false_eq_true,ite_false,StateT.run_pure,map_pure] at lifted
      rw [lifted]
      simp only [Bool.false_eq_true,ite_false]
      have unchanged:=set_same before.owners index (.established (shell self control binding) kernel) present
      simp only [finish,owner,PqxdhRecordLiftWorld.produce,List.map_nil,List.append_nil,unchanged,Function.update_eq_self]
  | true=>
      simp only [fits,ite_true] at lifted
      have forwarded : CborRecordWorldClient.refusal (n:=n)
          (.inr (.inr (.inr (index,.inl (TranscriptAuthParts.absSlice bytes)))))
          (CborRecordWorldCursor.worldShell before)=none := by
        simp only [CborRecordWorldClient.refusal,cursor,size,fits,ite_true]
      simp only [ite_true]
      rw [←RegistrationNativePlatformOrdinarySourceExecution.beacon_source setup wire reserve length view converted failure erased index
        (TranscriptAuthParts.absSlice bytes) before forwarded]
      have bounded : (TranscriptAuthParts.absSlice bytes).length≤Usize.max := by
        simpa only [size] using bytes.property
      simp only [StateT.run,RegistrationNativePlatformOrdinarySourceExecution.beacon,present,
        RegistrationNativePlatformOrdinarySourceRouting.beaconRecords,dite_eq_left bounded]
      rw [input bytes bounded]
      rw [RegistrationNativePlatformOrdinarySourceLoggedWorld.owner_source setup (ledgerCodec wire) reserve length view converted failure erased
        _ bytes _ _ rfl]
      let work := ownerNative setup (ledgerCodec wire) reserve (owner control binding kernel (before.ownerRaw index)) self.identity_key_kid bytes
      let first := fun result : Option RawCtxSourceSend.Encrypted ×RawCtxWholeOwner.OwnerState Unit =>
        (result.1, (⟨.established (shell self control binding) result.2.owner.kernel,result.2.rawAttempts⟩ : PqxdhRecordLiftBeacon.State))
      let last := fun result : ((Option RawCtxSourceSend.Encrypted ×PqxdhRecordLiftBeacon.State) ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) =>
        (result.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag index) result.2.2
          {before with owners:=before.owners.set index result.1.2.phase
                       ownerRaw:=Function.update before.ownerRaw index result.1.2.rawAttempts
                       primitive:=result.2.1})
      change _=((last <$> ((first <$>work).run (before.primitive,[]))).run previous)
      rw [StateT.run_map]
      rw [StateT.run_map]
      rw [StateT.run_map]
      rw [Functor.map_map]
      simp only [StateT.run] at lifted
      rw [lifted]
      rfl


theorem guarded (setup : Setup base KemSK) (wire : Wire)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (view : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (index : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (present : before.owners[index]?=some (.established (shell self control binding) kernel)) :
    project before index self control binding kernel <$>
      (((sample setup (ledgerCodec wire) reserve view failure erased self control binding kernel bytes).run
        (before.primitive,[])).run previous) =
    (((RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec wire) reserve route
      (.inr (.inr (.inr (index,.inl (TranscriptAuthParts.absSlice bytes)))))).run before).run previous) := by
  refine (world setup wire reserve length view converted failure erased before previous index self control binding kernel bytes present).trans ?_
  have cursor : (CborRecordWorldCursor.worldShell before).owners index=some
      (⟨self.identity_key_kid,kernel.refined.control.send_sequence.val⟩ : CborRecordWorldClient.Cursor) := by
    simp only [CborRecordWorldCursor.worldShell,present,Option.bind_some,shell]
  have size : (TranscriptAuthParts.absSlice bytes).length=bytes.val.length := by
    simp only [TranscriptAuthParts.absSlice,List.length_map]
  simp only [StateT.run,RegistrationNativePlatformOrdinaryWorld.guarded,CborRecordWorldClient.refusal,cursor,size]
  split_ifs <;>rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld.guarded
