-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (ledgerCodec)
open RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendWorld (shell)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

def finish (before : PqxdhRecordLiftWorld.State n) (index : Nat) (sourceShell : PqxdhRecordLiftInterface.BeaconShell)
    (result : (((Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Unit) ×
      RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :
    ((Option RawCtxWholeOwner.Decrypted ×PqxdhRecordLiftWorld.State n) ×Platform) :=
  ((result.1.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag index) result.1.2.2
    {before with owners:=before.owners.set index (.established sourceShell result.1.1.2.owner.kernel)
                 ownerRaw:=Function.update before.ownerRaw index result.1.1.2.rawAttempts
                 primitive:=result.1.2.1}),result.2)

def project (before : PqxdhRecordLiftWorld.State n) (index : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (result : ((RustM AdapterRecordStatefulReceive.Result ×RegistrationNativePlatformExtractedSdkOrdinaryDriver.State) ×Platform)) :=
  finish before index (shell self control binding)
    ((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.project
      (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner control binding kernel (before.ownerRaw index)) result.1.1,result.1.2),result.2)

omit material ed in
private theorem journal_apply {A : Type} (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (work : OracleComp RawCtxMixedOwner.NativeSpec A) (primitive : PqxdhRecordLiftWorld.Primitive) :
    simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve) work (primitive,[]) =
      PqxdhRecordLiftLoggedAdapters.swapResult <$>
        simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
          (PqxdhDeploymentNative.logged work) primitive :=
  RegistrationNativePlatformOrdinaryLogged.program_source _ work primitive []

theorem world (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (erased : Array U8 227#usize) (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (index : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (present : before.owners[index]?=some (.established (shell self control binding) kernel)) :
    project before index self control binding kernel <$>
      (((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup (ledgerCodec RegistrationNativeConcreteCodec.wire)
        erased kernel control.server_binding.identity_key_id binding.associated_data bytes).run
        (before.primitive,[])).run previous) =
      (((RegistrationNativePlatformOrdinaryWorld.beaconStep setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve index
        (.inr (TranscriptAuthParts.absSlice bytes))).run before).run previous) := by
  have core:=congrArg (fun work=>(work.run (before.primitive,[])).run previous)
    (RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.native setup reserve length erased
      (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner control binding kernel (before.ownerRaw index)) binding.associated_data rfl bytes)
  simp only [StateT.run_map] at core
  have lifted:=congrArg (fun distribution=>finish before index (shell self control binding) <$>distribution) core
  simp only [Functor.map_map] at lifted
  unfold project
  simp only [RegistrationNativePlatformOrdinaryWorld.beaconStep,present,StateT.run,PqxdhRecordLiftBeacon.handler,
    RawCtxMixedOwner.ownerImpl,bind_pure_comp,PqxdhDeploymentNative.logged_map,simulateQ_map]
  let code := simulateQ RawCtxMixedOwner.receiveAdapter
    ((RawCtxWholeOwner.rawReceive (ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)).run
      (RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner control binding kernel (before.ownerRaw index)))
  have journal:=congrArg (fun work=>work.run previous) (journal_apply setup reserve code before.primitive)
  change ((simulateQ (RegistrationNativePlatformOrdinarySourceJournal.native setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve) code).run (before.primitive,[])).run previous=
    (PqxdhRecordLiftLoggedAdapters.swapResult <$>
      (simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
        (PqxdhDeploymentNative.logged code)).run before.primitive).run previous at journal
  rw [StateT.run_map] at journal
  simp only [StateT.run,code] at journal
  simp only [StateT.run] at lifted
  rw [journal] at lifted
  simp only [Functor.map_map] at lifted
  let work :=simulateQ (RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve)
    (PqxdhDeploymentNative.logged code)
  let first : ((Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Unit) ×PqxdhRecordLiftLoggedAdapters.Frames) →
      ((Option RawCtxWholeOwner.Decrypted ×PqxdhRecordLiftBeacon.State) ×PqxdhRecordLiftLoggedAdapters.Frames) :=Prod.map (fun result : Option RawCtxWholeOwner.Decrypted ×RawCtxWholeOwner.OwnerState Unit =>
    (result.1,(⟨.established (shell self control binding) result.2.owner.kernel,result.2.rawAttempts⟩ : PqxdhRecordLiftBeacon.State))) id
  let last:=fun result : (((Option RawCtxWholeOwner.Decrypted ×PqxdhRecordLiftBeacon.State) ×PqxdhRecordLiftLoggedAdapters.Frames) ×PqxdhRecordLiftWorld.Primitive) =>
    (result.1.1.1,PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag index) result.1.2
      {before with owners:=before.owners.set index result.1.1.2.phase
                   ownerRaw:=Function.update before.ownerRaw index result.1.1.2.rawAttempts
                   primitive:=result.2})
  change _=((last <$> ((first <$>work).run before.primitive)).run previous)
  rw [StateT.run_map,StateT.run_map,StateT.run_map,Functor.map_map]
  dsimp only [RegistrationNativePlatformExtractedSdkOrdinarySendCommon.owner] at lifted ⊢
  rw [lifted]
  rfl


theorem guarded (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (route : RawCtxServerRouting.SenderDecoder) (erased : Array U8 227#usize) (before : PqxdhRecordLiftWorld.State n) (previous : Platform) (index : Nat)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconEstablished)
    (binding : session.SessionBinding) (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8)
    (present : before.owners[index]?=some (.established (shell self control binding) kernel)) :
    project before index self control binding kernel <$>
      (((RegistrationNativePlatformExtractedSdkOrdinaryReceiveCommon.sample setup (ledgerCodec RegistrationNativeConcreteCodec.wire)
        erased kernel control.server_binding.identity_key_id binding.associated_data bytes).run (before.primitive,[])).run previous) =
    (((RegistrationNativePlatformOrdinaryWorld.guarded setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve route
      (.inr (.inr (.inr (index,.inr (TranscriptAuthParts.absSlice bytes)))))).run before).run previous) := by
  exact world setup reserve length erased before previous index self control binding kernel bytes present

omit material ed in
private theorem primitives_canonical (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) :
    RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) reserve=
      RegistrationNativePlatformOrdinaryWorld.primitives setup (ledgerCodec wire) reserve := by
  funext query
  rcases query with kdf | (sealed | (opened | (hashed | written)))
  all_goals rfl

omit material ed in
theorem beacon_canonical (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E)) (index : Nat) (bytes : Pqxdh.Bytes) :
    RegistrationNativePlatformOrdinaryWorld.beaconStep (n:=n) setup
        (ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) reserve index (.inr bytes)=
      RegistrationNativePlatformOrdinaryWorld.beaconStep setup (ledgerCodec wire) reserve index (.inr bytes) := by
  funext before
  unfold RegistrationNativePlatformOrdinaryWorld.beaconStep
  rw [primitives_canonical]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld.guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld.guarded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld.beacon_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveWorld.beacon_canonical
