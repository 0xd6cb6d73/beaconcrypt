-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStepSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
/-! The actual Bundle driver reads only the stored source Self, caller RNG and physical backend. Returned source words update the same object and RNG; Rust failures retain the actual terminal backend without manufacturing a returned Self. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterStore (Store erase bundle)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw strongPhysical)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep returned store)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK E P R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
abbrev Word (R : Type) := core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R

def optionBytes (word : Word R) : Option Pqxdh.Bytes :=
  match word.1 with | .None=>none | .Some bytes=>some (TranscriptAuthParts.absSlice bytes)

def finish (before : Store n KemSK R P) (index : Nat) (result : RustM (Word R) ×(Backend n KemSK ×P)) :
    RustM (Option Pqxdh.Bytes ×Store n KemSK R P) ×(Backend n KemSK ×P) :=
  match result.1 with
  | .fail error=>(.fail error,result.2)
  | .div=>(.div,result.2)
  | .ok word=>(.ok (optionBytes word,bundle before index word result.2),result.2)

variable [original : CryptoOperations (RustT ProbComp)]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (physicalLocal : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (failure : ed.Error) (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (physicalChildren : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))

noncomputable def call {Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (before : Store n KemSK R P) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) :=
  finish before index <$> ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
    ((RegistrationNativePlatformPublicAdapterBundleSource.call coins setup checks representation created view physicalLocal
      (RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created) original)
      failure writer physicalChildren generator self before.rng).run before.backend.1).run before.backend.2)

noncomputable def run {Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (before : Store n KemSK R P) (index : Nat) :
    ProbComp (RustM (Option Pqxdh.Bytes ×Store n KemSK R P) ×(Backend n KemSK ×P)) :=
  match before.beacons index with
  | none=>pure (.ok (none,before),before.backend)
  | some self=>call coins setup checks representation created view physicalLocal failure writer physicalChildren generator before index self

omit original material platform ed in
private theorem source_eq {N Reply S : Type} {Private : N→Type} {model : ProbComp (Reply×N)}
    (step : TotalStep Private model) (first : {packet //packet∈support step.step.sample}→S)
    (update : RustM step.step.sourceType×N→S)
    (retained : ∀packet,first packet=update (step.step.sourceReply packet.val,step.step.sourceState packet.val)) :
    first <$>PFunctor.FreeM.attachSupp step.step.sample=update <$>step.step.sourceCall :=by
  rw [←step.step.source_exact,Functor.map_map]
  have erased:=congrArg (fun work=>(fun packet=>update (step.step.sourceReply packet,step.step.sourceState packet)) <$>work)
    (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase step.step.sample)
  simp only [Functor.map_map] at erased
  rw [←erased]
  congr 1
  funext packet
  exact retained packet

omit original in
private theorem active_raw (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source ×P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (index : Nat) {model : ProbComp (RustM (Option Pqxdh.Bytes) ×(RegistrationNativeExperiment.State n KemSK source ×P))}
    (step : TotalStep (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential) model)
    (decode : step.step.sourceType →Word R)
    (observed : ∀word,step.observe word=RegistrationNativePlatformExtractedSdkAdaptiveBundle.bytes (.ok (decode word)))
    (kept : ∀packet,(store step packet).base.objects=RegistrationNativePlatformExtractedSdkCarrierBundle.update objects.base.objects index
      (decode (returned step packet)) (step.step.sourceState packet.val)) :
    raw (strongPhysical setup view views created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption step)=
      (fun result=>finish (erase objects.base.objects) index (decode <$>result.1,RegistrationNativePlatformSdkReification.persistent result.2)) <$>step.step.sourceCall :=by
  unfold raw
  apply source_eq step
  intro packet
  change (RustM.ok (RegistrationNativeRawAdapter.resultOption (step.observe (returned step packet)),erase (store step packet).base.objects),
    (erase (store step packet).base.objects).backend)=_
  rw [kept packet,RegistrationNativePlatformPublicAdapterStore.bundle_update,RegistrationNativePlatformExtractedSdkPublic.returned_exact step packet,observed]
  rfl

local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "CutM"=>StateT (RegistrationNativePlatformCutJournal.State Native) (StateT P ProbComp)
variable (previousLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp))))
variable (reservePackets : Usize →StateT P ProbComp (core.result.Result Unit E))
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
variable (other : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp)))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) (StateT P ProbComp)))
variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)
local notation "packetWriter"=>RegistrationNativePlatformConcreteSource.writer reservePackets
theorem with_coins {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (stored : self.state=.FreshWithCoins control prekey oneTime kem) (phase : owner.phase=.freshWithCoins scalar)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner)
    (physicalLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))))
    (physicalChildren : ChildOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp)))) :
    let step:=RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
    raw (strongPhysical setup view containersView created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption step)=
      call coins setup checks representation created view physicalLocal failure packetWriter physicalChildren generator (erase objects.base.objects) index self :=by
  let step:=RegistrationNativePlatformPublicAdapterBundleStepSource.withCoins previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
  have objectsLaw:=RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_objects previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected
  have sourceLaw:=RegistrationNativePlatformPublicAdapterBundleStepSource.with_coins_source previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control scalar prekey oneTime kem generator stored phase before previous objects sourceSelected selected physicalLocal physicalChildren
  dsimp only
  rw [active_raw setup created view containersView credential (before.1,previous) objects index step id (fun _=>rfl) objectsLaw]
  have physical: (erase objects.base.objects).backend=(RegistrationNativePlatformSdkReification.backend before.1,previous):=objects.base.backend
  unfold call
  rw [physical]
  have mapped:=congrArg (fun tree=>finish (erase objects.base.objects) index <$>tree) sourceLaw
  simpa only [step,RegistrationNativePlatformPublicAdapterStore.erase,Functor.map_map,Prod.map,id_eq,id_map,Function.comp_def] using mapped
theorem fresh {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar=>PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (stored : self.state=.Fresh control prekey kem) (phase : owner.phase=.fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before.1,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) (selected : before.1.beacons[index]?=some owner)
    (physicalLocal : LocalOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp))))
    (physicalChildren : ChildOperations (RustT (StateT (RegistrationNativePlatformSdkReification.Backend n KemSK) (StateT P ProbComp)))) :
    let step:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control prekey kem generator contract stored phase before previous objects sourceSelected selected
    raw (strongPhysical setup view containersView created credential)
      (RegistrationNativePlatformPublicAdapterReply.map RegistrationNativeRawAdapter.resultOption step)=
      call coins setup checks representation created view physicalLocal failure packetWriter physicalChildren generator (erase objects.base.objects) index self :=by
  let step:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control prekey kem generator contract stored phase before previous objects sourceSelected selected
  have objectsLaw:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_objects previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control prekey kem generator contract stored phase before previous objects sourceSelected selected
  have sourceLaw:=RegistrationNativePlatformPublicAdapterBundleStepSource.fresh_source previousLocal coins setup checks representation created reservePackets index owner failure other recording containersView credential
      self view control prekey kem generator contract stored phase before previous objects sourceSelected selected physicalLocal physicalChildren
  dsimp only
  rw [active_raw setup created view containersView credential (before.1,previous) objects index step id (fun _=>rfl) objectsLaw]
  have physical: (erase objects.base.objects).backend=(RegistrationNativePlatformSdkReification.backend before.1,previous):=objects.base.backend
  unfold call
  rw [physical]
  have mapped:=congrArg (fun tree=>finish (erase objects.base.objects) index <$>tree) sourceLaw
  simpa only [step,RegistrationNativePlatformPublicAdapterStore.erase,Functor.map_map,Prod.map,id_eq,id_map,Function.comp_def] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical.with_coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical.fresh
