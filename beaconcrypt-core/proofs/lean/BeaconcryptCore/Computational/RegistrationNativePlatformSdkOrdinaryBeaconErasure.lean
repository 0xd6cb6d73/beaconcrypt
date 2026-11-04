-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconMissing
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (ledgerCodec)
open RegistrationNativePlatformSdkStrongCarrier (StrongCarrier)
variable {n : Nat} {Platform E I KemSK R : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw strongPhysical)
open RegistrationNativePlatformPublicAdapterStore (erase)
omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion keyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) :
    raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send setup reserve length keyView converted failure erased route view views created credential current before logical bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send setup reserve keyView failure erased (erase before.base.objects) logical bytes :=by
  cases selected:current.1.beacons[logical]? with
  | none=>
      have callEq : RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send setup reserve length keyView converted failure erased route view views created credential current before logical bytes=
          RegistrationNativePlatformSdkOrdinaryBeaconMissing.send setup RegistrationNativeConcreteCodec.wire reserve route view views created credential current before logical (TranscriptAuthParts.absSlice bytes) selected :=by
        unfold RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send
        exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
          (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected)
      calc
        _=raw (strongPhysical setup view views created credential)
            (RegistrationNativePlatformSdkOrdinaryBeaconMissing.send setup RegistrationNativeConcreteCodec.wire reserve route view views created credential current before logical (TranscriptAuthParts.absSlice bytes) selected) :=
          congrArg (raw (strongPhysical setup view views created credential)) callEq
        _=pure (.ok (none,erase before.base.objects),(erase before.base.objects).backend) :=
          RegistrationNativePlatformSdkOrdinaryBeaconSelected.missing_send setup RegistrationNativeConcreteCodec.wire reserve route view views created credential current before logical (TranscriptAuthParts.absSlice bytes) selected
        _=_ :=by
          have absent:=before.base.beacons logical
          rw [selected] at absent
          unfold RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send
          change _=(match before.base.objects.beacons logical with
            | none=>_
            | some object=>_)
          rw [absent]
  | some owner=>
      have found:=before.base.beacons logical
      rw [selected] at found
      let self:=Classical.choose found
      have sourceSelected:before.base.objects.beacons logical=some self := (Classical.choose_spec found).1
      have related:= (Classical.choose_spec found).2
      have address:=before.base.indexed logical owner selected
      have sourceLaw:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.send_source setup reserve keyView failure erased view views created credential
        current before.base logical owner selected self sourceSelected bytes
      cases stored:self.state
      case Established control binding manager=>
        have active:=RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related control binding manager stored
        let kernel:=Classical.choose active
        let completed:=Classical.choose (Classical.choose_spec active)
        have actual:=Classical.choose_spec (Classical.choose_spec active)
        have normalized : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel) :=stored.trans (congrArg _ actual.1)
        have callEq : RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send setup reserve length keyView converted failure erased route view views created credential current before logical bytes=RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views created credential current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes :=by
          unfold RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send
          exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
            ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
              ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
                (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
        calc
          _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views created credential current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes) :=
            congrArg (raw (strongPhysical setup view views created credential)) callEq
          _=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>(RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views created credential current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes).step.sourceCall :=by
            unfold RegistrationNativePlatformSdkOrdinaryBeaconStrongSteps.active_send
            exact (RegistrationNativePlatformSdkOrdinaryBeaconSelected.of_base setup view views created credential _ _).trans
              (RegistrationNativePlatformSdkOrdinaryBeaconSelected.active_send setup RegistrationNativeConcreteCodec.wire reserve length keyView converted failure erased route view views created credential
                current before.base logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes)
          _=_ :=by
            change RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>
              (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self <$>
                RegistrationNativePlatformExtractedSdkOrdinary.run
                  (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes)
                  current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) false)=_
            rw [address]
            exact sourceLaw.symm
      all_goals
        have idle : AdapterPublicOrdinaryBeacon.Inactive self :=by simp only [AdapterPublicOrdinaryBeacon.Inactive,stored]
        have dormant:=RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial.inactive view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related idle
        let tag:=Classical.choose dormant
        have callEq : RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send setup reserve length keyView converted failure erased route view views created credential current before logical bytes=RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle :=by
          unfold RegistrationNativePlatformSdkOrdinaryBeaconDispatch.send
          first
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
        calc
          _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle) :=
            congrArg (raw (strongPhysical setup view views created credential)) callEq
          _=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>(RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.send setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle).step.sourceCall :=
            RegistrationNativePlatformSdkOrdinaryBeaconSelected.idle_send setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential
              current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle sourceSelected
          _=_ :=by
            change RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryDriver.sendReply <$>
              (RegistrationNativePlatformExtractedSdkOrdinaryBeaconSendRun.observed owner.worldOwner self <$>
                RegistrationNativePlatformExtractedSdkOrdinary.run
                  (RegistrationNativePlatformExtractedSdkOrdinary.beaconSend setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes)
                  current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) false)=_
            rw [address]
            exact sourceLaw.symm

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive (setup : Setup base KemSK)
    (reserve : Nat→StateT Platform ProbComp (core.result.Result Unit E))
    (length : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (keyView : RegistrationNativePlatformSourceSeal.KeyView)
    (failure : primitives.Error) (erased : commitment.CommitmentTranscript) (route : RawCtxServerRouting.SenderDecoder)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native×Platform) (before : StrongCarrier (R:=R) setup view views created credential current)
    (logical : Nat) (bytes : Slice U8) :
    raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive setup reserve length keyView failure erased route view views created credential current before logical bytes)=
      RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive setup reserve keyView failure erased (erase before.base.objects) logical bytes :=by
  cases selected:current.1.beacons[logical]? with
  | none=>
      have callEq : RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive setup reserve length keyView failure erased route view views created credential current before logical bytes=
          RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive setup RegistrationNativeConcreteCodec.wire reserve route view views created credential current before logical (TranscriptAuthParts.absSlice bytes) selected :=by
        unfold RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive
        exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
          (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected)
      calc
        _=raw (strongPhysical setup view views created credential)
            (RegistrationNativePlatformSdkOrdinaryBeaconMissing.receive setup RegistrationNativeConcreteCodec.wire reserve route view views created credential current before logical (TranscriptAuthParts.absSlice bytes) selected) :=
          congrArg (raw (strongPhysical setup view views created credential)) callEq
        _=pure (.ok (none,erase before.base.objects),(erase before.base.objects).backend) :=
          RegistrationNativePlatformSdkOrdinaryBeaconSelected.missing_receive setup RegistrationNativeConcreteCodec.wire reserve route view views created credential current before logical (TranscriptAuthParts.absSlice bytes) selected
        _=_ :=by
          have absent:=before.base.beacons logical
          rw [selected] at absent
          unfold RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive
          change _=(match before.base.objects.beacons logical with
            | none=>_
            | some object=>_)
          rw [absent]
  | some owner=>
      have found:=before.base.beacons logical
      rw [selected] at found
      let self:=Classical.choose found
      have sourceSelected:before.base.objects.beacons logical=some self := (Classical.choose_spec found).1
      have related:= (Classical.choose_spec found).2
      have address:=before.base.indexed logical owner selected
      have sourceLaw:=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.receive_source setup reserve keyView failure erased view views created credential
        current before.base logical owner selected self sourceSelected bytes
      cases stored:self.state
      case Established control binding manager=>
        have active:=RegistrationNativePlatformSdkOrdinaryBeaconMaterial.established view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related control binding manager stored
        let kernel:=Classical.choose active
        let completed:=Classical.choose (Classical.choose_spec active)
        have actual:=Classical.choose_spec (Classical.choose_spec active)
        have normalized : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel) :=stored.trans (congrArg _ actual.1)
        have callEq : RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive setup reserve length keyView failure erased route view views created credential current before logical bytes=RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps.active_receive setup reserve length keyView failure erased route view views created credential current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes :=by
          unfold RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive
          exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
            ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
              ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
                (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
        calc
          _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps.active_receive setup reserve length keyView failure erased route view views created credential current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes) :=
            congrArg (raw (strongPhysical setup view views created credential)) callEq
          _=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>(RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps.active_receive setup reserve length keyView failure erased route view views created credential current before logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes).step.sourceCall :=by
            unfold RegistrationNativePlatformSdkOrdinaryBeaconReceiveStrongSteps.active_receive
            exact (RegistrationNativePlatformSdkOrdinaryBeaconSelected.of_base setup view views created credential _ _).trans
              (RegistrationNativePlatformSdkOrdinaryBeaconSelected.active_receive setup reserve length keyView failure erased route view views created credential
                current before.base logical owner selected self sourceSelected control binding kernel normalized completed actual.2.1 actual.2.2 bytes)
          _=_ :=by
            change RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>
              (RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveRun.observed owner.worldOwner self <$>
                RegistrationNativePlatformExtractedSdkOrdinary.run
                  (RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes)
                  current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) true)=_
            rw [address]
            exact sourceLaw.symm
      all_goals
        have idle : AdapterPublicOrdinaryBeacon.Inactive self :=by simp only [AdapterPublicOrdinaryBeacon.Inactive,stored]
        have dormant:=RegistrationNativePlatformSdkOrdinaryBeaconInactiveMaterial.inactive view setup.joint current.1.pool self owner
          current.1.server.world.world.1.owners[owner.worldOwner]? related idle
        let tag:=Classical.choose dormant
        have callEq : RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive setup reserve length keyView failure erased route view views created credential current before logical bytes=RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle :=by
          unfold RegistrationNativePlatformSdkOrdinaryBeaconDispatch.receive
          first
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
            | exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
                ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
                  ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ _ stored).trans
                    (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored)))
        calc
          _=raw (strongPhysical setup view views created credential) (RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle) :=
            congrArg (raw (strongPhysical setup view views created credential)) callEq
          _=RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>(RegistrationNativePlatformSdkOrdinaryBeaconIdleSteps.receive setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle).step.sourceCall :=
            RegistrationNativePlatformSdkOrdinaryBeaconSelected.idle_receive setup RegistrationNativeConcreteCodec.wire reserve route keyView failure erased view views created credential
              current before logical bytes owner selected tag (Classical.choose_spec dormant) self idle sourceSelected
          _=_ :=by
            change RegistrationNativePlatformExtractedSdkOrdinaryBeaconPhysical.update (erase before.base.objects) logical RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.receiveReply <$>
              (RegistrationNativePlatformExtractedSdkOrdinaryBeaconReceiveRun.observed owner.worldOwner self <$>
                RegistrationNativePlatformExtractedSdkOrdinary.run
                  (RegistrationNativePlatformExtractedSdkOrdinary.beaconReceive setup (ledgerCodec RegistrationNativeConcreteCodec.wire) reserve keyView failure erased self bytes)
                  current.1 current.2 (current.1.server.world.world.1.ownerRaw owner.worldOwner) true)=_
            rw [address]
            exact sourceLaw.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure.receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconErasure.receive
