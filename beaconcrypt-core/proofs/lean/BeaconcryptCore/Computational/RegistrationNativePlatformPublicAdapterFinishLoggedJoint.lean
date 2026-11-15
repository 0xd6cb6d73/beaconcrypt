-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedWire
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedRuntime
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage)
variable {n :Nat} {I KemSK P E R Error Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=mlSource) setup checks)
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "wire"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire
open RegistrationNativePlatformExtractedSdkPublic (returned returned_exact store)
open RegistrationNativePlatformSdkReification (backend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterDispatcherCore (Private physical)

noncomputable def active (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.InitSent pending prekey oneTime kem) (input :Slice U8)
    (owner :RegistrationNativeBeaconFrontend.Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (index :Nat) (selected :before.beacons[index]?=some owner)
    (phase :owner.phase=.initSent pending scalar) (previous :P)
    (objects :Private configuration created credential (before,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (note :Stage→Log) (past :List Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
        configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar before index selected phase
        previous objects sourceSelected) (List Log) where
  sample:=RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks configuration.agreement.representation created
    pending (AdapterPublicFinishLifetime.packet input) owner scalar before previous past
  erase:=RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample_erase setup wire note coins checks configuration.agreement.representation created
    pending (AdapterPublicFinishLifetime.packet input) owner scalar before previous past

omit [FrameDispatchFallback.Operations] in
theorem active_source (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.InitSent pending prekey oneTime kem) (input :Slice U8)
    (owner :RegistrationNativeBeaconFrontend.Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (index :Nat) (selected :before.beacons[index]?=some owner)
    (phase :owner.phase=.initSent pending scalar) (previous :P)
    (objects :Private configuration created credential (before,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (note :Stage→Log) (past :List Log) :
    RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project self pending <$>
      (active configuration created credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected note past).sample=
      RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.body configuration created note self input
        (erase (backend before),(previous,past)) :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformSdkFinishSampling.uniformP coins) originalCrypto
  have prior:=objects.base.beacons index
  rw [selected] at prior
  obtain ⟨actual,found,related⟩:=prior
  have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
  subst actual
  rw [show (active configuration created credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected note past).sample=
    RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks configuration.agreement.representation created
      pending (AdapterPublicFinishLifetime.packet input) owner scalar before previous past from rfl,
    RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project_run]
  have law:=RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.active coins setup checks configuration.agreement.representation created wire
    note configuration.erased configuration.parseEd configuration.verifyEd writer configuration.view (RegistrationNativePlatformPublicAdapterConfiguration.common configuration) configuration.decapsulation self pending prekey oneTime kem
    stored input owner scalar before related phase previous past
  have writers:=RegistrationNativePlatformPublicAdapterFinishLoggedWire.program (m:=PhysicalM) setup wire RegistrationNativeConcreteCodec.wire
    (RegistrationNativePlatformSdkFinishPhysicalBody.trusted (n:=n) coins setup checks configuration.agreement.representation created) note configuration.view
    (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup configuration.view (RegistrationNativePlatformPublicAdapterConfiguration.common configuration)) self input
  have actualCanonical:=RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.source (m:=PhysicalM) setup wire
    (RegistrationNativePlatformSdkFinishPhysicalBody.trusted (n:=n) coins setup checks configuration.agreement.representation created) note configuration.view
    (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup configuration.view (RegistrationNativePlatformPublicAdapterConfiguration.common configuration))
    configuration.erased (fun input=>StateT.lift (configuration.parseEd input)) (fun input key=>StateT.lift (configuration.verifyEd input key))
    (fun query=>StateT.lift (writer query)) self input
  have actualConcrete:=RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.source (m:=PhysicalM) setup RegistrationNativeConcreteCodec.wire
    (RegistrationNativePlatformSdkFinishPhysicalBody.trusted (n:=n) coins setup checks configuration.agreement.representation created) note configuration.view
    (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup configuration.view (RegistrationNativePlatformPublicAdapterConfiguration.common configuration))
    configuration.erased (fun input=>StateT.lift (configuration.parseEd input)) (fun input key=>StateT.lift (configuration.verifyEd input key))
    (fun query=>StateT.lift (writer query)) self input
  have observedWire:=actualCanonical.trans (writers.trans actualConcrete.symm)
  have projected:=congrArg (fun program=>(fun result=>((result.1.1.1,result.1.2),(result.2,result.1.1.2))) <$>
    (((program.run past).run (erase (backend before))).run previous)) observedWire
  exact law.trans projected

noncomputable def physicalLog (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    (current :Native×P) (objects :Private configuration created credential current) (log :List Log) :Store n KemSK R (P×List Log) :=
  let base:=physical configuration created credential current objects
  {base with backend:=(base.backend.1,(base.backend.2,log))}

noncomputable def output (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :RegistrationNativePlatformExtractedSdkPublic.TotalStep (Private configuration created credential) target)
    (augmented :RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation call (List Log)) :
    ProbComp (RustM (Option Pqxdh.Bytes×Store n KemSK R (P×List Log))×(Backend n KemSK×(P×List Log))) :=
  (fun packet=>
    let old:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
    let next:=physicalLog configuration created credential (call.step.native old.val).2 (store call old) packet.val.2
    (.ok (RegistrationNativeRawAdapter.resultOption (call.observe (returned call old)),next),next.backend)) <$>
      PFunctor.FreeM.attachSupp augmented.sample

omit [FrameDispatchFallback.Operations] in
theorem active_query (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential mlSource)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (prekey oneTime :beaconcrypt_crypto.crypto_kx.KeyPair) (kem :beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored :self.state=.InitSent pending prekey oneTime kem) (input :Slice U8)
    (owner :RegistrationNativeBeaconFrontend.Owner mlSource) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :Native) (index :Nat) (selected :before.beacons[index]?=some owner)
    (phase :owner.phase=.initSent pending scalar) (previous :P)
    (objects :Private configuration created credential (before,previous))
    (sourceSelected :objects.base.objects.beacons index=some self) (note :Stage→Log) (past :List Log) :
    output configuration created credential
      (RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
        configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar before index selected phase
        previous objects sourceSelected)
      (active configuration created credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected note past)=
      RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run configuration created note
        (physicalLog configuration created credential (before,previous) objects past) index input :=by
  let call:=RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
    configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected
  let augmented:=active configuration created credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected note past
  let finish:=fun reached=>Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id
    (RegistrationNativePlatformSdkFinishPhysical.finish (physicalLog configuration created credential (before,previous) objects past) index reached)
  have point (packet :{value //value∈support augmented.sample}) :
      (let old:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
       let next:=physicalLog configuration created credential (call.step.native old.val).2 (store call old) packet.val.2
       (.ok (RegistrationNativeRawAdapter.resultOption (call.observe (returned call old)),next),next.backend))=
      finish (RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project self pending packet.val) :=by
    let old:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
    have normal:=returned_exact call old
    change (RegistrationNativePlatformExtractedSdkFinish.sourceProjection self pending packet.val.1.1).1=.ok (returned call old) at normal
    have kept:=RegistrationNativePlatformSdkFinishPhysical.active_objects coins setup checks configuration.agreement.representation created wire
      configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected old
    change (RustM.ok (RegistrationNativeRawAdapter.resultOption (call.observe (returned call old)),
      physicalLog configuration created credential _ (store call old) packet.val.2),
      (physicalLog configuration created credential _ (store call old) packet.val.2).backend)=_
    unfold physicalLog physical
    rw [kept,RegistrationNativePlatformPublicAdapterStore.finish_update,
      RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_beacon]
    dsimp only [finish,RegistrationNativePlatformSdkFinishPhysical.finish,
      RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project]
    erw [normal]
    rfl
  have joint:=active_source configuration created credential self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected note past
  calc
    _=(fun packet :{value //value∈support augmented.sample}=>finish (RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project self pending packet.val)) <$>
      PFunctor.FreeM.attachSupp augmented.sample :=by
      unfold output
      congr 1
      funext packet
      exact point packet
    _=finish <$> (RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project self pending <$>augmented.sample) :=by
      rw [Functor.map_map]
      have erased:=congrArg (fun action=>(fun packet=>finish (RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project self pending packet)) <$>action)
        (PFunctor.FreeM.map_attachSupp augmented.sample)
      simp only [Functor.map_map] at erased
      exact erased
    _=_ :=by
      rw [joint]
      unfold RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run
      change _=(match objects.base.objects.beacons index with | none=>_ | some value=>_)
      rw [sourceSelected]
      simp only [Functor.map_map]
      change _=finish <$>RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.body configuration created note self input
        (physicalLog configuration created credential (before,previous) objects past).backend
      rw [show (physicalLog configuration created credential (before,previous) objects past).backend=
        (erase (backend before),(previous,past)) from by
        change (erase (RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects).backend.1,
          ((RegistrationNativePlatformPublicAdapterStore.erase objects.base.objects).backend.2,past))=_
        rw [RegistrationNativePlatformPublicAdapterStore.retained configuration.view configuration.views setup.joint created credential (before,previous) objects.base]
        rfl]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active_query
