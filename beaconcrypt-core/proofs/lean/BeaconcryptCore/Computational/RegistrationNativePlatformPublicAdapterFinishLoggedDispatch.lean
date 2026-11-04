-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredFinish
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch
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

open RegistrationNativePlatformPublicAdapterLoggedRuntime (Augmentation unchanged)
open RegistrationNativePlatformPublicAdapterFinishLoggedJoint (output physicalLog)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)

variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential mlSource)

noncomputable def transport {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    {left right :TotalStep (Private configuration created credential) target}
    (same :left=right) (augmented :Augmentation left (List Log)) :Augmentation right (List Log):=same ▸augmented

noncomputable def augmentation (current :Native×P) (objects :Private configuration created credential current)
    (index :Nat) (input :Slice U8) (note :Stage→Log) (past :List Log) :
    Augmentation (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) (List Log) :=by
  cases selected:current.1.beacons[index]? with
  | none=>exact unchanged _ past
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec prior).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint current.1.pool self owner
      current.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec prior).2
    cases stored:self.state with
    | InitSent pending prekey oneTime kem=>
      have phase :∃scalar,owner.phase=.initSent pending scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        cases matched.1
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.initSent pending scalar:=Classical.choose_spec phase
      have callEq:RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input=
          RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
            configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar current.1 index selected phase current.2 objects sourceSelected :=by
        unfold RegistrationNativePlatformPublicAdapterConfiguredFinish.typed RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      exact transport configuration created credential callEq.symm
        (RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active configuration created credential self pending prekey oneTime kem stored input owner scalar
          current.1 index selected phase current.2 objects sourceSelected note past)
    | _=>exact unchanged _ past

omit [FrameDispatchFallback.Operations] [PublicWrapperPlatform.CryptoOperations] in
theorem transport_output {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    {left right :TotalStep (Private configuration created credential) target}
    (same :left=right) (augmented :Augmentation left (List Log)) :
    output configuration created credential right (transport configuration created credential same augmented)=
      output configuration created credential left augmented :=by
  cases same
  rfl

def carryStore (past :List Log) (before :Store n KemSK R P) :Store n KemSK R (P×List Log) :=
  {before with backend:=(before.backend.1,(before.backend.2,past))}

def carryRaw (past :List Log) (reached :RustM (Option Pqxdh.Bytes×Store n KemSK R P)×(Backend n KemSK×P)) :
    RustM (Option Pqxdh.Bytes×Store n KemSK R (P×List Log))×(Backend n KemSK×(P×List Log)) :=
  (Prod.map id (carryStore past) <$>reached.1,(reached.2.1,(reached.2.2,past)))

omit [FrameDispatchFallback.Operations] [PublicWrapperPlatform.CryptoOperations] in
theorem unchanged_output {target :ProbComp (RustM (Option Pqxdh.Bytes)×(Native×P))}
    (call :TotalStep (Private configuration created credential) target) (past :List Log) :
    output configuration created credential call (unchanged call past)=
      carryRaw past <$> ((Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id) <$>
        RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical configuration created credential) call) :=by
  unfold output RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
  rw [←RegistrationNativePlatformPublicAdapterLoggedRuntime.project_sample call (unchanged call past),Functor.map_map,Functor.map_map,Functor.map_map]
  congr 1
  funext packet
  rw [RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log]
  rfl

omit [FrameDispatchFallback.Operations] in
theorem body_idle (note :Stage→Log) (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8)
    (idle :RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state) (before :Backend n KemSK×(P×List Log)) :
    RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.body configuration created note self input before=
      pure ((.ok (.None,self),before.1),before.2) :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.body RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.run
    AdapterPublicFinishObservedRequest.run
  cases state:self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control=>rfl
  | InitSent pending prekey oneTime kem=>simp only [state,RegistrationNativePlatformExtractedSdkIdle.FinishIdle] at idle

omit [FrameDispatchFallback.Operations] in
theorem source_idle (before :Store n KemSK R P) (index :Nat) (self :beaconcrypt_public_wrapper.beacon.Beacon)
    (found :before.beacons index=some self) (input :Slice U8) (note :Stage→Log) (past :List Log)
    (idle :RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state) :
    RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run configuration created note (carryStore past before) index input=
      carryRaw past <$>RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created before index input :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall RegistrationNativePlatformSdkFinishPhysical.source
  simp only [carryStore,found]
  rw [body_idle configuration created note self input idle,
    RegistrationNativePlatformSdkFinishPhysical.body_idle coins setup checks configuration.agreement.representation created configuration.erased
      configuration.parseEd configuration.verifyEd writer self input idle]
  simp only [StateT.run_pure,map_pure]
  rfl

omit [FrameDispatchFallback.Operations] [PublicWrapperPlatform.CryptoOperations] primitives
  [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
  [AdapterPublicOrdinaryPlatform.LookupOperations] originalGenerators originalCrypto originalLocal originalContainers in
private theorem raw_map {N Reply PublicReply :Type} {Private :N→Type} {target :ProbComp (Reply×N)}
    (call :TotalStep Private target) (physical :∀current,Private current→Store n KemSK R P)
    (observe :Reply→PublicReply) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (RegistrationNativePlatformPublicAdapterReply.map observe call)=
      (Prod.map (Functor.map (Prod.map observe id)) id) <$>RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical call :=by
  unfold RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw
  conv_rhs=>erw [Functor.map_map]
  rfl

theorem plain_query (current :Native×P) (objects :Private configuration created credential current) (index :Nat) (input :Slice U8) :
    (Prod.map (Functor.map (Prod.map RegistrationNativeRawAdapter.resultOption id)) id) <$>
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw (physical configuration created credential)
        (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input)=
      RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created (physical configuration created credential current objects) index input :=by
  have law:=RegistrationNativePlatformPublicAdapterConfiguredFinish.query configuration created credential current objects index input
  unfold RegistrationNativePlatformPublicAdapterConfiguredFinish.step at law
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast,raw_map] at law
  exact law

omit [FrameDispatchFallback.Operations] in
theorem source_missing (before :Store n KemSK R P) (index :Nat) (input :Slice U8)
    (found :before.beacons index=none) (note :Stage→Log) (past :List Log) :
    RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run configuration created note (carryStore past before) index input=
      carryRaw past <$>RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall configuration created before index input :=by
  unfold RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run RegistrationNativePlatformPublicAdapterConfiguredFinish.sourceCall RegistrationNativePlatformSdkFinishPhysical.source
  simp only [carryStore,found,map_pure]
  rfl

theorem query (current :Native×P) (objects :Private configuration created credential current)
    (index :Nat) (input :Slice U8) (note :Stage→Log) (past :List Log) :
    output configuration created credential (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input)
      (augmentation configuration created credential current objects index input note past)=
      RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run configuration created note
        (physicalLog configuration created credential current objects past) index input :=by
  cases selected:current.1.beacons[index]? with
  | none=>
    have absent:=objects.base.beacons index
    rw [selected] at absent
    have augEq:augmentation configuration created credential current objects index input note past=
      unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
      unfold augmentation
      exact (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
        ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans (by rfl))
    rw [augEq,unchanged_output,plain_query]
    exact (source_missing configuration created (physical configuration created credential current objects) index input absent note past).symm
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected :objects.base.objects.beacons index=some self:=(Classical.choose_spec prior).1
    have related :AdapterPublicWrapperState.Beacon configuration.view setup.joint current.1.pool self owner
      current.1.server.world.world.1.owners[owner.worldOwner]? :=(Classical.choose_spec prior).2
    cases stored:self.state with
    | InitSent pending prekey oneTime kem=>
      have phase :∃scalar,owner.phase=.initSent pending scalar :=by
        have matched:=related.phase
        cases phaseEq:owner.phase <;>simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        cases matched.1
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.initSent pending scalar:=Classical.choose_spec phase
      have callEq:RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input=
          RegistrationNativePlatformSdkFinishCoupled.active coins setup checks configuration.agreement.representation created wire
            configuration.view configuration.views credential self pending prekey oneTime kem stored input owner scalar current.1 index selected phase current.2 objects sourceSelected :=by
        unfold RegistrationNativePlatformPublicAdapterConfiguredFinish.typed RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      have augEq:augmentation configuration created credential current objects index input note past=
          transport configuration created credential callEq.symm
            (RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active configuration created credential self pending prekey oneTime kem stored input owner scalar
              current.1 index selected phase current.2 objects sourceSelected note past) :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,transport_output]
      exact RegistrationNativePlatformPublicAdapterFinishLoggedJoint.active_query configuration created credential self pending prekey oneTime kem stored input owner scalar
        current.1 index selected phase current.2 objects sourceSelected note past
    | Fresh control prekey kem=>
      have idle:RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state:=by rw [stored];trivial
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,unchanged_output,plain_query]
      exact (source_idle configuration created (physical configuration created credential current objects) index self sourceSelected input note past idle).symm
    | FreshWithCoins control prekey oneTime kem=>
      have idle:RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state:=by rw [stored];trivial
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,unchanged_output,plain_query]
      exact (source_idle configuration created (physical configuration created credential current objects) index self sourceSelected input note past idle).symm
    | Established control binding manager=>
      have idle:RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state:=by rw [stored];trivial
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,unchanged_output,plain_query]
      exact (source_idle configuration created (physical configuration created credential current objects) index self sourceSelected input note past idle).symm
    | Aborted control=>
      have idle:RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state:=by rw [stored];trivial
      have augEq:augmentation configuration created credential current objects index input note past=
          unchanged (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input) past :=by
        unfold augmentation
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      rw [augEq,unchanged_output,plain_query]
      exact (source_idle configuration created (physical configuration created credential current objects) index self sourceSelected input note past idle).symm

noncomputable def stepAugmentation (current :Native×P) (objects :Private configuration created credential current)
    (index :Nat) (input :Slice U8) (note :Stage→Log) (past :List Log) :
    Augmentation (RegistrationNativePlatformPublicAdapterConfiguredFinish.step configuration created credential current objects index input) (List Log) where
  sample:=(augmentation configuration created credential current objects index input note past).sample
  erase:=(augmentation configuration created credential current objects index input note past).erase

noncomputable def publicOutput {target :ProbComp (Option Pqxdh.Bytes×(Native×P))}
    (call :TotalStep (Private configuration created credential) target) (augmented :Augmentation call (List Log)) :
    ProbComp (RustM (Option Pqxdh.Bytes×Store n KemSK R (P×List Log))×(Backend n KemSK×(P×List Log))) :=
  (fun packet=>
    let old:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
    let next:=physicalLog configuration created credential (call.step.native old.val).2 (store call old) packet.val.2
    (.ok (call.observe (returned call old),next),next.backend)) <$>
      PFunctor.FreeM.attachSupp augmented.sample

theorem step_query (current :Native×P) (objects :Private configuration created credential current)
    (index :Nat) (input :Slice U8) (note :Stage→Log) (past :List Log) :
    publicOutput configuration created credential (RegistrationNativePlatformPublicAdapterConfiguredFinish.step configuration created credential current objects index input)
      (stepAugmentation configuration created credential current objects index input note past)=
      RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.run configuration created note
        (physicalLog configuration created credential current objects past) index input :=by
  change output configuration created credential
    (RegistrationNativePlatformPublicAdapterConfiguredFinish.typed configuration created credential current objects index input)
    (augmentation configuration created credential current objects index input note past)=_
  exact query configuration created credential current objects index input note past

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.augmentation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.transport_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.transport_output

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.unchanged_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.unchanged_output

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.body_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.body_idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.source_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.source_idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.plain_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.plain_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.source_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.source_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.stepAugmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.stepAugmentation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.step_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.step_query
