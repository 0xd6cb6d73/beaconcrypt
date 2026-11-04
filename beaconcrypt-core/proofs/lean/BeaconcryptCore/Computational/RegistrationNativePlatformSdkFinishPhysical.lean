-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupledDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkDependentCases
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkBeaconStateCases
/-! Finish executes the original SDK body from its actual stored object and physical backend. Actual returned objects and Env effects determine the next source store. Source failure and divergence retain their reached terminal backend without fabricating a replacement object. The complete phase dispatcher has the same physical marginal after erasing only the private indexed KEM observation transcript. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend commitEnvironment)
open RegistrationNativePlatformPublicAdapterStore (Store erase beacon)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (persistent normalize)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw)
open RegistrationNativePlatformExtractedSdkPublic (returned returned_exact store)
open RegistrationNativePlatformExtractedSdkFinish (runner BodyResult sourceProjection)
variable {n : Nat} {I KemSK R P E : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOriginal : LocalOperations (RustT (StateT P ProbComp))]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

def finish (before : Store n KemSK R P) (index : Nat)
    (reached : (RustM AdapterPublicFinishBody.Result × Backend n KemSK) × P) :
    RustM (RustM (Option Pqxdh.Bytes) × Store n KemSK R P) × (Backend n KemSK × P) :=
  let terminal:=persistent (reached.1.2,reached.2)
  (match reached.1.1 with
  | .fail error => .fail error
  | .div => .div
  | .ok word => .ok (AdapterPublicFinishEndpoint.bytes (.ok word),beacon before index word.2 terminal),terminal)

noncomputable def source (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (before : Store n KemSK R P) (index : Nat) (input : Slice U8) :
    ProbComp (RustM (RustM (Option Pqxdh.Bytes) × Store n KemSK R P) × (Backend n KemSK × P)) :=
  match before.beacons index with
  | none => pure (.ok (.ok none,before),before.backend)
  | some self => finish before index <$>
      ((RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=mlSource) coins setup checks representation created erased
        parseEd verifyEd writer self input).run before.backend.1).run before.backend.2

noncomputable def physical (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) : Store n KemSK R P :=
  normalize (erase before.base.objects)

omit [PublicWrapperPlatform.CryptoOperations] original localOriginal in
theorem physical_backend (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (current : Native × P)
    (before : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    (physical setup view views created credential current before).backend=
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend current.1),current.2) := by
  change persistent (erase before.base.objects).backend=_
  rw [RegistrationNativePlatformPublicAdapterStore.retained view views setup.joint created credential current before.base]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] original localOriginal in
theorem active_objects (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Native) (index : Nat) (selected : before.beacons[index]?=some owner)
    (phase : owner.phase=.initSent pending scalar) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential (before,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) :
    let call:=RegistrationNativePlatformSdkFinishCoupled.active coins setup checks representation created wire view views credential
      self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected
    ∀packet : {value //value∈support call.step.sample},
      (store call packet).base.objects=
        RegistrationNativePlatformExtractedSdkCarrierFinish.update objects.base.objects index (returned call packet)
          packet.val.1.1.2 (packet.val.1.2,packet.val.2) := by
  let call:=RegistrationNativePlatformSdkFinishCoupled.active coins setup checks representation created wire view views credential
      self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected
  change ∀packet : {value //value∈support call.step.sample},
      (store call packet).base.objects=
        RegistrationNativePlatformExtractedSdkCarrierFinish.update objects.base.objects index (returned call packet)
          packet.val.1.1.2 (packet.val.1.2,packet.val.2)
  intro packet
  have normal:=returned_exact call packet
  change (sourceProjection self pending packet.val.1).1=.ok (returned call packet) at normal
  rcases packet with ⟨⟨raw,next⟩,supported⟩
  rcases raw with ⟨⟨outcome,environment⟩,native⟩
  cases outcome with
  | fail error | div =>
    dsimp only [sourceProjection,AdapterPublicFinishNormalized.output] at normal
    cases normal
  | ok completed =>
    cases completed with
    | none | some completed =>
      dsimp only [sourceProjection,AdapterPublicFinishNormalized.output] at normal
      erw [←RustM.ok.inj normal]
      rfl

theorem active (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (initial : ∀request,(localOriginal.ratchet_initial_ratchet_hkdf request).run=
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup contract.decapsulate)
    (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : RegistrationNativeBeaconFrontend.Owner mlSource) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : Native) (index : Nat) (selected : before.beacons[index]?=some owner)
    (phase : owner.phase=.initSent pending scalar) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential (before,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) :
    let call:=RegistrationNativePlatformSdkFinishCoupled.active coins setup checks representation created wire view views credential
      self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected
    raw (physical setup view views created credential) call=
      finish (physical setup view views created credential (before,previous) objects) index <$>
        ((RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=mlSource) coins setup checks representation created erased
          parseEd verifyEd writer self input).run (RegistrationNativePlatformPublicAdapterPhysicalBackend.erase (backend before))).run previous := by
  let call:=RegistrationNativePlatformSdkFinishCoupled.active coins setup checks representation created wire view views credential
      self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected
  change raw (physical setup view views created credential) call=_
  have prior:=objects.base.beacons index
  rw [selected] at prior
  obtain ⟨actual,found,related⟩:=prior
  have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
  subst actual
  have bodyLaw:=RegistrationNativePlatformSdkFinishPhysicalSource.observed coins setup checks representation created wire erased
    parseEd verifyEd writer initial view contract aligned self pending prekey oneTime kem stored input owner scalar before related phase previous
  let output:=fun reached : BodyResult n KemSK mlSource ×P =>
    finish (physical setup view views created credential (before,previous) objects) index
      (RegistrationNativePlatformSdkFinishPhysicalSource.project self pending reached)
  have point (packet : {value //value∈support call.step.sample}) :
      (let next:=physical setup view views created credential (call.step.native packet.val).2 (store call packet)
       (RustM.ok (call.observe (returned call packet),next),next.backend))=output packet.val := by
    have normal:=returned_exact call packet
    change (sourceProjection self pending packet.val.1).1=.ok (returned call packet) at normal
    have kept:=active_objects coins setup checks representation created wire view views credential self pending prekey oneTime kem stored input
      owner scalar before index selected phase previous objects sourceSelected packet
    change (RustM.ok (call.observe (returned call packet),normalize (erase (store call packet).base.objects)),
      (normalize (erase (store call packet).base.objects)).backend)=_
    rw [kept,RegistrationNativePlatformPublicAdapterStore.finish_update,
      RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize_beacon]
    dsimp only [output,finish,RegistrationNativePlatformSdkFinishPhysicalSource.project]
    erw [normal]
    rfl
  unfold raw
  calc
    _=(fun packet : {value //value∈support call.step.sample}=>output packet.val) <$>PFunctor.FreeM.attachSupp call.step.sample := by
      congr 1
      funext packet
      exact point packet
    _=output <$>call.step.sample := by
      have erasedLaw:=congrArg (fun tree=>output <$>tree) (RegistrationNativePlatformExtractedSdkAdaptive.attached_erase call.step.sample)
      simp only [Functor.map_map] at erasedLaw
      exact erasedLaw
    _=_ := by
      have mapped:=congrArg (fun tree=>finish (physical setup view views created credential (before,previous) objects) index <$>tree) bodyLaw
      simp only [Functor.map_map] at mapped
      exact mapped

 theorem body_idle (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8)
    (idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state) :
    RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=mlSource) coins setup checks representation created erased
      parseEd verifyEd writer self input =pure (.ok (.None,self)) := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
  let : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterLeaves.localOperations localOriginal
  let trusted:=RegistrationNativePlatformSdkFinishPhysicalBody.trusted (n:=n) coins setup checks representation created
  let : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication
      (RegistrationNativePlatformSdkFinishDictionaries.authentication (source:=mlSource) setup trusted)
      (fun input=>StateT.lift (parseEd input)) (fun input key=>StateT.lift (verifyEd input key)))
    (RegistrationNativePlatformSdkFinishDictionaries.recording setup trusted erased) (fun query=>StateT.lift (writer query))
  let : Codecs (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) := AdapterPublicConcreteCodecs.codecs
  unfold RegistrationNativePlatformSdkFinishPhysicalBody.body RegistrationNativePlatformSdkFinishSourceProgram.run
  exact RegistrationNativePlatformExtractedSdkIdle.finish_source self input idle

 theorem source_idle (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (before : Store n KemSK R P) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (found : before.beacons index=some self) (input : Slice U8)
    (idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state)
    (canonical : persistent before.backend=before.backend) :
    source (mlSource:=mlSource) coins setup checks representation created erased parseEd verifyEd writer before index input=
      pure (.ok (.ok none,before),before.backend) := by
  unfold source
  simp only [found]
  erw [body_idle coins setup checks representation created erased parseEd verifyEd writer self input idle]
  simp only [StateT.run_pure,map_pure]
  unfold finish
  rw [canonical]
  have unchanged : Function.update before.beacons index (some self)=before.beacons := by
    rw [←found,Function.update_eq_self]
  have same : beacon before index self before.backend=before := by
    cases before
    simp only [beacon,unchanged]
  change pure (RustM.ok (RustM.ok (none : Option Pqxdh.Bytes),beacon before index self before.backend),before.backend)=_
  rw [same]

omit material platform ed [PublicWrapperPlatform.CryptoOperations] original localOriginal in
private noncomputable def transport {N A : Type} {Private : N→Type} {left right : ProbComp (A×N)}
    (same : left=right) (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private left) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep Private right :=same ▸call

omit material platform ed [PublicWrapperPlatform.CryptoOperations] original localOriginal in
private theorem mpr_transport {N A : Type} {Private : N→Type} {left right : ProbComp (A×N)}
    (same : left=right)
    (typeEq : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private left=
      RegistrationNativePlatformExtractedSdkPublic.TotalStep Private right)
    (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private right) :
    Eq.mpr typeEq call=transport same.symm call :=by
  cases same
  rfl

omit [PublicWrapperPlatform.CryptoOperations] original localOriginal in
private theorem raw_transport {N A : Type} {Private : N→Type} {left right : ProbComp (A×N)}
    (same : left=right) (call : RegistrationNativePlatformExtractedSdkPublic.TotalStep Private left)
    (project : ∀current,Private current→Store n KemSK R P) :
    raw project (transport same call)=raw project call :=by
  cases same
  rfl

omit [PublicWrapperPlatform.CryptoOperations] original localOriginal in
private noncomputable def missing
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native×P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      (pure ((.ok none :RustM (Option Pqxdh.Bytes)),current)) := {
  step:={ Packet:=Unit
          sample:=pure ()
          sourceType:=Option Pqxdh.Bytes
          sourceReply:=fun _=>.ok none
          sourceState:=fun _=>objects.base.objects.snapshot.committed
          sourceCall:=pure (.ok none,objects.base.objects.snapshot.committed)
          source_exact:=rfl
          native:=fun _=>(.ok none,current)
          native_exact:=rfl
          store:=fun _ _=>objects }
  observe:=RustM.ok
  normal:=fun _ _=>⟨none,rfl⟩
  reply:=by intro _packet _supported returned actual;cases actual;rfl }

omit [PublicWrapperPlatform.CryptoOperations] original localOriginal in
private theorem missing_raw
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native×P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current) :
    raw (physical setup view views created credential) (missing setup view views created credential current objects)=
      pure (.ok (.ok none,physical setup view views created credential current objects),
        (physical setup view views created credential current objects).backend) :=by
  let call:=missing setup view views created credential current objects
  let result:=(RustM.ok (RustM.ok (none :Option Pqxdh.Bytes),physical setup view views created credential current objects),
    (physical setup view views created credential current objects).backend)
  unfold raw
  calc
    _=(fun _ : {value //value∈support call.step.sample}=>result) <$>PFunctor.FreeM.attachSupp call.step.sample :=by
      congr 1
      funext packet
      have same : returned call packet=none := (RustM.ok.inj (returned_exact call packet)).symm
      change (RustM.ok (call.observe (returned call packet),physical setup view views created credential _ (store call packet)),
        (physical setup view views created credential _ (store call packet)).backend)=_
      rw [same]
      rfl
    _=pure result :=rfl

variable [idleLocal : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource ×P) ProbComp))]
variable [idleCrypto : CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource ×P) ProbComp))]
variable [idleChildren : ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource ×P) ProbComp))]
variable [idleCodecs : Codecs (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource ×P) ProbComp))]

omit original localOriginal in
private theorem idle_raw
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (current : Native×P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential current)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8)
    (idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state) :
    raw (physical setup view views created credential)
      (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
        (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
        current objects.base.objects.snapshot.committed objects self input idle)=
      pure (.ok (.ok none,physical setup view views created credential current objects),
        (physical setup view views created credential current objects).backend) :=by
  let call:=RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
      current objects.base.objects.snapshot.committed objects self input idle
  let result:=(RustM.ok (RustM.ok (none :Option Pqxdh.Bytes),physical setup view views created credential current objects),
    (physical setup view views created credential current objects).backend)
  unfold raw
  calc
    _=(fun _ : {value //value∈support call.step.sample}=>result) <$>PFunctor.FreeM.attachSupp call.step.sample :=by
      congr 1
      funext packet
      have same : returned call packet=(core.option.Option.None,self) := (RustM.ok.inj (returned_exact call packet)).symm
      change (RustM.ok (call.observe (returned call packet),physical setup view views created credential _ (store call packet)),
        (physical setup view views created credential _ (store call packet)).backend)=_
      rw [same]
      rfl
    _=pure result :=rfl

theorem query (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (initial : ∀request,(localOriginal.ratchet_initial_ratchet_hkdf request).run=
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup contract.decapsulate)
    (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before : Native) (index : Nat) (input : Slice U8) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential (before,previous)) :
    raw (physical setup view views created credential)
      (RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
        before index input previous objects)=
      source (mlSource:=mlSource) coins setup checks representation created erased parseEd verifyEd writer
        (physical setup view views created credential (before,previous) objects) index input := by
  cases selected:before.beacons[index]? with
  | none=>
    have absent:=objects.base.beacons index
    rw [selected] at absent
    have callEq : RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
        before index input previous objects = transport
        (RegistrationNativePlatformSdkFinishDispatchModel.missing setup checks representation created wire index
          (AdapterPublicFinishLifetime.packet input) before coins previous selected).symm
        (missing setup view views created credential (before,previous) objects) :=by
      unfold RegistrationNativePlatformSdkFinishCoupledDispatch.step
      apply (RegistrationNativePlatformSdkDependentCases.rec_none _ _ _ selected).trans
      apply (RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
      exact mpr_transport (RegistrationNativePlatformSdkFinishDispatchModel.missing setup checks representation created wire index (AdapterPublicFinishLifetime.packet input) before coins previous selected) _ _
    calc
      _=raw (physical setup view views created credential) _ :=congrArg (raw (physical setup view views created credential)) callEq
      _=pure (.ok (.ok none,physical setup view views created credential (before,previous) objects),
          (physical setup view views created credential (before,previous) objects).backend) :=by
        rw [raw_transport]
        exact missing_raw setup view views created credential (before,previous) objects
      _=_ :=by
        unfold source
        change _=(match objects.base.objects.beacons index with | none=>_ | some self=>_)
        rw [absent]
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected:objects.base.objects.beacons index=some self:=(Classical.choose_spec prior).1
    have related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner
        before.server.world.world.1.owners[owner.worldOwner]? := (Classical.choose_spec prior).2
    cases stored:self.state with
    | InitSent pending prekey oneTime kem=>
      have phase : ∃scalar,owner.phase=.initSent pending scalar := by
        have matched:=related.phase
        cases phaseEq:owner.phase <;> simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        cases matched.1
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.initSent pending scalar:=Classical.choose_spec phase
      have callEq : RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
          before index input previous objects = RegistrationNativePlatformSdkFinishCoupled.active coins setup checks representation created wire view views credential
          self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected :=by
        unfold RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_sent _ _ _ _ _ _ pending prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by rfl))))
      calc
        _=raw (physical setup view views created credential) _ :=congrArg (raw (physical setup view views created credential)) callEq
        _=_ :=by
          rw [active coins setup checks representation created wire erased parseEd verifyEd writer initial view contract aligned views credential
            self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected]
          unfold source
          change _=(match objects.base.objects.beacons index with | none=>_ | some self=>_)
          rw [sourceSelected]
          rw [physical_backend]
    | Fresh control prekey kem=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state :=by rw [stored];trivial
      have callEq : RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
          before index input previous objects = transport
          (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index
            (AdapterPublicFinishLifetime.packet input) before coins previous owner selected
            (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state
              before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)).symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before,previous) objects.base.objects.snapshot.committed objects self input idle) :=by
        unfold RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_fresh _ _ _ _ _ _ control prekey kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index (AdapterPublicFinishLifetime.packet input) before coins previous owner selected (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)) _ _))))
      calc
        _=raw (physical setup view views created credential) _ :=congrArg (raw (physical setup view views created credential)) callEq
        _=pure (.ok (.ok none,physical setup view views created credential (before,previous) objects),
            (physical setup view views created credential (before,previous) objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup view views created credential (before,previous) objects self input idle
        _=_ :=by
          apply (source_idle coins setup checks representation created erased parseEd verifyEd writer
            (physical setup view views created credential (before,previous) objects) index self sourceSelected input idle ?_).symm
          rfl
    | FreshWithCoins control prekey oneTime kem=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state :=by rw [stored];trivial
      have callEq : RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
          before index input previous objects = transport
          (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index
            (AdapterPublicFinishLifetime.packet input) before coins previous owner selected
            (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state
              before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)).symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before,previous) objects.base.objects.snapshot.committed objects self input idle) :=by
        unfold RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_withCoins _ _ _ _ _ _ control prekey oneTime kem stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index (AdapterPublicFinishLifetime.packet input) before coins previous owner selected (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)) _ _))))
      calc
        _=raw (physical setup view views created credential) _ :=congrArg (raw (physical setup view views created credential)) callEq
        _=pure (.ok (.ok none,physical setup view views created credential (before,previous) objects),
            (physical setup view views created credential (before,previous) objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup view views created credential (before,previous) objects self input idle
        _=_ :=by
          apply (source_idle coins setup checks representation created erased parseEd verifyEd writer
            (physical setup view views created credential (before,previous) objects) index self sourceSelected input idle ?_).symm
          rfl
    | Established control binding manager=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state :=by rw [stored];trivial
      have callEq : RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
          before index input previous objects = transport
          (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index
            (AdapterPublicFinishLifetime.packet input) before coins previous owner selected
            (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state
              before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)).symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before,previous) objects.base.objects.snapshot.committed objects self input idle) :=by
        unfold RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_established _ _ _ _ _ _ control binding manager stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index (AdapterPublicFinishLifetime.packet input) before coins previous owner selected (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)) _ _))))
      calc
        _=raw (physical setup view views created credential) _ :=congrArg (raw (physical setup view views created credential)) callEq
        _=pure (.ok (.ok none,physical setup view views created credential (before,previous) objects),
            (physical setup view views created credential (before,previous) objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup view views created credential (before,previous) objects self input idle
        _=_ :=by
          apply (source_idle coins setup checks representation created erased parseEd verifyEd writer
            (physical setup view views created credential (before,previous) objects) index self sourceSelected input idle ?_).symm
          rfl
    | Aborted control=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state :=by rw [stored];trivial
      have callEq : RegistrationNativePlatformSdkFinishCoupledDispatch.step coins setup checks representation created wire view views credential
          before index input previous objects = transport
          (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index
            (AdapterPublicFinishLifetime.packet input) before coins previous owner selected
            (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state
              before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)).symm
          (RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
            (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential)
            (before,previous) objects.base.objects.snapshot.committed objects self input idle) :=by
        unfold RegistrationNativePlatformSdkFinishCoupledDispatch.step
        exact (RegistrationNativePlatformSdkDependentCases.rec_some _ _ _ owner selected).trans
          ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ selected).trans
            ((RegistrationNativePlatformSdkBeaconStateCases.rec_aborted _ _ _ _ _ _ control stored).trans
              ((RegistrationNativePlatformSdkDependentCases.rec_apply _ _ _ stored).trans (by exact mpr_transport (RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index (AdapterPublicFinishLifetime.packet input) before coins previous owner selected (RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state before.server.world.world.1.owners[owner.worldOwner]? related.phase idle)) _ _))))
      calc
        _=raw (physical setup view views created credential) _ :=congrArg (raw (physical setup view views created credential)) callEq
        _=pure (.ok (.ok none,physical setup view views created credential (before,previous) objects),
            (physical setup view views created credential (before,previous) objects).backend) :=by
          rw [raw_transport]
          exact idle_raw setup view views created credential (before,previous) objects self input idle
        _=_ :=by
          apply (source_idle coins setup checks representation created erased parseEd verifyEd writer
            (physical setup view views created credential (before,previous) objects) index self sourceSelected input idle ?_).symm
          rfl

theorem normal (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (initial : ∀request,(localOriginal.ratchet_initial_ratchet_hkdf request).run=
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup contract.decapsulate)
    (views : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before : Native) (index : Nat) (input : Slice U8) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views created credential (before,previous))
    (result : RustM (RustM (Option Pqxdh.Bytes) × Store n KemSK R P) × (Backend n KemSK × P))
    (supported : result∈support (source (mlSource:=mlSource) coins setup checks representation created erased parseEd verifyEd writer
        (physical setup view views created credential (before,previous) objects) index input)) :
    ∃word,result.1=.ok word ∧result.2=word.2.backend :=by
  have actual:=Eq.mp (congrArg (fun work=>result∈support work)
    (query coins setup checks representation created wire erased parseEd verifyEd writer initial view contract aligned views credential
      before index input previous objects).symm) supported
  simp only [raw,support_map] at actual
  obtain ⟨packet,_possible,same⟩:=actual
  cases same
  exact ⟨_,rfl,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.physical_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.physical_backend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.active_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.active_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.active

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.body_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.body_idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.source_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.source_idle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysical.normal
