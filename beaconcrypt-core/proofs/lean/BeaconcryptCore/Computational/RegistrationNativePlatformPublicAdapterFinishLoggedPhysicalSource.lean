-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedSample
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPlatform
/-! The actual original SDK Finish body has the source-object and retained physical-state marginal of the same coupled native packet. The private key row and source scalars follow from actual stored material. Only the indexed KEM analysis observation log is erased; source objects, actual Env commit, all primitive counters/caches and P remain exact. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend backend worldBackend commitEnvironment)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformExtractedSdkFinish (runner BodyResult sourceProjection)
open AdapterPublicFinishLifetime (packet)
variable {n : Nat} {I KemSK P E Log : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOriginal : LocalOperations (RustT (StateT P ProbComp))]

noncomputable def raw (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (reached :(BodyResult n KemSK source×P)×List Log) :
    (RustM AdapterPublicFinishBody.Result×Backend n KemSK)×(P×List Log) :=
  (((sourceProjection self pending reached.1.1).1,erase (backend reached.1.1.2)),reached.1.2,reached.2)

noncomputable def project (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending)
    (reached :(BodyResult n KemSK source×P)×List Log) :
    (RustM AdapterPublicFinishBody.Result×Backend n KemSK)×(P×List Log) :=
  (((sourceProjection self pending reached.1.1).1,
    erase (backend (commitEnvironment reached.1.1.1.2 reached.1.1.2))),reached.1.2,reached.2)

omit platform localOriginal in
 theorem active (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (note :RegistrationNativePlatformPublicAdapterSourceTrace.Stage→Log)
    (erased :commitment.CommitmentTranscript)
    (parseEd :Slice U8→StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd :Slice U8→ed.PublicKey→StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup contract.decapsulate)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (phase : owner.phase=.initSent pending scalar) (previous : P) (past :List Log) :
    letI :CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
      RegistrationNativePlatformPublicAdapterUniformObserver.operations
        (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
    raw self pending <$>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
      pending (packet input) owner scalar before previous past =
      (fun result=>((result.1.1.1,result.1.2),(result.2,result.1.1.2))) <$>
        (((RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.run (mlSource:=source) setup wire
          (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks representation created) note erased
          (fun input=>StateT.lift (parseEd input)) (fun input key=>StateT.lift (verifyEd input key)) (fun query=>StateT.lift (writer query))
          self input).run past).run
            (erase (backend before))).run previous := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
  let keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar :=
    AdapterPublicAgreementBeaconMaterial.from_material view setup.joint before.pool self owner
      before.server.world.world.1.owners[owner.worldOwner]? related pending pending prekey oneTime kem scalar stored phase
  have row:=AdapterPublicAgreementBeaconMaterial.indexed_material view setup.joint before.pool self owner
    before.server.world.world.1.owners[owner.worldOwner]? related pending pending prekey oneTime kem scalar stored phase
  have closed:=RegistrationNativePlatformPublicAdapterFinishLoggedClosedSource.program note setup checks representation created wire view contract aligned
    self pending prekey oneTime kem stored input owner scalar keys past (backend before)
    (RegistrationNativePlatformSdkReification.worldBackend_idempotent before.server.world.world.1)
    (owner.kemPublic,view.kemSecret kem.secret_key) row rfl
  have sampled:=congrArg (fun work=>(simulateQ coins work).run previous) closed
  simp only [simulateQ_map,StateT.run_map] at sampled
  have nativeLaw:=RegistrationNativePlatformPublicAdapterFinishLoggedSample.platform coins setup checks representation created wire note self pending input owner scalar before previous past
  have observed:=congrArg (fun work=>Prod.map (Prod.map id erase) id <$>work) nativeLaw
  simp only [Functor.map_map] at observed
  have transport:=RegistrationNativePlatformPublicAdapterFinishLoggedPlatform.program note coins setup wire
    (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) view contract self input past
  have target:=congrArg (fun work=>(work.run (erase (backend before))).run previous) transport
  have first:=observed.trans (sampled.trans target)
  have packed:=congrArg (fun action=>(fun result=>((result.1.1.1,result.1.2),(result.2,result.1.1.2))) <$>action) first
  simp only [RegistrationNativePlatformPublicAdapterFinishLoggedSample.nativeResult,Functor.map_map,
    Prod.map_def,id_eq,Function.comp_def] at packed
  have literal:=RegistrationNativePlatformPublicAdapterFinishSourceObservedProgram.source setup wire
    (RegistrationNativePlatformSdkFinishPhysicalBody.trusted coins setup checks representation created) note
    view (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) erased
    (fun input=>StateT.lift (parseEd input)) (fun input key=>StateT.lift (verifyEd input key)) (fun query=>StateT.lift (writer query)) self input
  have observedLiteral:=congrArg (fun program=>(fun result=>((result.1.1.1,result.1.2),(result.2,result.1.1.2))) <$>
    (((program.run past).run (erase (backend before))).run previous)) literal
  exact packed.trans observedLiteral.symm

omit platform [PublicWrapperPlatform.CryptoOperations] original localOriginal in
 theorem project_run (coins :QueryImpl unifSpec (StateT P ProbComp))
    (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
    (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire :RegistrationNativeWire.Wire) (note :RegistrationNativePlatformPublicAdapterSourceTrace.Stage→Log)
    (self :beaconcrypt_public_wrapper.beacon.Beacon) (pending :registration.BeaconPending) (input :Slice U8)
    (owner :Owner source) (scalar :PqxdhJointGapDh.ScalarBytes)
    (before :RegistrationNativeExperiment.State n KemSK source) (previous :P) (past :List Log) :
    project self pending <$>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
      pending (packet input) owner scalar before previous past=
      raw self pending <$>RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample setup wire note coins checks representation created
        pending (packet input) owner scalar before previous past :=by
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have called:reached.1∈support ((runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous) :=by
    rw [←RegistrationNativePlatformPublicAdapterFinishLoggedFactor.sample_erase setup wire note coins checks representation created pending
      (packet input) owner scalar before previous past,support_map]
    exact ⟨reached,supported,rfl⟩
  have committed:=RegistrationNativePlatformSdkFinishAuxiliaryFrame.commit setup checks representation created wire pending
    (packet input) owner scalar before coins previous reached.1 called
  have erased:=congrArg RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent committed
  have same:=congrArg (fun state=>(((sourceProjection self pending reached.1.1).1,state.1),(state.2,reached.2))) erased
  exact congrArg (fun value=>(pure value:ProbComp _)) same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.active

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedPhysicalSource.project_run
