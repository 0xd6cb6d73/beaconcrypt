-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishRunnerSource
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformSdkReification (Backend backend worldBackend commitEnvironment)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformExtractedSdkFinish (runner BodyResult sourceProjection)
open AdapterPublicFinishLifetime (packet)
variable {n : Nat} {I KemSK P E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOriginal : LocalOperations (RustT (StateT P ProbComp))]

noncomputable def raw (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (reached : BodyResult n KemSK source × P) :
    (RustM AdapterPublicFinishBody.Result × Backend n KemSK) × P :=
  (((sourceProjection self pending reached.1).1,erase (backend reached.1.2)),reached.2)

noncomputable def project (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (reached : BodyResult n KemSK source × P) :
    (RustM AdapterPublicFinishBody.Result × Backend n KemSK) × P :=
  (((sourceProjection self pending reached.1).1,
    erase (backend (commitEnvironment reached.1.1.2 reached.1.2))),reached.2)

 theorem active (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (initial : ∀ request, (localOriginal.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup contract.decapsulate)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (phase : owner.phase=.initSent pending scalar) (previous : P) :
    raw self pending <$> (runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous =
      ((RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=source) coins setup checks representation created erased
        parseEd verifyEd writer self input).run (erase (backend before))).run previous := by
  let : CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
  let : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
    RegistrationNativePlatformPublicAdapterLeaves.localOperations localOriginal
  let keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar :=
    AdapterPublicAgreementBeaconMaterial.from_material view setup.joint before.pool self owner
      before.server.world.world.1.owners[owner.worldOwner]? related pending pending prekey oneTime kem scalar stored phase
  have row:=AdapterPublicAgreementBeaconMaterial.indexed_material view setup.joint before.pool self owner
    before.server.world.world.1.owners[owner.worldOwner]? related pending pending prekey oneTime kem scalar stored phase
  have closed:=RegistrationNativePlatformSdkFinishClosedSource.program setup checks representation created wire view contract aligned
    self pending prekey oneTime kem stored input owner scalar keys (backend before)
    (RegistrationNativePlatformSdkReification.worldBackend_idempotent before.server.world.world.1)
    (owner.kemPublic,view.kemSecret kem.secret_key) row rfl
  have sampled:=congrArg (fun work=>(simulateQ coins work).run previous) closed
  simp only [simulateQ_map,StateT.run_map] at sampled
  have nativeLaw:=RegistrationNativePlatformSdkFinishRunnerSource.platform coins setup checks representation created wire self pending input owner scalar before previous
  have observed:=congrArg (fun work=>Prod.map (Prod.map id erase) id <$>work) nativeLaw
  simp only [Functor.map_map] at observed
  have transport:=RegistrationNativePlatformSdkFinishPlatform.program coins setup wire
    (RegistrationNativePlatformSdkFinishBackend.handler (n:=n) setup checks representation created) view contract self input
  have target:=congrArg (fun work=>(work.run (erase (backend before))).run previous) transport
  have actual : RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=source) coins setup checks representation created erased
      parseEd verifyEd writer self input =
      RegistrationNativePlatformSdkFinishSourceProgram.program setup wire
        (RegistrationNativePlatformSdkFinishPhysicalBody.trusted (n:=n) coins setup checks representation created)
        view (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self input := by
    apply RegistrationNativePlatformSdkFinishSourceProgram.source_program setup wire
      (RegistrationNativePlatformSdkFinishPhysicalBody.trusted (n:=n) coins setup checks representation created) erased
      (fun input=>StateT.lift (parseEd input)) (fun input key=>StateT.lift (verifyEd input key))
      (fun query=>StateT.lift (writer query)) _ view
      (RegistrationNativePlatformSdkFinishPhysicalBody.model (n:=n) coins setup view contract) self input
    intro request
    change StateT.lift (localOriginal.ratchet_initial_ratchet_hkdf request).run = _
    rw [initial]
    funext state
    rfl
  have executed:=congrArg (fun work=>(work.run (erase (backend before))).run previous) actual
  exact observed.trans (sampled.trans (target.trans executed.symm))

omit platform [PublicWrapperPlatform.CryptoOperations] original localOriginal in
 theorem project_run (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconPending) (input : Slice U8) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : P) :
    project self pending <$>(runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous =
      raw self pending <$>(runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous := by
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have committed:=RegistrationNativePlatformSdkFinishAuxiliaryFrame.commit setup checks representation created wire pending
    (packet input) owner scalar before coins previous reached supported
  have erased:=congrArg RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent committed
  have same:=congrArg (fun state=>(((sourceProjection self pending reached.1).1,state.1),state.2)) erased
  exact congrArg (fun value=>(pure value :ProbComp _)) same

 theorem observed (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (initial : ∀ request, (localOriginal.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (aligned : RegistrationNativePlatformSdkFinishDecapsulation.Aligned setup contract.decapsulate)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (phase : owner.phase=.initSent pending scalar) (previous : P) :
    project self pending <$> (runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous =
      ((RegistrationNativePlatformSdkFinishPhysicalBody.body (n:=n) (source:=source) coins setup checks representation created erased
        parseEd verifyEd writer self input).run (erase (backend before))).run previous := by
  rw [project_run coins setup checks representation created wire self pending input owner scalar before previous]
  exact active coins setup checks representation created wire erased parseEd verifyEd writer initial view contract aligned
    self pending prekey oneTime kem stored input owner scalar before related phase previous

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource.active

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource.project_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource.project_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource.observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalSource.observed
