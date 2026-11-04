-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishLifetime
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedFinish
import BeaconcryptCore.Refinement.AdapterPublicFinishSourceJournal
import BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint
/-! The literal complete extracted active SDK finish and the actual corrected native finish are projections of the same trusted cryptographic run. Concrete decoding, source loops and individual primitive contracts are dependencies. Every reached result has derived normality, exact returned bytes and selected owner, and the complete private-material, binding, assigned-identifier, kernel and World-slot relation; the native finalizer accounts explicitly for metadata and the terminal administrative effect. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
open BeaconcryptCore.Refinement
open AdapterPublicFinishLifetime (packet)
open BeaconcryptCore.Computational

variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))]
variable {E : Type}
abbrev BodyResult (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  (RustM (Option registration.CompletedBeacon) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source
def decodedPacket (packet : Option registration.ResponsePacket) : core.option.Option registration.ResponsePacket :=
  match packet with | none=>.None | some value=>.Some value
noncomputable def runner {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source) : StateT Platform ProbComp (BodyResult n KemSK source) :=
  simulateQ coins (RegistrationNativeFinishLifetime.tree setup checks representation created wire pending packet owner scalar before)
noncomputable def sourceProjection (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (result : BodyResult n KemSK source) :=
  (AdapterPublicFinishNormalized.output {self with state := .Aborted (RegistrationResponse.abortedState pending)} result.1.1, result.2)
noncomputable def nativeProjection (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (pending : registration.BeaconPending)
    (owners : List (RegistrationNativeBeaconFrontend.Owner source)) (result : BodyResult n KemSK source) :=
  (RegistrationNativeFinishTerminalTree.bytes result.1.1,
    RegistrationNativeFinishTerminalTree.after index owner (RegistrationResponse.abortedState pending) result.1.1
      (RegistrationNativeFinishTerminalTree.assemble owners result.1.2 result.2))

theorem same_execution (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State) setup view)
    (parseEd : Slice U8 → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys)
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
    ((RegistrationNativeExperiment.beacon setup checks representation created
      ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) self input).run)).run before =
        (fun result => (AdapterPublicFinishNormalized.output {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} result.1.1, result.2)) <$>
          RegistrationNativeFinishLifetime.tree setup checks representation created wire pending (packet input) owner scalar before) ∧
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before =
      (fun result => (RegistrationNativeFinishTerminalTree.bytes result.1.1,
        RegistrationNativeFinishTerminalTree.after index owner (RegistrationResponse.abortedState pending) result.1.1
          (RegistrationNativeFinishTerminalTree.assemble before.beacons result.1.2 result.2))) <$>
            RegistrationNativeFinishLifetime.tree setup checks representation created wire pending (packet input) owner scalar before) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
  simpa only [RegistrationNativePlatformExtractedFinish.finish_source] using
    AdapterPublicFinishLifetime.same_execution setup checks representation created wire erased writer initial view model parseEd verifyEd self pending
      prekey oneTime kem stored input owner scalar keys decap before index related selected phase

theorem executed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State) setup view)
    (parseEd : Slice U8 → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys)
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
    ((simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
      ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
        (m := AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) self input).run)).run before)).run previous =
      Prod.map (sourceProjection self pending) id <$>
        (runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous) ∧
    ((simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous =
      Prod.map (nativeProjection index owner pending before.beacons) id <$>
        (runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
  have actual := same_execution setup checks representation created wire erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap before index related selected phase
  constructor
  · rw [actual.1, simulateQ_map, StateT.run_map]
    rfl
  · rw [actual.2, simulateQ_map, StateT.run_map]
    rfl

omit platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem returned_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar)
    (decoded : Option registration.ResponsePacket)
    (result : (RustM (Option registration.CompletedBeacon) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source)
    {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous afterPlatform : Platform)
    (reached : (result,afterPlatform) ∈support ((runner coins setup checks representation created wire pending decoded owner scalar before).run previous)) :
    ∃ returned : AdapterPublicFinishBody.Result,
      AdapterPublicFinishNormalized.output {self with state := .Aborted (RegistrationResponse.abortedState pending)} result.1.1 = .ok returned ∧
      AdapterPublicFinishEndpoint.bytes (.ok returned) = RegistrationNativeFinishTerminalTree.bytes result.1.1 ∧
      (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons result).beacons[index]? =
        some (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) result.1.1) ∧
      AdapterPublicWrapperState.Beacon view setup.joint (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons result).pool
        returned.2 (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) result.1.1)
        (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons result).server.world.world.1.owners[owner.worldOwner]? := by
  have raw : result ∈support (RegistrationNativeFinishLifetime.tree setup checks representation created wire pending decoded owner scalar before) := by
    apply OracleComp.support_simulateQ_run'_subset coins _ previous
    rw [StateT.run'_eq, support_map]
    exact ⟨(result,afterPlatform),reached,rfl⟩
  have called : result ∈support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
    ((RegistrationNativeFinishFactor.body setup wire pending (decodedPacket decoded) owner scalar).run
      (RegistrationWorldAgreementCompiler.erase before.server.world))).run before) := by
    cases decoded <;> exact raw
  exact AdapterPublicFinishLifetime.reached_material view setup checks representation created wire index self owner pending prekey oneTime kem scalar
    stored before related selected phase _ result called

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.same_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.same_execution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.executed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.executed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.returned_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.returned_material
