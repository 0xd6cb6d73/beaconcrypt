-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
/-! The actual same-packet support certificate is passed to the private continuation so current source frame receipts can construct every untouched object relation internally. This changes no execution, source result, native marginal or public reply. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported
open BeaconcryptCore.Refinement
open AdapterPublicFinishLifetime (packet)
open BeaconcryptCore.Computational

variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))]
variable {E : Type}

noncomputable def step (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
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
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform)
    (Private : (RegistrationNativeExperiment.State n KemSK source ×Platform)→Type)
    (embed : ∀ (sourceAfter : RegistrationNativeExperiment.State n KemSK source ×Platform)
      (raw : _root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source) (afterPlatform : Platform) (returned : AdapterPublicFinishBody.Result),
      sourceAfter=(raw.2,afterPlatform) →
      (raw,afterPlatform)∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous) →
      AdapterPublicFinishNormalized.output {self with state:=.Aborted (RegistrationResponse.abortedState pending)} raw.1.1=.ok returned →
      AdapterPublicFinishEndpoint.bytes (.ok returned)=RegistrationNativeFinishTerminalTree.bytes raw.1.1 →
      (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).beacons[index]?=
        some (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1) →
      AdapterPublicWrapperState.Beacon view setup.joint
        (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).pool returned.2
        (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1)
        (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).server.world.world.1.owners[owner.worldOwner]? →
      Private (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw,afterPlatform)) :
    RegistrationNativePlatformExtractedSdkAdaptive.Step Private
      ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
  have actual := RegistrationNativePlatformExtractedSdkFinish.executed setup checks representation created wire erased writer initial view model parseEd verifyEd self pending
    prekey oneTime kem stored input owner scalar keys decap before index related selected phase coins previous
  refine {
    Packet := _root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source ×Platform
    sample := (_root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous
    sourceType := AdapterPublicFinishBody.Result
    sourceReply := fun raw=>(_root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.sourceProjection self pending raw.1).1
    sourceState := fun raw=>(raw.1.2,raw.2)
    sourceCall := (fun result=>(result.1.1,(result.1.2,result.2))) <$>
      (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
        ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
          (m:=AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State)) self input).run)).run before)).run previous
    source_exact := ?_
    native := fun raw=>((_root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending before.beacons raw.1).1,
      ((_root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending before.beacons raw.1).2,raw.2))
    native_exact := ?_
    store := ?_ }
  · rw [actual.1,Functor.map_map]
    rfl
  · rw [actual.2,Functor.map_map]
    rfl
  · rintro ⟨raw,afterPlatform⟩ supported
    have receipt := RegistrationNativePlatformExtractedSdkFinish.returned_material view setup checks representation created wire
      index self owner pending prekey oneTime kem scalar stored before related selected phase (packet input) raw coins previous afterPlatform supported
    let returned := Classical.choose receipt
    have facts := Classical.choose_spec receipt
    dsimp only [_root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.sourceProjection]
    rw [facts.1]
    exact embed (raw.2,afterPlatform) raw afterPlatform returned rfl supported facts.1 facts.2.1 facts.2.2.1 facts.2.2.2

noncomputable def publicStep (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
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
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform)
    (Private : (RegistrationNativeExperiment.State n KemSK source ×Platform)→Type)
    (embed : ∀ (sourceAfter : RegistrationNativeExperiment.State n KemSK source ×Platform)
      (raw : _root_.BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source) (afterPlatform : Platform) (returned : AdapterPublicFinishBody.Result),
      sourceAfter=(raw.2,afterPlatform) →
      (raw,afterPlatform)∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous) →
      AdapterPublicFinishNormalized.output {self with state:=.Aborted (RegistrationResponse.abortedState pending)} raw.1.1=.ok returned →
      AdapterPublicFinishEndpoint.bytes (.ok returned)=RegistrationNativeFinishTerminalTree.bytes raw.1.1 →
      (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).beacons[index]?=
        some (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1) →
      AdapterPublicWrapperState.Beacon view setup.joint
        (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).pool returned.2
        (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1)
        (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).server.world.world.1.owners[owner.worldOwner]? →
      Private (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw,afterPlatform)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep Private
      ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous) := by
  let call:=step setup checks representation created wire erased writer initial view model parseEd verifyEd
    self pending prekey oneTime kem stored input owner scalar keys decap before index related selected phase coins previous Private embed
  refine {step:=call,observe:=fun value=>AdapterPublicFinishEndpoint.bytes (.ok value),normal:=?_,reply:=?_}
  · intro raw supported
    exact RegistrationNativePlatformExtractedSdkAdaptiveFinish.normal view setup checks representation created wire index self owner pending prekey oneTime kem scalar
      stored before related selected phase (packet input) raw.1 coins previous raw.2 supported
  · intro raw supported returned resultEq
    change (RegistrationNativePlatformExtractedSdkFinish.sourceProjection self pending raw.1).1=.ok returned at resultEq
    have same:=RegistrationNativePlatformExtractedSdkAdaptiveFinish.reply self pending index owner before.beacons raw.1
    rw [resultEq] at same
    exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported.publicStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported.publicStep
