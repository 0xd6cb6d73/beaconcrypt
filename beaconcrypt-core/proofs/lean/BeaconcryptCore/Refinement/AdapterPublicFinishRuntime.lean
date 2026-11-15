-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishLifetime
import BeaconcryptCore.Computational.RegistrationNativePlatformRawFinish
/-! The literal complete extracted active SDK finish and the raw finish of the ordinary stateful platform runtime are projections of the same cryptographic execution. Concrete source-backed decoding handles every input, including malformed responses; the runtime still performs the active abort transition. Individual primitive, private-object and representation contracts are explicit. Both projections retain the complete native state and the same external platform state; the terminal projection includes the assigned identifier and administrative effect. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishRuntime
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {I KemSK E Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State))]
theorem active (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (sealView : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (runtimeWriter : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source RegistrationServerRoleBackend.State))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source RegistrationServerRoleBackend.State) setup view)
    (parseEd : Slice U8 → M n KemSK source RegistrationServerRoleBackend.State (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → M n KemSK source RegistrationServerRoleBackend.State (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : Owner source)
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
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
    ((RegistrationNativePlatformExperiment.liftNative (coins (Platform := Platform)) (RegistrationNativeExperiment.beacon setup checks representation created
      ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) self input).run))).run before =
        (fun result => (AdapterPublicFinishNormalized.output {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} result.1.1, result.2)) <$>
          simulateQ (coins (Platform := Platform)) (RegistrationNativeFinishLifetime.tree setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire) pending (AdapterPublicFinishLifetime.packet input) owner scalar before)) ∧
    ((simulateQ (RegistrationNativePlatformOrdinaryExperiment.handler setup checks RegistrationNativeConcreteCodec.wire route representation created source credential
      sealView failure allocation reserveRegistration reservePeer reserveFrame erased helper runtimeWriter)
      (RegistrationNativeRawAdapter.adapter (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
        (.inr (.finish index (TranscriptAuthParts.absSlice input))))).run before =
      (fun result => (RegistrationNativeRawAdapter.resultOption (RegistrationNativeFinishTerminalTree.bytes result.1.1),
        RegistrationNativeFinishTerminalTree.after index owner (RegistrationResponse.abortedState pending) result.1.1
          (RegistrationNativeFinishTerminalTree.assemble before.beacons result.1.2 result.2))) <$>
        simulateQ (coins (Platform := Platform)) (RegistrationNativeFinishLifetime.tree setup checks representation created
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
          pending (AdapterPublicFinishLifetime.packet input) owner scalar before)) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
  have coupled := AdapterPublicFinishLifetime.same_execution setup checks representation created
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
    erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap before index related selected phase
  constructor
  · change simulateQ (coins (Platform := Platform)) ((RegistrationNativeExperiment.beacon setup checks representation created
      ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
        (m := AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) self input).run)).run before) = _
    rw [coupled.1, simulateQ_map]
  · rw [RegistrationNativePlatformRawFinish.raw setup checks route representation created credential sealView failure allocation
      reserveRegistration reservePeer reserveFrame erased helper runtimeWriter index input, StateT.run_map]
    change (fun result => (RegistrationNativeRawAdapter.resultOption result.1, result.2)) <$>
      simulateQ (coins (Platform := Platform)) ((RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source
          (RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativeConcreteCodec.wire)
          index (AdapterPublicFinishLifetime.packet input))).run before) = _
    rw [coupled.2, simulateQ_map, Functor.map_map]

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishRuntime.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishRuntime.active

end BeaconcryptCore.Refinement.AdapterPublicFinishRuntime
