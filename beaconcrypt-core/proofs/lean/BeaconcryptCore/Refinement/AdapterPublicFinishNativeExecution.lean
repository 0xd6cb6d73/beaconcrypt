-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishFreeSafety
/-! The literal complete active extracted SDK finish now executes in the actual Native trusted interpreter. Equality retains the complete returned source object, owners, primitive pool, cache histories and real counters on the same execution. Concrete decoder and source body refinements occur in the dependency chain; only granular primitive functional and representation contracts remain. Metadata journals and the terminal World lifecycle are composed separately. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishNativeExecution
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner Trusted)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State))]
variable {E : Type}
theorem source_native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (wire : RegistrationNativeWire.Wire)
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
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
    RegistrationNativeExperiment.beacon setup checks representation created
      ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) self input).run) =
        simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          (AdapterPublicFinishFreeTree.program setup wire self pending input owner scalar) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicFinishFreeTree.source_tree setup wire erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap]
  exact RegistrationNativeLocalEnvironmentFrame.beacon_lift setup checks representation created _
    (AdapterPublicFinishFreeSafety.program_safe setup wire self pending input owner scalar)

end BeaconcryptCore.Refinement.AdapterPublicFinishNativeExecution

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishNativeExecution.source_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishNativeExecution.source_native
