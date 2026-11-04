-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish
/-! Active finish constructs the next complete source-object carrier internally from the same supported SDK result, preserving actual returned environment, source Self, every untouched object and both public counters. No caller continuation or complete source/frame law is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinishSteps
open BeaconcryptCore.Refinement
open AdapterPublicFinishLifetime (packet)
open BeaconcryptCore.Computational

variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))]
variable {E : Type}

variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)

noncomputable def step {R : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
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
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) {Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform)
    (objects : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containersView setup.joint created credential (before,previous))
    (sourceSelected : objects.objects.beacons index=some self) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep (RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containersView setup.joint created credential)
      ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous) := by
  have related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]? := by
    have prior:=objects.beacons index
    rw [selected] at prior
    obtain ⟨actual,found,material⟩:=prior
    have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
    subst actual
    exact material
  apply RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported.publicStep setup checks representation created wire erased writer initial view model parseEd verifyEd
    self pending prekey oneTime kem stored input owner scalar keys decap before index related selected phase coins previous
  intro sourceAfter raw afterPlatform returned sourceEq supported normal publicEq found material
  exact RegistrationNativePlatformExtractedSdkCarrierFinish.put coins setup checks representation created view containersView credential wire (before,previous) objects
    index owner selected self sourceSelected pending prekey oneTime kem scalar stored phase (packet input) (raw,afterPlatform) supported returned found material

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinishSteps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinishSteps.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinishSteps.step
