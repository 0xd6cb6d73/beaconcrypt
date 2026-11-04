-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongFinishSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongFinishDispatch
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


variable {Platform : Type}
variable [idleLocal : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleCrypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleChildren : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleCodecs : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]

omit localOps crypto idleLocal idleCrypto idleChildren idleCodecs [PublicWrapperPlatform.CryptoOperations] in
private noncomputable def absent {R : Type}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (created : PqxdhLiveServerConstruction.Created Unit)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (current : RegistrationNativeExperiment.State n KemSK source×Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential current) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (pure ((.ok none :RustM (Option Pqxdh.Bytes)),current)) := {
  step:={
    Packet:=Unit
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
  reply:=by intro _packet _supported returned actual; cases actual; rfl }

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
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat) (input : Slice U8)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before,previous))
    (decapsulation : ∀(owner : RegistrationNativeBeaconFrontend.Owner source) (secret : material.KemSecretKey),
      before.beacons[index]?=some owner →
      before.pool.keys[owner.kemHandle]?=some (owner.kemPublic,view.kemSecret secret) →
      ∀ciphertext,model.decapsulate ciphertext (view.kemSecret secret)=AdapterPublicAgreementBeaconFrontend.indexedDecapsulation owner ciphertext) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous) := by
  cases selected:before.beacons[index]? with
  | none=>
    rw [RegistrationNativePlatformSdkFinishDispatchModel.missing setup checks representation created wire index (packet input) before coins previous selected]
    exact absent containersView credential setup created view (before,previous) objects
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected : objects.base.objects.beacons index=some self := (Classical.choose_spec prior).1
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
      let keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
          (AdapterPublicAgreementBeaconMaterial.registrationKeys {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar :=
        AdapterPublicAgreementBeaconMaterial.from_material view setup.joint before.pool self owner
          before.server.world.world.1.owners[owner.worldOwner]? related pending pending prekey oneTime kem scalar stored phase
      have row:=AdapterPublicAgreementBeaconMaterial.indexed_material view setup.joint before.pool self owner
        before.server.world.world.1.owners[owner.worldOwner]? related pending pending prekey oneTime kem scalar stored phase
      have decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
          (AdapterPublicAgreementBeaconMaterial.registrationKeys {self with state:=.Aborted (RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys := by
        exact ⟨decapsulation owner kem.secret_key selected row⟩
      exact RegistrationNativePlatformSdkStrongFinishSteps.step containersView credential setup checks representation created wire erased writer initial view model parseEd verifyEd
        self pending prekey oneTime kem stored input owner scalar keys decap before index selected phase coins previous objects sourceSelected
    | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state := by rw [stored]; trivial
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state
        before.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      rw [RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index (packet input) before coins previous owner selected inactive]
      exact RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
        (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
        (before,previous) objects.base.objects.snapshot.committed objects self input idle
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongFinishDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongFinishDispatch.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongFinishDispatch.step
