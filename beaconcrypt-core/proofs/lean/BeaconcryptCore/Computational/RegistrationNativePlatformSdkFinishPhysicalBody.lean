-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSourceProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampling
/-! The actual SDK Finish body executes with the original source crypto dictionary and persistent local leaves. Its executable inputs are the actual source Self and original source bytes, with no model owner, scalar or precomputed protocol reply. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativeBeaconFrontend (Trusted)
open RegistrationNativePlatformSdkReification (Backend)
variable {n : Nat} {I KemSK E P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOriginal : LocalOperations (RustT (StateT P ProbComp))]
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)

noncomputable def trusted (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    QueryImpl (Trusted n KemSK) PhysicalM := fun query =>
  RegistrationNativePlatformInterpret.state coins
    (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created query)

noncomputable def body (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) : PhysicalM (RustM AdapterPublicFinishBody.Result) :=
  letI : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
  letI : LocalOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterLeaves.localOperations localOriginal
  RegistrationNativePlatformSdkFinishSourceProgram.run (source:=source) setup
    (trusted coins setup checks representation created) erased
    (fun input=>StateT.lift (parseEd input)) (fun input key=>StateT.lift (verifyEd input key))
    (fun query=>StateT.lift (writer query)) self input

noncomputable def model (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view) :
    letI : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
    AdapterPublicAgreementCommonModel.Model (m:=PhysicalM) setup view :=
  RegistrationNativePlatformPublicAdapterCommonModel.model (RegistrationNativePlatformSdkFinishSampling.uniformP coins) setup view contract

 theorem body_source (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (erased : commitment.CommitmentTranscript)
    (parseEd : Slice U8 → StateT P ProbComp (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → StateT P ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (initial : ∀ request, (localOriginal.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    letI : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterUniformObserver.operations
      (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
    body (n:=n) (source:=source) coins setup checks representation created erased parseEd verifyEd writer self input =
      RegistrationNativePlatformSdkFinishSourceProgram.program setup RegistrationNativeConcreteCodec.wire
        (trusted coins setup checks representation created) view (model (n:=n) coins setup view contract) self input := by
  let : CryptoOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterUniformObserver.operations
    (RegistrationNativePlatformSdkFinishSampling.uniformP coins) original
  let : LocalOperations (RustT PhysicalM) := RegistrationNativePlatformPublicAdapterLeaves.localOperations localOriginal
  apply RegistrationNativePlatformSdkFinishSourceProgram.source_program setup RegistrationNativeConcreteCodec.wire
    (trusted coins setup checks representation created) erased
    (fun input=>StateT.lift (parseEd input)) (fun input key=>StateT.lift (verifyEd input key))
    (fun query=>StateT.lift (writer query)) _ view (model (n:=n) coins setup view contract) self input
  intro request
  change StateT.lift (localOriginal.ratchet_initial_ratchet_hkdf request).run = _
  rw [initial]
  funext before
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishPhysicalBody.body_source
