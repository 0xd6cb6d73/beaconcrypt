-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTokenLineage
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierServer
/-! Actual successful source acceptance extends the live-token parse lineage with its own authentication parse receipt. The complete source acceptance sample, not a validity premise about arbitrary tokens, supplies the new fact. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptedTokens
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response Platform : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "NativeM"=>StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp)
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp)))]

theorem accepted {E R Error : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source ×Platform)
    (before : RegistrationNativePlatformPublicAdapterTokenLineage.Carrier (R:=R) setup view views created credential current)
    (input : Slice U8)
    (edGetter : ∀key,(@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run=pure (.ok (view.edPublic key)))
    (mlGetter : ∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
    (receipt : AdapterPublicServerReservationReceipt.Receipt R) (word : AdapterPublicServerAgreementReceipt.Word R)
    (rawAfter : RegistrationNativeExperiment.State n KemSK source) (platformAfter : Platform)
    (supported : (((receipt,.ok word),rawAfter),platformAfter)∈support
      (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator
        before.base.base.objects.server input before.base.base.objects.rng).run current.1).run current.2))
    (snapshot : RegistrationNativePlatformExtractedSdkCarrier.SourceSnapshot n KemSK Platform source) :
    RegistrationNativePlatformPublicAdapterTokenLineage.Parsed
      (RegistrationNativePlatformExtractedSdkCarrierServer.acceptUpdate before.base.base.objects word snapshot).tokens := by
  rcases word with ⟨optional,self,rng⟩
  cases optional with
  | none=>exact before.parsed
  | some token=>
    apply RegistrationNativePlatformPublicAdapterTokenLineage.insert before.base.base.objects.tokens before.parsed
    exact AdapterPublicServerAcceptDispatch.parsed coins setup codec route verify edLaws recording writer generator
      before.base.base.objects.server input before.base.base.objects.rng view views created credential current.1 rawAfter
      before.base.base.server edGetter mlGetter receipt token self rng current.2 platformAfter supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptedTokens
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptedTokens.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptedTokens.accepted
