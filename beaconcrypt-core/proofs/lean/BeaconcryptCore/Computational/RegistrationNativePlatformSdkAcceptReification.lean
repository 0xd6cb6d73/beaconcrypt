-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerReification
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptPoolFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptReification
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable {P : Type}
variable {n : Nat} {KemSK I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "NativeM" => StateT Native (StateT P ProbComp)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT P ProbComp)))]
theorem accepted {E R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before after : Native) (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT Native (StateT P ProbComp)) self.consumed_registrations identifier =
        pure (views.replay self.consumed_registrations identifier))
    (allocated : StateT P ProbComp AdapterPublicServerReservationNative.AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT P ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT P ProbComp) views {self with consumed_registrations := history})
    (receipt : AdapterPublicServerReservationReceipt.Receipt R) (word : AdapterPublicServerAgreementReceipt.Word R) (previous next : P)
    (supported : (((receipt, .ok word), after), next) ∈ support
      (((RegistrationNativePlatformExtractedSdkServer.Accept.run coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous))
    (reply : RustM (Option Nat)) (nativeAfter : Native)
    (projected : AdapterPublicServerReservationNative.project view (AdapterPublicServerAcceptDispatch.charged input before)
      ((receipt,.ok word),after)=.ok (reply,nativeAfter))
    (returned : AdapterPublicServerAgreementPost.Returned view views created credential word (reply,nativeAfter)) :
    RegistrationNativePlatformSdkReification.persistent
      (RegistrationNativePlatformSdkServerReification.snapshot view views word.2.1
        (RegistrationNativePlatformSdkServerReification.acceptEnvironment view
          (AdapterPublicServerAcceptDispatch.charged input before) receipt) (after,next)).committed=
      RegistrationNativePlatformSdkReification.persistent (nativeAfter,next) := by
  have poolEq:=RegistrationNativePlatformSdkAcceptPoolFrame.run coins setup codec route verify edLaws recording writer
    generator self input rng view views created credential before after related edGetter mlGetter membershipOperation
    allocated operation insertion receipt (.ok word) previous next supported
  have chargedPool : (AdapterPublicServerAcceptDispatch.charged input before).pool=before.pool := by
    unfold AdapterPublicServerAcceptDispatch.charged
    cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) <;> rfl
  exact RegistrationNativePlatformSdkServerReification.accept_project view views created credential
    (AdapterPublicServerAcceptDispatch.charged input before) after nativeAfter receipt word reply projected
    (poolEq.trans chargedPool.symm) returned.1 next
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptReification

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptReification.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkAcceptReification.accepted
