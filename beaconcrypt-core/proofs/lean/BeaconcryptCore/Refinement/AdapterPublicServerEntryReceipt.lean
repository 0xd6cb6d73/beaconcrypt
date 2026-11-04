-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix
import BeaconcryptCore.Refinement.AdapterPublicServerEntry
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Private instrumentation covers the original extracted public Server delegator, concrete decoding, real getter/pin/authentication prefix and the complete actual lookup/reservation/agreement/one-use insertion path. Receipt erasure recovers that exact public SDK body, including returned Self/RNG and every Rust failure/poststate. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

noncomputable def program {E R Error : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R) : NativeM (Receipt R × RustM (Word R)) :=
  letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  letI : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  letI : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  do
    let checked ← (AdapterPublicServerAcceptBody.authenticate (m := NativeM) self input).run
    match checked with
    | .fail error => pure (none, .fail error)
    | .div => pure (none, .div)
    | .ok .None => pure (none, .ok (.None, self, rng))
    | .ok (.Some pending) => AdapterPublicServerLookupReceipt.program coins generator self pending rng

theorem sdk {E R Error : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R) :
    letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    letI : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
    letI : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
    Prod.snd <$> program coins setup codec route verify edLaws recording writer generator self input rng =
      (beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m := RustT NativeM) generator self input rng).run := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicServerEntry.source]
  unfold program AdapterPublicServerEntry.sequence
  rw [map_bind, RustT.run_bind]
  apply bind_congr
  intro checked
  cases checked with
  | fail error | div => simp only [map_pure]
  | ok optional => cases optional with
    | none => simp only [map_pure, RustT.run_pure]
    | some pending => exact AdapterPublicServerLookupReceipt.sdk coins generator self pending rng


theorem source_joint {E R Error : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (input : Slice U8) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey)) :
    (program coins setup codec route verify edLaws recording writer generator self input rng).run before = (
      match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
      | none => pure ((none, .ok (.None, self, rng)), before)
      | some packet => do
        let (checked, current) ← (AdapterPublicServerWorldLens.world
          (AdapterPublicServerAuthenticationPrefix.program coins setup codec route verify edLaws
            self.control before.server.pin.binding before.server.pin.public_key packet)).run before
        match checked with
        | .fail error => pure ((none, .fail error), current)
        | .div => pure ((none, .div), current)
        | .ok .None => pure ((none, .ok (.None, self, rng)), current)
        | .ok (.Some pending) => (AdapterPublicServerLookupReceipt.program coins generator self pending rng).run current) := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  unfold program
  rw [StateT.run_bind, AdapterPublicServerAuthenticationPrefix.source coins setup codec route verify edLaws recording writer
    view views created credential self input before related edGetter mlGetter]
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => simp only [pure_bind, StateT.run_pure]
  | some packet =>
    simp only []
    apply bind_congr
    rintro ⟨checked, current⟩
    cases checked with
    | fail error | div => rfl
    | ok optional => cases optional <;> rfl


end BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt.sdk

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt.source_joint
