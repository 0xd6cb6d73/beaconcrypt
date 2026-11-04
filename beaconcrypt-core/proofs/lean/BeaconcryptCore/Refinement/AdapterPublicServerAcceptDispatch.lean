-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceNative
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceParsed
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptanceSemantics
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The typed accept dispatcher records a parsed-input ordinal before the original SDK receipt and actual native acceptance on the same run. Malformed raw inputs retain their original no-call state. Only this administrative bookkeeping is added around the unchanged source body. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerReservationNative (project AllocationReply)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response PlatformState : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource (StateT PlatformState ProbComp)
attribute [local irreducible] RegistrationAuthenticationExecutor.begin
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]


local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource

noncomputable def charged (input : Slice U8) (before : Native) : Native :=
  match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => before
  | some _ => {before with parsedAccepts := before.parsedAccepts + 1}

noncomputable def entry {A : Type} (input : Slice U8) (work : NativeM A) : NativeM A := fun before => work (charged input before)

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original localOps containers in
theorem entry_run {A : Type} (input : Slice U8) (work : NativeM A) (before : Native) :
    (entry input work).run before = work.run (charged input before) := rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original in
theorem material_retained (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource) (self : beaconcrypt_public_wrapper.server.Server)
    (before : Native) (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (input : Slice U8) :
    AdapterPublicWrapperState.Server view views created credential self (charged input before).server := by
  unfold charged
  cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) <;> exact related

noncomputable def native (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : (StateT PlatformState ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (input : Slice U8) : NativeM (RustM (Option Nat)) :=
  match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => pure (.ok none)
  | some packet => do
    modify fun before => {before with parsedAccepts := before.parsedAccepts + 1}
    RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet)

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] original localOps containers in
theorem native_run (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : (StateT PlatformState ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (input : Slice U8) (before : Native) :
    (native coins setup codec checks reserve route verify representation created input).run before =
      (AdapterPublicServerAcceptanceNative.accept coins setup codec checks reserve route verify representation created input).run (charged input before) := by
  unfold native charged AdapterPublicServerAcceptanceNative.accept
  cases RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) <;> rfl

theorem coupled {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView mlSource KemSK) (views : AdapterPublicWrapperStorage.Views)
    (model : AdapterPublicAgreementPrimitiveModel.Model (m := ProbComp) generator setup checks view)
    (entropy : AdapterPublicAgreementServerNative.Entropy model)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (@CryptoOperations.edPublicBytes material ed (RustT NativeM)
      (AdapterPublicAgreementNativePlatformInterpreter.operations coins original) key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (membershipOperation : ∀ identifier, AdapterPublicServerReplayPrefix.contains
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp))
      self.consumed_registrations identifier = pure (views.replay self.consumed_registrations identifier))
    (allocated : (StateT PlatformState ProbComp) AllocationReply)
    (allocationOperation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := (StateT PlatformState ProbComp)) views {self with consumed_registrations := history}) :
    project view (charged input before) <$>
      ((entry input (AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng)).run before) =
      RustM.ok <$> (native coins setup codec checks (AdapterPublicServerSourceLens.admitted <$> allocated)
        route verify model.representation created input).run before := by
  rw [entry_run, native_run]
  exact AdapterPublicServerAcceptanceNative.coupled coins setup codec checks route verify edLaws recording writer generator
    view views model entropy created credential self input rng (charged input before)
    (material_retained view views created credential self before related input) edGetter mlGetter membershipOperation
    allocated allocationOperation footprint insertion


theorem sdk {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
    Prod.snd <$> entry input (AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng) =
      entry input ((beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m := RustT NativeM) generator self input rng).run) := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  exact congrArg (fun work => entry input work)
    (AdapterPublicServerEntryReceipt.sdk coins setup codec route verify edLaws recording writer generator self input rng)

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] original localOps containers in
theorem typed [primitive : AdapterSealPrimitive.Operations] {E : Type}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT PlatformState ProbComp))
    (reserveRegistration reservePeer : (StateT PlatformState ProbComp) Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT PlatformState ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT PlatformState ProbComp))
    (input : Slice U8) (packet : registration.InitPacket)
    (decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) = some packet)
    (before : Native) :
    (native coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route mlSource.verify representation created input).run before =
      (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created mlSource credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.accept packet))).run before := by
  unfold native
  rw [decoded]
  rfl

open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt)
open AdapterPublicServerAgreementPost (Returned)


theorem post {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations identifier =
        pure (views.replay self.consumed_registrations identifier))
    (allocated : StateT PlatformState ProbComp AllocationReply)
    (operation : (AdapterPublicServerAcceptBody.setReserve
      (m := StateT Native (StateT PlatformState ProbComp)) self.consumed_registrations).run =
        RustM.ok <$> StateT.lift allocated)
    (footprint : ∀ previous reply next, (reply, next) ∈ support (allocated.run previous) →
      AdapterPublicWrapperStorage.ReplayReserve views self.consumed_registrations reply)
    (insertion : ∀ history, AdapterPublicServerAgreementRetention.Standard (n := n) (KemSK := KemSK)
      (mlSource := mlSource) (m := StateT PlatformState ProbComp) views {self with consumed_registrations := history})
    (receipt : Receipt R) (word : Word R) (previous next : PlatformState)
    (supported : (((receipt, .ok word), after), next) ∈ support
      (((entry input (AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng)).run before).run previous)) :
    ∃ handle nativeAfter, project view (charged input before) ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
      Returned view views created credential word (.ok handle, nativeAfter) := by
  rw [entry_run] at supported
  exact AdapterPublicServerAcceptancePost.source coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential (charged input before) after
    (material_retained view views created credential self before related input) edGetter mlGetter membershipOperation
    allocated operation footprint insertion receipt word previous next supported


theorem parsed {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
    (receipt : Receipt R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (nextRng : R) (previous next : PlatformState)
    (supported : (((receipt, .ok (.Some token, current, nextRng)), after), next) ∈ support
      (((entry input (AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng)).run before).run previous)) :
    AdapterPublicServerToken.ParsedToken token := by
  rw [entry_run] at supported
  exact AdapterPublicServerAcceptanceParsed.source coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential (charged input before) after
    (material_retained view views created credential self before related input) edGetter mlGetter receipt token current nextRng previous next supported

end BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.entry_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.entry_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.material_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.material_retained

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.native_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.coupled

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.sdk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.sdk

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.typed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.post

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptDispatch.parsed
