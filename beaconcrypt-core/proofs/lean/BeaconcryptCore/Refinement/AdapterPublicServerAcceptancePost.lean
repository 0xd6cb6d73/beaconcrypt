-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerLookupPost
import BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Every normal result of the actual complete public acceptance receipt retains live source Server material, and every returned source capability owns exactly the agreement in its matching native one-use slot. The source returned object, private RNG and original prefix effects are retained, including all rejection and failed-allocation branches. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerAgreementReceipt (Word)
open AdapterPublicServerReservationReceipt (Receipt)
open AdapterPublicServerReservationNative (AllocationReply project)
open AdapterPublicServerAgreementPost (Returned)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n : Nat} {KemSK I Reader Response PlatformState : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
variable [containers : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) (StateT PlatformState ProbComp)))]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "NativeM" => StateT Native (StateT PlatformState ProbComp)

theorem source {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
      (((AdapterPublicServerEntryReceipt.program coins setup codec route verify edLaws recording writer generator self input rng).run before).run previous)) :
    ∃ handle nativeAfter, project view before ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
      Returned view views created credential word (.ok handle, nativeAfter) := by
  rw [AdapterPublicServerEntryReceipt.source_joint coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential before related edGetter mlGetter] at supported
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none =>
    rw [decoded] at supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    cases supported
    exact ⟨none, before, rfl, related, trivial⟩
  | some packet =>
    rw [decoded] at supported
    simp only [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨lookup, currentNative⟩, between⟩, called, continued⟩ := supported
    rw [AdapterPublicServerWorldLens.world_run] at called
    simp only [StateT.run_map, support_map] at called
    obtain ⟨⟨⟨looked, world⟩, nextExternal⟩, called, returned⟩ := called
    have stateEq := congrArg (fun result => result.1.2) returned
    have replyEq := congrArg (fun result => result.1.1) returned
    have externalEq := congrArg Prod.snd returned
    cases replyEq
    cases externalEq
    change AdapterPublicAgreementNativeWorldMap.putWorld before world = currentNative at stateEq
    subst currentNative
    have prefixFrame := AdapterPublicServerPrefixFrame.program_server coins setup codec route verify edLaws
      self.control before.server.pin.binding before.server.pin.public_key packet
      before.server.world.world.1 world lookup previous between called
    have currentMaterial := AdapterPublicServerPrefixMaterial.related_world view views created credential self before related world prefixFrame
    cases lookup with
    | fail error | div =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        reduceCtorEq, and_false, false_and] at continued
    | ok optional => cases optional with
      | none =>
        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
        cases continued
        exact ⟨none, AdapterPublicAgreementNativeWorldMap.putWorld before world, rfl, currentMaterial, trivial⟩
      | some pending =>
        obtain ⟨handle, nativeAfter, projected, post⟩ := AdapterPublicServerLookupPost.source coins generator self pending rng
          view views created credential (AdapterPublicAgreementNativeWorldMap.putWorld before world) after currentMaterial
          (membershipOperation _) allocated operation footprint insertion receipt word between next continued
        rw [AdapterPublicServerPrefixMaterial.project_world] at projected
        exact ⟨handle, nativeAfter, projected, post⟩

theorem actual {E R Error : Type} (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
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
    :
    letI : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
    letI : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
    letI : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
    ∀ word previous next, ((.ok word, after), next) ∈ support
      ((((beaconcrypt_public_request.server.Server.get_shared_secret_with_rng
        (m := RustT NativeM) generator self input rng).run).run before).run previous) →
      ∃ receipt handle nativeAfter, project view before ((receipt, .ok word), after) = .ok (.ok handle, nativeAfter) ∧
        Returned view views created credential word (.ok handle, nativeAfter) := by
  let : CryptoOperations (RustT NativeM) := AdapterPublicAgreementNativePlatformInterpreter.operations coins original
  let : ChildOperations (RustT NativeM) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication
      (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer
  let : Codecs (RustT NativeM) := AdapterPublicConcreteCodecs.codecs
  intro word previous next supported
  rw [← AdapterPublicServerEntryReceipt.sdk coins setup codec route verify edLaws recording writer generator self input rng] at supported
  simp only [StateT.run_map, support_map] at supported
  obtain ⟨⟨⟨⟨receipt, result⟩, currentNative⟩, currentExternal⟩, called, returned⟩ := supported
  have stateEq := congrArg (fun value => value.1.2) returned
  have resultEq := congrArg (fun value => value.1.1) returned
  have externalEq := congrArg Prod.snd returned
  change currentNative = after at stateEq
  change result = .ok word at resultEq
  cases externalEq
  subst currentNative
  subst result
  obtain ⟨handle, nativeAfter, projected, post⟩ := source coins setup codec route verify edLaws recording writer generator self input rng
    view views created credential before after related edGetter mlGetter membershipOperation allocated operation footprint insertion
    receipt word previous next called
  exact ⟨receipt, handle, nativeAfter, projected, post⟩

end BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptancePost.actual
