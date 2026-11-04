-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationNative
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal SDK Server getters and fingerprint helper use the same actual shared-cache hash callback as mandatory authentication. The complete Native/platform state, including the additional pin hash effect, is retained. Getter premises concern individual immutable primitive fields. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerWorldLens (world world_run simulate_world)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK I Reader Response : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

noncomputable def hash (coins : QueryImpl unifSpec m) :
    QueryImpl RegistrationNativeServerPinRecompute.Spec NativeM := fun request =>
  world (RegistrationNativePlatformInterpret.state coins (RegistrationNativeServerPinRecompute.nativeHash request))

omit material platform in
theorem hash_child {E : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec NativeM)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM) (request : registration.HashRequest) :
    (@ChildOperations.executeHash (RustT NativeM) (AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication
        (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) recording writer) request).run = hash coins request := by
  apply StateT.ext
  intro before
  change ((AdapterPublicWrapperChildNative.normalAuthentication
    (AdapterPublicServerAuthenticationNative.native coins setup codec route verify edLaws)) (.hash request)).run before = _
  simp only [AdapterPublicWrapperChildNative.normalAuthentication, QueryImpl.apply_compose,
    AdapterInitAuthenticationStateful.native, simulateQ_map, simulateQ_spec_query,
    AdapterPublicServerAuthenticationNative.native, RegistrationNativePlatformAuthentication.native,
    hash, StateT.run_map, world_run, RegistrationNativeServerPinRecompute.nativeHash,
    bind_pure_comp, Functor.map_map]
  unfold RegistrationNativePlatformAuthentication.core RegistrationNativePlatformInterpret.state
  simp only [RegistrationWorldAuthentication.implementation, QueryImpl.apply_compose,
    RegistrationWorldAuthentication.callbacks, simulateQ_spec_query,
    PqxdhRecordLiftWorld.handler, bind_pure_comp, simulateQ_map]
  change (fun result => (RustM.ok result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
      simulateQ coins (((fun value => core.option.Option.Some (RegistrationAuthenticationShared.digestArray value)) <$>
        PqxdhRecordLiftWorld.effects (.inr (.hash (RegistrationInputs.hashBytes request)))).run before.server.world.world.1) =
    (fun result => (result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
      simulateQ coins (((fun value => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray value))) <$>
        PqxdhRecordLiftWorld.effects (.inr (.hash (RegistrationInputs.hashBytes request)))).run before.server.world.world.1)
  simp only [StateT.run_map, simulateQ_map, Functor.map_map]

omit material platform ed in
theorem program_run (coins : QueryImpl unifSpec m)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (simulateQ (hash coins) (RegistrationNativeServerPinRecompute.program before.server.pin.binding before.server.pin.public_key)).run before =
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceBuild.pin coins)).run before := by
  unfold hash
  rw [← simulate_world, ← RegistrationNativePlatformInterpret.state_simulate, world_run]
  unfold RegistrationNativePlatformInterpret.state RegistrationNativePlatformExperiment.server
    RegistrationNativePlatformSourceBuild.pin RegistrationNativeServerPinRecompute.native
  simp only [StateT.run, Functor.map_map]
  rfl

variable [localOps : LocalOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]
variable [children : ChildOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK mlSource) m))]

theorem source (coins : QueryImpl unifSpec m) (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (hashLeaf : ∀ request, (children.executeHash request).run = hash coins request) :
    ((beaconcrypt_public_request.server.Server.authentication_pin (m := RustT NativeM) self).run).run before =
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceBuild.pin coins)).run before := by
  rw [AdapterPublicWrapperPin.server_program self _ _ (hash coins)
    (edGetter (platform.arcView self.identity).identity_key.public_key)
    (mlGetter (platform.arcView self.identity).mldsa_identity) hashLeaf]
  have identity : view.edPublic (platform.arcView self.identity).identity_key.public_key = before.server.pin.binding.identity_public_key :=
    related.identity.publicKey.trans related.pinIdentity.symm
  have identifier : (platform.arcView self.identity).identity_key_kid = before.server.pin.binding.identity_key_id :=
    related.identity.identifier.trans related.pinIdentifier.symm
  have publicKey : (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey = before.server.pin.public_key :=
    congrArg RegistrationNativeMldsa.Credential.publicKey related.identity.mldsa |>.trans related.pinMldsa.symm
  rw [identity, identifier, publicKey]
  exact program_run coins before

end BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal.hash_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal.hash_child

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal.program_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal.source
