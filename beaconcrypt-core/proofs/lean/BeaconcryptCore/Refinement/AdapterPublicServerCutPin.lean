-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPinGlobal
import BeaconcryptCore.Refinement.AdapterPublicServerSigningNative
import BeaconcryptCore.Refinement.AdapterPublicServerLocalLens
/-! The exact Server pin getter is pure under the request-only hash-cut dictionary. The same dictionary records actual authentication and AD transcript hashes, retaining their effects and the common platform poststate while erasure drops only the auxiliary cut. Individual immutable Ed/ML getters supply their object views. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicServerCutPin
open BeaconcryptCore.Computational
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n : Nat} {KemSK : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "Native" => RegistrationNativeExperiment.State n KemSK mlSource
local notation "NativeM" => StateT Native m
local notation "CutM" => StateT (RegistrationNativePlatformCutJournal.State Native) m
variable (coins : QueryImpl unifSpec m)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

noncomputable def outgoing : QueryImpl RegistrationSigningShared.Spec NativeM :=
  fun query => AdapterPublicServerLocalLens.localState (RegistrationNativePlatformServerCompletion.outgoing coins sign query)

noncomputable def hash : QueryImpl RegistrationNativeServerPinRecompute.Spec CutM := fun request =>
  (fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
    RegistrationNativePlatformCutJournal.hash (outgoing coins sign) request

theorem hash_native (request : registration.HashRequest) :
    (fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      outgoing (n := n) (KemSK := KemSK) (mlSource := mlSource) coins sign (.hash request) = AdapterPublicServerPinGlobal.hash coins request := by
  apply StateT.ext
  intro before
  rw [StateT.run_map]
  unfold outgoing
  rw [AdapterPublicServerLocalLens.local_run]
  simp only [RegistrationNativePlatformServerCompletion.outgoing, AdapterPublicServerPinGlobal.hash,
    AdapterPublicServerWorldLens.world_run, RegistrationNativeServerPinRecompute.nativeHash, bind_pure_comp, Functor.map_map]
  unfold RegistrationNativePlatformServerCompletion.liftNative RegistrationNativePlatformInterpret.state
    RegistrationNativePlatformServerCompletion.nativeOutgoing RegistrationWorldSigning.outgoing
  simp only [StateT.run, simulateQ_map, Functor.map_map]
  change _ = (fun result => (result.1, AdapterPublicAgreementNativeWorldMap.putWorld before result.2)) <$>
    simulateQ coins (((fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$>
      PqxdhRecordLiftWorld.effects (.inr (.hash (RegistrationInputs.hashBytes request))) :
      StateT (PqxdhRecordLiftWorld.State n) ProbComp RegistrationNativeServerPinRecompute.HashReply).run before.server.world.world.1)
  rw [StateT.run_map, simulateQ_map, Functor.map_map]
  rfl


theorem hash_erasure (request : registration.HashRequest) (before : RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id Prod.fst <$> (hash coins sign request).run before =
      (AdapterPublicServerPinGlobal.hash coins request).run before.1 := by
  rw [← hash_native coins sign request, StateT.run_map]
  unfold hash
  rw [StateT.run_map]
  have actual := congrArg (fun work : m (CtxRomAuth.CtxDigest × Native) =>
    (fun result => (RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1)), result.2)) <$> work)
    (RegistrationNativePlatformCutErasure.outgoing (outgoing coins sign) (.hash request) before)
  simpa only [RegistrationNativePlatformCutJournal.forward, Functor.map_map, Prod.map, id_eq] using actual

variable {A : Type}
theorem program_erasure (work : OracleComp RegistrationNativeServerPinRecompute.Spec A)
    (before : RegistrationNativePlatformCutJournal.State Native) :
    Prod.map id Prod.fst <$> (simulateQ (hash coins sign) work).run before =
      (simulateQ (AdapterPublicServerPinGlobal.hash coins) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (hash_erasure coins sign) work before

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) m))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK mlSource)) m))]
variable {E : Type}

theorem source (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (previous : ChildOperations (RustT CutM))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) NativeM)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationNativePlatformCutJournal.State Native)
    (related : AdapterPublicWrapperState.Server view views created credential self before.1.server)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey)) :
    letI : ChildOperations (RustT CutM) := AdapterPublicServerSigningNative.children (outgoing coins sign) previous writer
    Prod.map id Prod.fst <$> (((beaconcrypt_public_request.server.Server.authentication_pin (m := RustT CutM) self).run).run before) =
      (RegistrationNativePlatformExperiment.server (RegistrationNativePlatformSourceBuild.pin coins)).run before.1 := by
  rw [AdapterPublicWrapperPin.server_program self _ _
    (edGetter (platform.arcView self.identity).identity_key.public_key)
    (mlGetter (platform.arcView self.identity).mldsa_identity)]
  have identity : view.edPublic (platform.arcView self.identity).identity_key.public_key = before.1.server.pin.binding.identity_public_key :=
    related.identity.publicKey.trans related.pinIdentity.symm
  have identifier : (platform.arcView self.identity).identity_key_kid = before.1.server.pin.binding.identity_key_id :=
    related.identity.identifier.trans related.pinIdentifier.symm
  have publicKey : (view.mldsa (platform.arcView self.identity).mldsa_identity).publicKey = before.1.server.pin.public_key :=
    congrArg RegistrationNativeMldsa.Credential.publicKey related.identity.mldsa |>.trans related.pinMldsa.symm
  rw [identity, identifier, publicKey]
  simp only [StateT.run_pure, map_pure, Prod.map, id_eq]
  change (pure (RustM.ok (core.option.Option.Some
    (⟨before.1.server.pin.binding, before.1.server.pin.public_key⟩ : session.ServerAuthenticationPin)), before.1) : m _) = _
  exact AdapterPublicServerPinGlobal.program_run coins before.1

end BeaconcryptCore.Refinement.AdapterPublicServerCutPin

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCutPin.hash_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCutPin.hash_native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCutPin.hash_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCutPin.hash_erasure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCutPin.program_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCutPin.program_erasure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCutPin.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCutPin.source
