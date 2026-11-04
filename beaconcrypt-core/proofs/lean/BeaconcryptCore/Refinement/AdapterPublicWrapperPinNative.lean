-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
/-! The actual public Server getter/hash helper equals the native shared-World pin computation under narrow immutable key getters and the concrete hash-field interpretation. Private source-object views derive its binding and ML public key. A retained actual cache receipt preserves every non-hash coordinate and charges the literal extra hash before the adaptive continuation. The generic helper also supports richer private journals through its separate hash-program theorem. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
open RegistrationNativeServerPinRecompute (Spec program native nativeHash)
variable {n : Nat} {m : Type → Type} [Monad m] [LawfulMonad m]

noncomputable def hash (coins : QueryImpl unifSpec m) :
    QueryImpl Spec (StateT (RegistrationServerFrontendCompiler.State n) m) := fun request before =>
  (fun result => (result.1, { before with world :=
    { before.world with world := (result.2, before.world.world.2) } })) <$>
    simulateQ coins ((nativeHash request).run before.world.world.1)

theorem program_run (coins : QueryImpl unifSpec m) (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array U8 1952#usize) (before : RegistrationServerFrontendCompiler.State n) :
    (simulateQ (hash coins) (program binding publicKey)).run before =
      (fun result => (result.1, { before with world :=
        { before.world with world := (result.2, before.world.world.2) } })) <$>
        simulateQ coins ((native binding publicKey).run before.world.world.1) := by
  simp only [program, native, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
    map_bind, map_pure]
  dsimp only [hash, StateT.run]
  simp only [bind_map_left]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [localOps : LocalOperations (RustT (StateT (RegistrationServerFrontendCompiler.State n) m))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationServerFrontendCompiler.State n) m))]
variable [children : ChildOperations (RustT (StateT (RegistrationServerFrontendCompiler.State n) m))]

theorem server_run (coins : QueryImpl unifSpec m) (self : beaconcrypt_public_wrapper.server.Server)
    (before : RegistrationServerFrontendCompiler.State n)
    (edLeaf : (crypto.edPublicBytes (platform.arcView self.identity).identity_key.public_key).run = pure (.ok before.pin.binding.identity_public_key))
    (mlLeaf : (localOps.auth_MldsaIdentity_public_key (platform.arcView self.identity).mldsa_identity).run = pure (.ok before.pin.public_key))
    (identifier : (platform.arcView self.identity).identity_key_kid = before.pin.binding.identity_key_id)
    (hashLeaf : ∀ request, (children.executeHash request).run = hash coins request) :
    ((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self).run).run before =
    (RegistrationNativePlatformSourceBuild.pin coins).run before := by
  rw [AdapterPublicWrapperPin.server_program self _ _ (hash coins) edLeaf mlLeaf hashLeaf,
    identifier, program_run]
  rfl


theorem server_related {source : RegistrationNativeMldsa.Source} {KemSK : Type}
    (coins : QueryImpl unifSpec m) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view containers created credential self before)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (hashLeaf : ∀ request, (children.executeHash request).run = hash coins request) :
    ((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self).run).run before =
    (RegistrationNativePlatformSourceBuild.pin coins).run before := by
  apply server_run coins self before
  · simpa only [related.identity.publicKey, related.pinIdentity] using
      edGetter (platform.arcView self.identity).identity_key.public_key
  · simpa only [related.identity.mldsa, related.pinMldsa] using
      mlGetter (platform.arcView self.identity).mldsa_identity
  · exact related.identity.identifier.trans related.pinIdentifier.symm
  · exact hashLeaf


section Cached
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}
variable (coins : QueryImpl unifSpec m) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view containers created credential self before)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    (hashLeaf : ∀ request, (children.executeHash request).run = hash coins request)
include related edGetter mlGetter hashLeaf

def charged (current : RegistrationServerFrontendCompiler.State n) : RegistrationServerFrontendCompiler.State n :=
  { current with world := { current.world with world :=
    (PqxdhRecordLiftWorld.chargeEffect (.inr (.hash (PqxdhRefinement.absBytes current.pin.public_key)))
      current.world.world.1, current.world.world.2) } }

theorem cached_run (cached : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2) :
    ((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self).run).run before =
      pure (.ok (.Some before.pin), charged before) := by
  rw [server_related coins view containers created credential self before related edGetter mlGetter hashLeaf]
  unfold RegistrationNativePlatformSourceBuild.pin
  dsimp only [StateT.run]
  have hit := RegistrationNativeServerPinRecompute.native_hit before.pin before.world.world.1 cached
  dsimp only [StateT.run] at hit
  rw [hit]
  simp only [simulateQ_pure, map_pure, charged]

theorem cached_continuation {Output : Type}
    (cached : RegistrationNativeServerPinRecompute.Cached before.pin before.world.world.1.primitive.2)
    (next : core.option.Option session.ServerAuthenticationPin → RustT (StateT (RegistrationServerFrontendCompiler.State n) m) Output) :
    (((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self) >>= next).run).run before =
      ((next (.Some before.pin)).run).run (charged before) := by
  rw [RustT.run_bind, StateT.run_bind,
    cached_run coins view containers created credential self before related edGetter mlGetter hashLeaf cached]
  simp only [pure_bind]
end Cached

end BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.program_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.server_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.server_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.server_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.server_related

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.cached_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.cached_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.cached_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.cached_continuation
