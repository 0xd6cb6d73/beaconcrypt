-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperPin
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild
/-! The actual public Server helper equals native pure pin selection under the exact immutable key getters. It retains the complete selected binding and ML public key, consumes no hash operation, and leaves the native state unchanged. -/
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

omit [LawfulMonad m] in
theorem program_run (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array U8 1952#usize) (before : RegistrationServerFrontendCompiler.State n) :
    (simulateQ (fun _ => pure (.ok .None) : QueryImpl Spec (StateT (RegistrationServerFrontendCompiler.State n) m))
      (program binding publicKey)).run before =
      pure (.ok (.Some (⟨binding, publicKey⟩ : session.ServerAuthenticationPin)), before) := by
  rfl

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [localOps : LocalOperations (RustT (StateT (RegistrationServerFrontendCompiler.State n) m))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationServerFrontendCompiler.State n) m))]

theorem server_run (coins : QueryImpl unifSpec m) (self : beaconcrypt_public_wrapper.server.Server)
    (before : RegistrationServerFrontendCompiler.State n)
    (edLeaf : (crypto.edPublicBytes (platform.arcView self.identity).identity_key.public_key).run = pure (.ok before.pin.binding.identity_public_key))
    (mlLeaf : (localOps.auth_MldsaIdentity_public_key (platform.arcView self.identity).mldsa_identity).run = pure (.ok before.pin.public_key))
    (identifier : (platform.arcView self.identity).identity_key_kid = before.pin.binding.identity_key_id)
    :
    ((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self).run).run before =
    (RegistrationNativePlatformSourceBuild.pin coins).run before := by
  rw [AdapterPublicWrapperPin.server_program self _ _ edLeaf mlLeaf, identifier,
    RegistrationNativePlatformSourceBuild.pin_exact]
  rfl


theorem server_related {source : RegistrationNativeMldsa.Source} {KemSK : Type}
    (coins : QueryImpl unifSpec m) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view containers created credential self before)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey))
    :
    ((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self).run).run before =
    (RegistrationNativePlatformSourceBuild.pin coins).run before := by
  apply server_run coins self before
  · simpa only [related.identity.publicKey, related.pinIdentity] using
      edGetter (platform.arcView self.identity).identity_key.public_key
  · simpa only [related.identity.mldsa, related.pinMldsa] using
      mlGetter (platform.arcView self.identity).mldsa_identity
  · exact related.identity.identifier.trans related.pinIdentifier.symm


/-- Under the source-object field relation, pin selection retains every native coordinate. -/
theorem related_exact {source : RegistrationNativeMldsa.Source} {KemSK : Type}
    (coins : QueryImpl unifSpec m) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before : RegistrationServerFrontendCompiler.State n)
    (related : AdapterPublicWrapperState.Server view containers created credential self before)
    (edGetter : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key)))
    (mlGetter : ∀ identity, (localOps.auth_MldsaIdentity_public_key identity).run = pure (.ok (view.mldsa identity).publicKey)) :
    ((beaconcrypt_public_request.server.Server.authentication_pin
      (m := RustT (StateT (RegistrationServerFrontendCompiler.State n) m)) self).run).run before =
      pure (.ok (.Some before.pin), before) := by
  rw [server_related coins view containers created credential self before related edGetter mlGetter,
    RegistrationNativePlatformSourceBuild.pin_exact]

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

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.related_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPinNative.related_exact
