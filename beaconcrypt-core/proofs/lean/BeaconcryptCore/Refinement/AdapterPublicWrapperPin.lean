-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute
/-! The actual public fingerprint and Server getter sequence interpret in one shared monad. Only two immutable primitive getter contracts and the actual hash leaf interpretation are parameters; failure/divergence and every shared poststate are retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicWrapperPin
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperLiftFunction
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

omit material platform primitive localOps crypto in
theorem fingerprint_program (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (hash : QueryImpl RegistrationNativeServerPinRecompute.Spec m)
    (hashLeaf : ∀ request, (children.executeHash request).run = hash request) :
    (beaconcrypt_public_request.auth.fingerprint_pin (m := RustT m) binding publicKey).run =
      simulateQ hash (RegistrationNativeServerPinRecompute.program binding publicKey) := by
  unfold beaconcrypt_public_request.auth.fingerprint_pin
  dsimp only [call, LiftFunction.lift, AdapterPublicWrapperLiftFunction.function,
    AdapterPublicWrapperLiftFunction.result, AdapterRecordRequestMonad.liftRust,
    registration.begin_server_pin, registration.PinFingerprint.request]
  simp only [RustT.run_bind, pure_bind, hashLeaf,
    RegistrationNativeServerPinRecompute.program, RegistrationNativeServerPinRecompute.request,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  apply bind_congr
  intro reply
  cases reply <;> rfl


theorem server_program (self : beaconcrypt_public_wrapper.server.Server)
    (publicBytes : Std.Array U8 32#usize) (publicKey : Std.Array U8 1952#usize)
    (hash : QueryImpl RegistrationNativeServerPinRecompute.Spec m)
    (edLeaf : (crypto.edPublicBytes (platform.arcView self.identity).identity_key.public_key).run = pure (.ok publicBytes))
    (mlLeaf : (localOps.auth_MldsaIdentity_public_key (platform.arcView self.identity).mldsa_identity).run = pure (.ok publicKey))
    (hashLeaf : ∀ request, (children.executeHash request).run = hash request) :
    (beaconcrypt_public_request.server.Server.authentication_pin (m := RustT m) self).run =
      simulateQ hash (RegistrationNativeServerPinRecompute.program
        ⟨publicBytes, (platform.arcView self.identity).identity_key_kid⟩ publicKey) := by
  unfold beaconcrypt_public_request.server.Server.authentication_pin
  simp only [beaconcrypt_public_request.server.Server.identity_pk,
    beaconcrypt_public_request.server.Server.identity_key_kid,
    beaconcrypt_public_request.server.Server.mldsa_public_key]
  dsimp only [call, LiftFunction.lift, AdapterPublicWrapperLiftFunction.function,
    AdapterPublicWrapperLiftFunction.result, AdapterRecordRequestMonad.liftRust,
    CoreModels.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]
  simp only [RustT.run_bind, pure_bind, edLeaf, mlLeaf]
  exact fingerprint_program _ _ hash hashLeaf

end BeaconcryptCore.Refinement.AdapterPublicWrapperPin

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPin.fingerprint_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPin.fingerprint_program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPin.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPin.server_program
