-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
/-! The current public pin helper retains the complete supplied Server binding and ML public key. Pin construction is pure; Server getters retain their reached primitive results and shared state. -/
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
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]

omit material platform primitive localOps crypto in
theorem pin_program (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    (beaconcrypt_public_request.auth.server_pin (m := RustT m) binding publicKey).run =
      pure (.ok (.Some (⟨binding, publicKey⟩ : session.ServerAuthenticationPin))) := by
  simp only [beaconcrypt_public_request.auth.server_pin,call,LiftFunction.lift,
    AdapterRecordRequestMonad.liftRust,registration.begin_server_pin,session.ServerAuthenticationPin.new,
    RustT.run_bind,RustT.run_pure,pure_bind]


theorem server_program (self : beaconcrypt_public_wrapper.server.Server)
    (publicBytes : Std.Array U8 32#usize) (publicKey : Std.Array U8 1952#usize)
    (edLeaf : (crypto.edPublicBytes (platform.arcView self.identity).identity_key.public_key).run = pure (.ok publicBytes))
    (mlLeaf : (localOps.auth_MldsaIdentity_public_key (platform.arcView self.identity).mldsa_identity).run = pure (.ok publicKey)) :
    (beaconcrypt_public_request.server.Server.authentication_pin (m := RustT m) self).run =
      pure (.ok (.Some (⟨⟨publicBytes, (platform.arcView self.identity).identity_key_kid⟩, publicKey⟩ : session.ServerAuthenticationPin))) := by
  unfold beaconcrypt_public_request.server.Server.authentication_pin
  simp only [beaconcrypt_public_request.server.Server.identity_pk,
    beaconcrypt_public_request.server.Server.identity_key_kid,
    beaconcrypt_public_request.server.Server.mldsa_public_key]
  dsimp only [call, LiftFunction.lift, AdapterPublicWrapperLiftFunction.function,
    AdapterPublicWrapperLiftFunction.result, AdapterRecordRequestMonad.liftRust,
    CoreModels.alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]
  simp only [RustT.run_bind, pure_bind, edLeaf, mlLeaf]
  exact pin_program _ _

end BeaconcryptCore.Refinement.AdapterPublicWrapperPin

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPin.pin_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPin.pin_program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperPin.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperPin.server_program
