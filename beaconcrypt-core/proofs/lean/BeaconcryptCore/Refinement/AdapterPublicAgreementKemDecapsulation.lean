-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFields
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Per-primitive ML-KEM ciphertext parsing, decapsulation and shared-secret byte-view contracts. Every fixed-width ciphertext is preserved exactly; functional decapsulation remains optional and retains its arbitrary monadic effects. Private SDK keys are mapped only by their actual private MaterialView, never by public-key equality. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementKemDecapsulation
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 CipherArray)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

structure Views where
  ciphertext : material.KemCiphertext → CipherArray
  shared : material.KemSharedSecret → Array32

structure Ciphertext (view : Views) where
  parse : CipherArray → material.KemCiphertext
  operation : ∀ input, crypto.kemCipherFromBytes input.to_slice = pure (.Ok (parse input))
  exactBytes : ∀ input, view.ciphertext (parse input) = input

structure Shared (view : Views) where
  realize : Array32 → material.KemSharedSecret
  exactBytes : ∀ bytes, view.shared (realize bytes) = bytes
  getter : ∀ shared, crypto.kemSharedBytes shared = pure (view.shared shared)

def reply (realize : Array32 → material.KemSharedSecret) (failure : primitive.Error)
    (result : core.option.Option Array32) : core.result.Result material.KemSharedSecret primitive.Error :=
  match result with
  | .None => .Err failure
  | .Some bytes => .Ok (realize bytes)

structure Contract (keys : AdapterPublicWrapperState.MaterialView source KemSK) (view : Views)
    (shared : Shared (m := m) view) (decapsulate : CipherArray → KemSK → m (core.option.Option Array32)) where
  failure : material.KemCiphertext → material.KemSecretKey → primitive.Error
  operation : ∀ ciphertext secret, crypto.decapsulate ciphertext secret = RustT.lift
    ((reply shared.realize (failure ciphertext secret)) <$>
      decapsulate (view.ciphertext ciphertext) (keys.kemSecret secret))

theorem decoded (keys : AdapterPublicWrapperState.MaterialView source KemSK) (view : Views)
    (parse : Ciphertext (m := m) view) (shared : Shared (m := m) view)
    (decapsulate : CipherArray → KemSK → m (core.option.Option Array32))
    (contract : Contract (m := m) keys view shared decapsulate)
    (input : CipherArray) (secret : material.KemSecretKey) :
    AdapterPublicAgreementFields.decapsulate (m := m) (.Some input) (.Some secret) =
      RustT.lift (decapsulate input (keys.kemSecret secret)) := by
  unfold AdapterPublicAgreementFields.decapsulate
  dsimp only
  rw [parse.operation, pure_bind]
  dsimp only
  rw [contract.operation, parse.exactBytes]
  apply RustT.ext
  simp only [RustT.run_bind, RustT.run_lift, bind_map_left]
  rw [← bind_pure_comp]
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some bytes =>
    simp only [reply, shared.getter, shared.exactBytes, pure_bind, RustT.run_pure]
end BeaconcryptCore.Refinement.AdapterPublicAgreementKemDecapsulation

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementKemDecapsulation.decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementKemDecapsulation.decoded
