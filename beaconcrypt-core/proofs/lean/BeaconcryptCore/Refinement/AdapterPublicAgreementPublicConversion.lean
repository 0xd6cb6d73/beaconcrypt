-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFields
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Ordinary per-primitive Ed25519 parsing and conversion representation contracts. Invalid parse replies remain invalid source conversion replies. Successful parsing preserves the exact supplied public bytes. No agreement, authentication or protocol conclusion is a field. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementPublicConversion
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicAgreementFields (Array32)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

structure Contract (functional : Pqxdh.Crypto) (view : AdapterPublicWrapperState.MaterialView source KemSK) where
  parse : Array32 → core.result.Result primitive.PublicKey primitive.Error
  conversion : primitive.PublicKey → core.result.Result Array32 primitive.Error
  parseNormal : ∀ input, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes input.to_slice = .ok (parse input)
  parseView : ∀ input key, parse input = .Ok key → view.edPublic key = input
  parseRejected : ∀ input error, parse input = .Err error → RegistrationPublicConversion.convert functional input = .None
  operation : ∀ key, crypto.convertPublic key = pure (conversion key)
  value : ∀ key, core.result.Result.ok (conversion key) =
    .ok (RegistrationPublicConversion.convert functional (view.edPublic key))

omit material primitive crypto [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

theorem converted_public (functional : Pqxdh.Crypto) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (contract : Contract (m := m) functional view) (input : Array32) :
    AdapterPublicAgreementFields.convertPublic (m := m) input =
      pure (RegistrationPublicConversion.convert functional input) := by
  rw [AdapterPublicAgreementFields.convertPublic, contract.parseNormal, lift_ok, pure_bind]
  cases parsed : contract.parse input with
  | Err error =>
    rw [contract.parseRejected input error parsed]
  | Ok key =>
    change (do let result ← crypto.convertPublic key
               liftRust (core.result.Result.ok result)) = _
    rw [contract.operation, pure_bind, contract.value, lift_ok, contract.parseView input key parsed]
end BeaconcryptCore.Refinement.AdapterPublicAgreementPublicConversion

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPublicConversion.converted_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPublicConversion.converted_public
