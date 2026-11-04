-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterConstructors
import BeaconcryptCore.PanicFreedom.AdapterPublicRegistrationLoops

/-! Regression witnesses for the quantifier boundary of execution contracts. This pure model calls its supplied RNG and returns an ordinary error after that call. The selected RNG returns an ordinary error, while a different RNG diverges. The selected contracts remain inhabited. These witnesses establish contract satisfiability, not correspondence with native primitive implementations or cryptographic security. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterSelectedRngContracts
open Refinement AdapterNormal AdapterPublicRegistrationLoops
variable [material : PublicWrapperPlatform.Material]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]

def errorRng : rand_core.TryCryptoRng Unit primitive.Error where
  TryRngInst := {
    coreerrorErrorInst := crypto.errorInstance
    try_fill_bytes := fun before bytes => ok (.Err crypto.errorToken, before, bytes)
    try_next_u32 := fun before => ok (.Err crypto.errorToken, before)
    try_next_u64 := fun before => ok (.Err crypto.errorToken, before)
  }

def divergentRng : rand_core.TryCryptoRng Unit primitive.Error where
  TryRngInst := {
    coreerrorErrorInst := crypto.errorInstance
    try_fill_bytes := fun _ _ => div
    try_next_u32 := fun _ => div
    try_next_u64 := fun _ => div
  }

private def afterFill {A F R E : Type} (generator : rand_core.TryCryptoRng R E)
    (before : R) (error : F) : RustM (core.result.Result A F × R) := do
  let (_, after, _) ← generator.TryRngInst.try_fill_bytes before ⟨[], by simp⟩
  ok (.Err error, after)

@[instance_reducible] def cryptoModel : PublicWrapperPlatform.CryptoOperations := {
  crypto with
  kxGenerate := fun generator before => afterFill generator before crypto.errorToken
  encapsulate := fun generator _ before => afterFill generator before crypto.errorToken
}

@[instance_reducible] def constructorModel : AdapterBeaconConstructorPrimitive.Operations where
  mldsaGenerate := fun generator before => afterFill generator before ()
  edGenerate := fun generator before => afterFill generator before crypto.errorToken
  kemGenerate := fun generator before => afterFill generator before crypto.errorToken

theorem selected_agreement_contracts :
    AgreementRngContracts (crypto := cryptoModel) errorRng := by
  let : PublicWrapperPlatform.CryptoOperations := cryptoModel
  exact {
    kxGenerate := fun _ => ⟨_, rfl⟩
    encapsulate := fun _ _ => ⟨_, rfl⟩
  }

theorem selected_generation_returns_error (before : Unit) :
    cryptoModel.kxGenerate errorRng before = ok (.Err crypto.errorToken, before) := rfl

theorem selected_encapsulation_returns_error
    (key : beaconcrypt_crypto.crypto_kem.mlkem768.PublicKey) (before : Unit) :
    cryptoModel.encapsulate errorRng key before = ok (.Err crypto.errorToken, before) := rfl

theorem other_generation_diverges (before : Unit) :
    cryptoModel.kxGenerate divergentRng before = div := rfl

theorem selected_contracts_with_divergent_other (before : Unit) :
    AgreementRngContracts (crypto := cryptoModel) errorRng ∧
      ¬ Normal (cryptoModel.kxGenerate divergentRng before) := by
  refine ⟨selected_agreement_contracts, ?_⟩
  rintro ⟨value, returned⟩
  cases returned

variable [authentication : beaconcrypt.auth.Operations]

theorem selected_beacon_contracts
    (parse : ∀ input, Normal (primitive.parse input))
    (edPublicBytes : ∀ key, Normal (crypto.edPublicBytes key))
    (hash : ∀ request, Normal (authentication.hash request)) :
    AdapterConstructors.BeaconContracts (crypto := cryptoModel)
      (generators := constructorModel) errorRng := by
  let : PublicWrapperPlatform.CryptoOperations := cryptoModel
  let : AdapterBeaconConstructorPrimitive.Operations := constructorModel (crypto := crypto)
  exact {
    parse := parse
    edPublicBytes := edPublicBytes
    hash := hash
    mldsaGenerate := fun _ => ⟨_, rfl⟩
    edGenerate := fun _ => ⟨_, rfl⟩
    kxGenerate := fun _ => ⟨_, rfl⟩
    kemGenerate := fun _ => ⟨_, rfl⟩
  }

end BeaconcryptCore.PanicFreedom.AdapterSelectedRngContracts
