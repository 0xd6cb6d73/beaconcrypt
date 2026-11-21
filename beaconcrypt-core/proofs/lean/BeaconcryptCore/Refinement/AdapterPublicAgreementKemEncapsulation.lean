-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFields
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Per-primitive ML-KEM key parsing, encapsulation sampling and output byte views. Invalid keys retain exact rejection before encapsulation. Selected successful primitive sampling retains the actual returned RNG and opaque ciphertext/shared objects; it explicitly excludes RNG/backend error only for that selected primitive model. General source Err behavior is separate. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 CipherArray KemArray)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

structure Views where
  ciphertext : material.KemCiphertext → CipherArray
  shared : material.KemSharedSecret → Array32

structure Getters (view : Views) where
  ciphertext : ∀ value, crypto.kemCipherBytes value = pure (view.ciphertext value)
  shared : ∀ value, crypto.kemSharedBytes value = pure (view.shared value)

structure PublicKey (keys : AdapterPublicWrapperState.MaterialView source KemSK) (valid : KemArray → Bool) where
  parse : KemArray → core.result.Result material.KemPublicKey primitive.Error
  operation : ∀ input, crypto.kemPublicFromBytes input.to_slice = pure (parse input)
  exactBytes : ∀ input key, parse input = .Ok key → keys.kemPublic key = RegistrationRootInput.pqKey input
  admission : ∀ input, valid input = true ↔ ∃ key, parse input = .Ok key

structure Contract {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicWrapperState.MaterialView source KemSK) (view : Views)
    (encapsulate : PqxdhKemIndCca.MlKem768PublicKey → m (CipherArray × Array32)) where
  realize : material.KemPublicKey → (CipherArray × Array32) → R → material.KemCiphertext × material.KemSharedSecret × R
  ciphertextView : ∀ key bytes rng, view.ciphertext (realize key bytes rng).1 = bytes.1
  sharedView : ∀ key bytes rng, view.shared (realize key bytes rng).2.1 = bytes.2
  operation : ∀ key rng, crypto.encapsulate generator key rng = RustT.lift
    ((fun bytes => (.Ok ((realize key bytes rng).1, (realize key bytes rng).2.1), (realize key bytes rng).2.2)) <$>
      encapsulate (keys.kemPublic key))

theorem rejected {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicWrapperState.MaterialView source KemSK) (valid : KemArray → Bool)
    (parse : PublicKey (m := m) keys valid) (input : KemArray) (error : primitive.Error)
    (rejected : parse.parse input = .Err error) (rng : R) :
    AdapterPublicAgreementFields.encapsulate (m := m) generator (.Some input) rng = pure (.None, rng) := by
  unfold AdapterPublicAgreementFields.encapsulate
  dsimp only
  rw [parse.operation, pure_bind, rejected]

theorem invalid {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicWrapperState.MaterialView source KemSK) (valid : KemArray → Bool)
    (parse : PublicKey (m := m) keys valid) (input : KemArray) (rng : R)
    (invalid : valid input = false) :
    AdapterPublicAgreementFields.encapsulate (m := m) generator (.Some input) rng = pure (.None, rng) := by
  cases parsed : parse.parse input with
  | Err error => exact rejected generator keys valid parse input error parsed rng
  | Ok key =>
    have accepted := (parse.admission input).mpr ⟨key, parsed⟩
    rw [invalid] at accepted
    cases accepted

noncomputable section

theorem admitted {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (keys : AdapterPublicWrapperState.MaterialView source KemSK) (valid : KemArray → Bool)
    (parse : PublicKey (m := m) keys valid) (view : Views) (getters : Getters (m := m) view)
    (encapsulate : PqxdhKemIndCca.MlKem768PublicKey → m (CipherArray × Array32))
    (contract : Contract (m := m) generator keys view encapsulate)
    (input : KemArray) (key : material.KemPublicKey) (parsed : parse.parse input = .Ok key) (rng : R) :
    AdapterPublicAgreementFields.encapsulate (m := m) generator (.Some input) rng =
      RustT.lift ((fun bytes => (.Some bytes, (contract.realize key bytes rng).2.2)) <$>
        encapsulate (RegistrationRootInput.pqKey input)) := by
  unfold AdapterPublicAgreementFields.encapsulate
  dsimp only
  rw [parse.operation, pure_bind, parsed]
  dsimp only
  rw [contract.operation, parse.exactBytes input key parsed]
  apply RustT.ext
  simp only [RustT.run_bind, RustT.run_lift, bind_map_left,
    getters.ciphertext, getters.shared, contract.ciphertextView, contract.sharedView,
    map_pure, RustT.run_pure, bind_pure_comp, Functor.map_map]
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation.rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation.rejected

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation.invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation.invalid

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementKemEncapsulation.admitted
