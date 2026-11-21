-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! A selected primitive sampling/representation contract for actual X25519 key generation. It exposes the updated caller RNG and actual private object views. In this selected contract the supplied scalar sampler has no backend/RNG error; the general source factoring separately retains every Err and returned RNG. This is a primitive functional model boundary, not a protocol or whole executor premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 KeyPair)
open BeaconcryptCore.Computational
open PqxdhJointGapDh (ScalarBytes)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

structure Contract {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (publicKey : ScalarBytes → Array32) (sample : m ScalarBytes) where
  realize : ScalarBytes → R → KeyPair × R
  privateView : ∀ scalar rng, view.kxSecret (realize scalar rng).1.secret_key = scalar
  publicView : ∀ scalar rng, view.kxPublic (realize scalar rng).1.public_key = publicKey scalar
  operation : ∀ rng, crypto.kxGenerate generator rng = RustT.lift
    ((fun scalar => (.Ok (realize scalar rng).1, (realize scalar rng).2)) <$> sample)

noncomputable section

theorem fields {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (publicKey : ScalarBytes → Array32)
    (sample : m ScalarBytes) (contract : Contract generator view publicKey sample)
    (publicGetter : ∀ key, crypto.kxPublicBytes key = pure (view.kxPublic key)) (rng : R) :
    AdapterPublicAgreementFields.generate (m := m) generator rng =
      RustT.lift ((fun scalar => (.Some (publicKey scalar), .Some (contract.realize scalar rng).1,
        (contract.realize scalar rng).2)) <$> sample) := by
  rw [AdapterPublicAgreementPrimitiveFields.generation, contract.operation]
  apply RustT.ext
  simp only [RustT.run_bind, RustT.run_lift, bind_map_left, map_pure, RustT.run_pure, publicGetter,
    contract.publicView, bind_pure_comp, Functor.map_map]

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration.fields
