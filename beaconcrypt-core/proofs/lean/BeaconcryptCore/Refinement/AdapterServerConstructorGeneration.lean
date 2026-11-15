-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! The Server constructor retains its mandatory ML generation primitive contract, including optional failure, joint caller RNG and private credential view. The Beacon constructor has no ML generation operation. This contract concerns only an individual original foreign primitive; no controller or source correspondence is assumed. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK R Error : Type}

structure MldsaContract (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (sample : m (Option (RegistrationNativeMldsa.Credential source))) where
  joint : R → m (Option (RegistrationNativeMldsa.Credential source) × R)
  nativeMarginal : ∀ rng, Prod.fst <$> joint rng = sample
  realize : RegistrationNativeMldsa.Credential source → beaconcrypt_public_wrapper.auth.MldsaIdentity
  privateView : ∀ credential, view.mldsa (realize credential) = credential
  operation : ∀ rng, generators.mldsaGenerate generator rng = RustT.lift
    ((fun reply => (match reply.1 with | none => .Err () | some credential => .Ok (realize credential), reply.2)) <$> joint rng)

end BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
