-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicServerEntryRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The original public Server delegator is separately extracted without source or LLBC normalization. Its foreign signatures are exact aliases to both maintained actual source children. The typed request lift specializes back to that RustM body and factors the complete public call through those children for arbitrary shared effects, retaining early rejection, returned Self and RNG. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerEntry
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
variable [PublicWrapperPlatform.CryptoOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.Codecs] [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]
variable [beaconcrypt.ratchet.Operations] [beaconcrypt.auth.Operations]

theorem rust_source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m := RustM) generator self input rng =
      beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng generator self input rng := by
  simp only [beaconcrypt_public_request.server.Server.get_shared_secret_with_rng,
    beaconcrypt_public_server_entry.server.Server.get_shared_secret_with_rng,
    beaconcrypt_public_server_entry.server.Server.authenticate_registration_lookup,
    beaconcrypt_public_server_entry.server.Server.get_shared_secret_from_lookup_with_rng,
    AdapterPublicWrapperSpecialization.authenticate_lookup_source,
    AdapterPublicWrapperSpecialization.accept_registration_source]
  rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [containers : ContainerOperations (RustT m)] [codec : Codecs (RustT m)]
variable [children : ChildOperations (RustT m)]

noncomputable def sequence {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    RustT m (core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R) := do
  let lookup ← AdapterPublicServerAcceptBody.authenticate self input
  match lookup with
  | .None => pure (.None, self, rng)
  | .Some lookup => AdapterPublicServerAcceptBody.acceptLookup generator self lookup rng

omit material platform ed [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.CryptoOperations] [PublicWrapperPlatform.ContainerOperations] [PublicWrapperPlatform.Codecs]
  [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] [beaconcrypt.ratchet.Operations]
  [beaconcrypt.auth.Operations] localOps crypto containers codec children [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl

omit [PublicWrapperPlatform.CryptoOperations] [PublicWrapperPlatform.Codecs] [RegistrationWriterPrimitive.Operations]
  [AdapterWirePrimitive.Operations] [beaconcrypt.ratchet.Operations] [beaconcrypt.auth.Operations] in
theorem source {R E : Type} (generator : rand_core.TryCryptoRng R E)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    beaconcrypt_public_request.server.Server.get_shared_secret_with_rng (m := RustT m) generator self input rng =
      sequence generator self input rng := by
  unfold beaconcrypt_public_request.server.Server.get_shared_secret_with_rng sequence
  rw [AdapterPublicServerAcceptBody.authenticate_source]
  apply bind_congr
  intro lookup
  cases lookup with
  | none => simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | some lookup =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind]
    exact AdapterPublicServerAcceptBody.accept_lookup_source generator self lookup rng
end BeaconcryptCore.Refinement.AdapterPublicServerEntry

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerEntry.rust_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerEntry.rust_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerEntry.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerEntry.source
