-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterServerConstructorRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization
variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [AdapterInitEdPrimitive.Operations] [AdapterBeaconConstructorPrimitive.Operations]
variable [AdapterBeaconConstructorPrimitive.Standard] [AdapterServerConstructorPrimitive.Standard]

omit [AdapterBeaconConstructorPrimitive.Standard] in
theorem caller_rng {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) (rng : R) :
    beaconcrypt_server_constructor_request.server.Server.try_new_with_rng (m := RustM) generator identifier identitySeed mldsaSeed rng =
      beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed rng := by
  unfold beaconcrypt_server_constructor_request.server.Server.try_new_with_rng beaconcrypt_server_constructor.server.Server.try_new_with_rng
  dsimp only [AdapterPublicWrapperLiftFunction.call,AdapterPublicWrapperLiftFunction.function,
    AdapterPublicWrapperLiftFunction.result,AdapterRecordRequestMonad.instLiftRustRustM,
    AdapterBeaconConstructorRequestMonad.rustOperations,
    beaconcrypt_crypto.crypto_sign.KeyPair.generate_with_rng,
    beaconcrypt_server_constructor.auth.MldsaIdentity.generate_with_rng]
  cases identitySeed <;> cases mldsaSeed <;> simp only [bind_assoc,pure_bind] <;> rfl

theorem operating_system (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) :
    beaconcrypt_server_constructor_request.server.Server.try_new (m := RustM) identifier identitySeed mldsaSeed =
      beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed := by
  unfold beaconcrypt_server_constructor_request.server.Server.try_new beaconcrypt_server_constructor.server.Server.try_new
  rw [caller_rng]
  rfl

theorem panicking_entry (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) :
    beaconcrypt_server_constructor_request.server.Server.new (m := RustM) identifier identitySeed mldsaSeed =
      beaconcrypt_server_constructor.server.Server.new identifier identitySeed mldsaSeed := by
  unfold beaconcrypt_server_constructor_request.server.Server.new beaconcrypt_server_constructor.server.Server.new
  rw [operating_system]
  rfl
end BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization.caller_rng' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization.caller_rng

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization.operating_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization.operating_system

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization.panicking_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorSpecialization.panicking_entry
