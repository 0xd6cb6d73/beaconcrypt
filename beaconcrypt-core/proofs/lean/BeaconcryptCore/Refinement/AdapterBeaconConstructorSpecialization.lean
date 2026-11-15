-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterBeaconConstructorRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperSpecialization
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization
variable [PublicWrapperPlatform.Material] [PublicWrapperPlatform.Platform]
variable [AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterBeaconConstructorPrimitive.Operations]
variable [AdapterBeaconConstructorPrimitive.Standard]
variable [beaconcrypt.auth.Operations] [beaconcrypt.ratchet.Operations]
variable [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]

omit [PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator] [AdapterBeaconConstructorPrimitive.Standard]
    [beaconcrypt.auth.Operations] [beaconcrypt.ratchet.Operations]
    [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] in
theorem caller_rng {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (rng : R) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m := RustM) generator identifier identityKey mldsaKey rng =
      beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey rng := by
  rfl

omit [PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator]
    [beaconcrypt.auth.Operations] [beaconcrypt.ratchet.Operations]
    [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] in
theorem operating_system (identifier : U64) (identityKey mldsaKey : Slice U8) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new (m := RustM) identifier identityKey mldsaKey =
      beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey := by
  rfl

omit [PublicWrapperPlatform.Platform] [PublicWrapperPlatform.Allocator]
    [beaconcrypt.auth.Operations] [beaconcrypt.ratchet.Operations]
    [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] in
theorem panicking_entry (identifier : U64) (identityKey mldsaKey : Slice U8) :
    beaconcrypt_constructor_request.beacon.Beacon.new (m := RustM) identifier identityKey mldsaKey =
      beaconcrypt_constructor.beacon.Beacon.new identifier identityKey mldsaKey := by
  rfl

end BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization.caller_rng' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization.caller_rng

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization.operating_system' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization.operating_system

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization.panicking_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorSpecialization.panicking_entry
