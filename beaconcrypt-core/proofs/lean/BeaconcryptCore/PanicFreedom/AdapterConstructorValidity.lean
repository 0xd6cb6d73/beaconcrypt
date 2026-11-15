-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterConstructors
import BeaconcryptCore.PanicFreedom.AdapterPublicOrdinary

/-! Successful fallible constructors initialize the safety invariant used by every subsequent public messaging call. Ordinary key-generation errors remain normal results. Standard map initialization is a distinct structural platform contract. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace BeaconcryptCore.PanicFreedom.AdapterConstructorValidity
open Refinement AdapterNormal AdapterConstructors beaconcrypt_public_wrapper
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : PublicWrapperPlatform.CryptoOperations]
variable [generators : AdapterBeaconConstructorPrimitive.Operations]
variable [standard : AdapterBeaconConstructorPrimitive.Standard]
variable [authentication : beaconcrypt.auth.Operations]

omit platform standard authentication in
theorem beacon_try_new_with_rng_valid
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (contracts : BeaconContracts generator) (identifier : U64)
    (identityKey mldsaKey : Slice U8) (rng : R) :
    Ensures (beaconcrypt_constructor.beacon.Beacon.try_new_with_rng generator identifier identityKey mldsaKey rng)
      (fun result => match result.1 with | .Ok self => AdapterPublicOrdinary.ValidBeacon self | .Err _ => True) := by
  unfold beaconcrypt_constructor.beacon.Beacon.try_new_with_rng
  simp only [beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from,
    core.option.Option.ok_or,
    pqxdh.BeaconFresh.new,
    bind_tc_ok]
  repeat'
    try dsimp! only
    try simp only [bind_tc_ok]
    first
      | with_reducible apply ensures_bind_at
      | (solve | simp_all)
      | (apply ensures_ok; trivial)
      | exact contracts.parse _
      | exact contracts.edPublicBytes _
      | exact contracts.edGenerate _
      | exact contracts.kxGenerate _
      | exact contracts.kemGenerate _
      | exact server_pin_total _ _
      | exact RegistrationInputs.copied_slice_total _ _
      | (rintro ⟨left, right⟩)
      | (intro value)
      | (split)
      | (split at *)

variable [serverStandard : AdapterServerConstructorPrimitive.Standard]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
variable [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]

structure InitializationContracts : Prop where
  mapValid : ∀ seed map, serverStandard.mapWithKey U64 AdapterPublicOrdinary.Remote seed = ok map →
    AdapterPublicOrdinary.ValidMap map

omit crypto standard authentication in
theorem server_try_new_with_rng_valid
    {R E : Type} (generator : rand_core.TryCryptoRng R E) (contracts : ServerContracts generator)
    (initialization : InitializationContracts) (identifier : U64)
    (identitySeed mldsaSeed : core.option.Option (Slice U8)) (rng : R) :
    Ensures (beaconcrypt_server_constructor.server.Server.try_new_with_rng generator identifier identitySeed mldsaSeed rng)
      (fun result => match result.1 with | .Ok self => AdapterPublicOrdinary.ValidServer self | .Err _ => True) := by
  unfold beaconcrypt_server_constructor.server.Server.try_new_with_rng
  simp only [beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once,
    core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
    core.convert.From.Blanket.from,
    pqxdh.ServerState.new,
    bind_tc_ok]
  repeat'
    try dsimp! only
    try simp only [bind_tc_ok]
    first
      | with_reducible apply ensures_bind_at
      | with_reducible apply normal_bind_at
      | (solve | simp_all)
      | (apply ensures_ok; apply initialization.mapValid; assumption)
      | exact normal_ok _
      | exact contracts.edGenerate _
      | exact contracts.mldsaGenerate _
      | exact contracts.edFromSeed _
      | exact contracts.mldsaFromSeed _
      | exact contracts.edSecretBytes _
      | exact contracts.mapWithKey _ _ _
      | exact contracts.setWithKey _ _
      | exact contracts.arcNew _
      | exact RegistrationInputs.copied_slice_total _ _
      | (rintro ⟨left, right⟩)
      | (intro value)
      | (split)
      | (split at *)

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
    [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] platform serverStandard authentication in
theorem beacon_try_new_valid (contracts : BeaconContracts standard.os) (identifier : U64)
    (identityKey mldsaKey : Slice U8) :
    Ensures (beaconcrypt_constructor.beacon.Beacon.try_new identifier identityKey mldsaKey)
      (fun result => match result with | .Ok self => AdapterPublicOrdinary.ValidBeacon self | .Err _ => True) := by
  obtain ⟨⟨result, rng⟩, returned, valid⟩ := beacon_try_new_with_rng_valid standard.os contracts identifier identityKey mldsaKey ()
  refine ⟨result, ?_, valid⟩
  simp only [beaconcrypt_constructor.beacon.Beacon.try_new,
    beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError, returned, bind_tc_ok]
  rfl

omit crypto authentication in
theorem server_try_new_valid (contracts : ServerContracts standard.os) (initialization : InitializationContracts)
    (identifier : U64) (identitySeed mldsaSeed : core.option.Option (Slice U8)) :
    Ensures (beaconcrypt_server_constructor.server.Server.try_new identifier identitySeed mldsaSeed)
      (fun result => match result with | .Ok self => AdapterPublicOrdinary.ValidServer self | .Err _ => True) := by
  obtain ⟨⟨result, rng⟩, returned, valid⟩ := server_try_new_with_rng_valid standard.os contracts initialization identifier identitySeed mldsaSeed ()
  refine ⟨result, ?_, valid⟩
  simp only [beaconcrypt_server_constructor.server.Server.try_new,
    beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError, returned, bind_tc_ok]
  rfl

end BeaconcryptCore.PanicFreedom.AdapterConstructorValidity
